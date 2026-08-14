/*
 * FLARE v1 decode engine (JavaScript port).
 *
 * This mirrors protocol.py / signal_proc.py / decoder.py from the Python
 * project, but solves a harder problem: the Python/Arduino receivers all
 * had an explicit "start" signal (RX_START) giving them a shared time
 * reference with the sender. A phone camera watching a screen has no such
 * signal -- the sender started flashing at some arbitrary moment relative
 * to when the camera started capturing. So this version adds a PHASE
 * SEARCH: it tries several candidate time-alignments and uses the
 * PREAMBLE+SFD pattern (which is what it's there for) to figure out which
 * alignment is actually correct.
 *
 * Usable both in a browser (attaches to `window.Flare`) and in Node
 * (exports via module.exports) so the decode logic itself can be unit
 * tested without a real camera.
 */

(function (root) {
  const PREAMBLE = "10101010";
  const SFD = "11101001";
  const EOF_MARKER = "01011010";
  const SYNC = PREAMBLE + SFD; // 16 bits

  function crc8(bytes) {
    let crc = 0;
    for (let i = 0; i < bytes.length; i++) {
      crc ^= bytes[i];
      for (let b = 0; b < 8; b++) {
        if (crc & 0x80) {
          crc = ((crc << 1) ^ 0x07) & 0xff;
        } else {
          crc = (crc << 1) & 0xff;
        }
      }
    }
    return crc;
  }

  function bitsToByte(bits) {
    return parseInt(bits, 2);
  }

  /**
   * Majority vote over samples within [tCenter-halfWindow, tCenter+halfWindow].
   * Returns true/false, or null if there isn't enough data yet (the window
   * extends past the newest sample -- i.e. "not received yet", not "off").
   */
  function windowVote(samples, tCenter, halfWindow, latestT) {
    if (tCenter + halfWindow > latestT) {
      return null; // haven't captured this far yet
    }
    let onCount = 0;
    let total = 0;
    for (let i = 0; i < samples.length; i++) {
      const s = samples[i];
      if (s.t >= tCenter - halfWindow && s.t <= tCenter + halfWindow) {
        total++;
        if (s.on) onCount++;
      }
    }
    if (total === 0) return null;
    return onCount * 2 >= total;
  }

  /**
   * Recover up to numBits bits starting at absolute time t0, at the given
   * slotMs. Returns { bits, complete } -- bits uses 'X' for an ambiguous
   * slot and stops early (complete=false) if the buffer doesn't yet cover
   * the requested range.
   */
  function recoverBitsFrom(samples, t0, slotMs, numBits) {
    if (samples.length === 0) return { bits: "", complete: false };
    const latestT = samples[samples.length - 1].t;
    const halfWindow = slotMs * 0.22; // widened from 0.15 -- real camera
    // capture has more jitter/noise than the synthetic tests this was
    // originally tuned against, so a slightly wider vote window trades a
    // little precision for a lot more real-world noise tolerance.
    let bits = "";
    for (let i = 0; i < numBits; i++) {
      const tQ1 = t0 + i * slotMs + slotMs * 0.25;
      const tQ3 = t0 + i * slotMs + slotMs * 0.75;
      const first = windowVote(samples, tQ1, halfWindow, latestT);
      const second = windowVote(samples, tQ3, halfWindow, latestT);
      if (first === null || second === null) {
        return { bits, complete: false };
      }
      if (!first && second) bits += "1";
      else if (first && !second) bits += "0";
      else bits += "X";
    }
    return { bits, complete: true };
  }

  /**
   * Parses a bitstring already ALIGNED so index 0 = start of PREAMBLE
   * (i.e. bits.slice(0, 16) === SYNC). Mirrors decoder.py's field parsing.
   */
  function parseAlignedPacket(bits) {
    const result = {
      sfdFound: true,
      crcValid: false,
      eofValid: false,
      text: null,
      error: null,
    };

    let cursor = SYNC.length;
    const lengthBits = bits.slice(cursor, cursor + 8);
    if (lengthBits.length < 8 || lengthBits.includes("X")) {
      result.error = "LENGTH field not yet fully received";
      return result;
    }
    const length = bitsToByte(lengthBits);
    cursor += 8;

    const dataBits = bits.slice(cursor, cursor + 8 * length);
    if (dataBits.length < 8 * length) {
      result.error = "DATA field not yet fully received";
      return result;
    }
    if (dataBits.includes("X")) {
      result.error = "DATA field corrupted";
      return result;
    }
    const dataBytes = [];
    for (let i = 0; i < dataBits.length; i += 8) {
      dataBytes.push(bitsToByte(dataBits.slice(i, i + 8)));
    }
    cursor += 8 * length;

    const checksumBits = bits.slice(cursor, cursor + 8);
    if (checksumBits.length < 8 || checksumBits.includes("X")) {
      result.error = "CHECKSUM field not yet fully received";
      return result;
    }
    const receivedChecksum = bitsToByte(checksumBits);
    cursor += 8;

    const eofBits = bits.slice(cursor, cursor + 8);
    result.eofValid = eofBits === EOF_MARKER;

    const expectedChecksum = crc8([length, ...dataBytes]);
    result.crcValid = expectedChecksum === receivedChecksum;
    result.length = length;

    if (result.crcValid) {
      result.text = dataBytes.map((b) => String.fromCharCode(b)).join("");
    } else {
      result.error = "CRC mismatch -- message corrupted";
    }
    return result;
  }

  /**
   * FlareReceiver: stateful engine an app can feed samples into.
   * ingestSample(t, on) as data arrives; call attemptDecode() periodically.
   */
  class FlareReceiver {
    constructor(slotMs, options = {}) {
      this.slotMs = slotMs;
      this.samples = [];
      this.maxBufferMs = options.maxBufferMs || 120000; // 2 minutes -- covers
      // reasonably long messages even at slow flash speeds. A message
      // longer than this at a given slot speed would need a larger buffer
      // (exposed via the options.maxBufferMs constructor param).
      this.phaseSteps = options.phaseSteps || 10;
      this.lastResult = null;
    }

    ingestSample(t, on) {
      this.samples.push({ t, on });
      const cutoff = t - this.maxBufferMs;
      while (this.samples.length > 0 && this.samples[0].t < cutoff) {
        this.samples.shift();
      }
    }

    /**
     * Detects times where the (already-thresholded) signal changes state.
     * Manchester encoding guarantees a transition at every bit's midpoint,
     * so real transitions are exactly the candidate anchors worth trying --
     * far fewer and far more meaningful than a blind time grid, and this
     * is what actually lets the receiver lock on regardless of when it
     * started listening relative to when the sender started transmitting.
     */
    detectTransitions() {
      const transitions = [];
      for (let i = 1; i < this.samples.length; i++) {
        if (this.samples[i].on !== this.samples[i - 1].on) {
          transitions.push(this.samples[i].t);
        }
      }
      return transitions;
    }

    /**
     * Tries each recent transition as a hypothesis for "this is the
     * mid-point of bit 0" and checks whether that alignment produces a
     * valid PREAMBLE+SFD. Returns a decode result once a full valid (or
     * confidently invalid) packet is found, otherwise null ("still
     * listening").
     */
    attemptDecode() {
      if (this.samples.length === 0) return null;
      const transitions = this.detectTransitions();
      const maxCandidates = this.options_maxCandidates || 40;
      const candidates = transitions.slice(0, maxCandidates);

      for (const tEdge of candidates) {
        const phase = tEdge - this.slotMs / 2;
        const { bits: syncBits, complete } = recoverBitsFrom(
          this.samples, phase, this.slotMs, SYNC.length
        );
        if (!complete) continue;
        if (syncBits !== SYNC) continue;

        // Found alignment. Now pull LENGTH to know the full packet size,
        // then re-pull the whole thing once we know how long it is.
        const lenProbe = recoverBitsFrom(this.samples, phase, this.slotMs, SYNC.length + 8);
        if (!lenProbe.complete) continue;
        const lengthBits = lenProbe.bits.slice(SYNC.length, SYNC.length + 8);
        if (lengthBits.includes("X")) continue;
        const length = bitsToByte(lengthBits);
        const totalBits = SYNC.length + 8 + 8 * length + 8 + 8;

        const full = recoverBitsFrom(this.samples, phase, this.slotMs, totalBits);
        if (!full.complete) continue; // found sync, but message still arriving

        const result = parseAlignedPacket(full.bits);
        result.phase = phase;
        result.rawBits = full.bits;
        this.lastResult = result;
        return result;
      }
      return null;
    }
  }

  const Flare = {
    PREAMBLE,
    SFD,
    EOF_MARKER,
    crc8,
    bitsToByte,
    recoverBitsFrom,
    parseAlignedPacket,
    FlareReceiver,
  };

  if (typeof module !== "undefined" && module.exports) {
    module.exports = Flare;
  } else {
    root.Flare = Flare;
  }
})(typeof window !== "undefined" ? window : globalThis);
