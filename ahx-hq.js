//
/*

  ahx-hq.js - ES6 Module Version
	usually the codeflow is like this:

  import { AHXMaster, AHXSong, setAHXOversampling } from 'ahx-hq';

	const ahxMaster = new AHXMaster(); // create a new AHX Replayer; only create one
	const ahxSong = new AHXSong();
	await ahxSong.LoadSong('song.ahx'); // asynchronously load a AHX song into memory
	ahxMaster.Play(ahxSong); // start playing

  setAHXOversampling(false); // change oversampling anytime while playing or before playing



	---- Changelog ----
	Modified Feb 02 2026 - convert to modern es6 module, add oversampling option (ffx)
	---------------------------
	Modified Aug 30 2020 - Additional check for Tempo (bryc)
	---------------------------
  * This fixes an edge case when F00 is used with voice data.
    Thanks to pachuco for finding it:
    https://github.com/pete-gordon/hivelytracker/issues/40#issuecomment-683404896

    Normally F00 is never used with any voice parameters, but
    a small number of known files are affected by this condition:
    Yelm - Oldskoolcrackintrosong
    Varthall - this creamy nation
    Miao - logo
    Jazz (NL) - jingles (NOTE: occurs beyond end point)
    Jazz (NL) - hawaii-balls (NOTE: occurs beyond end point)
    Mermaid - kingkong (NOTE: occurs beyond end point)
    Syphus - last tense (NOTE: occurs in unused pattern #9)
	---------------------------
	Modified Jun 21 2020 - webkitAudioContext compatibility (bryc)
	---------------------------
  * Use webkitAudioContext when needed - Supports Safari and older browsers
    ---------------------------
	Modified Oct 03 2016 - decodeURI -> decodeURIComponent (bryc)
	---------------------------
  * Reverting but fixing the case for #
    ---------------------------
	Modified Apr 25 2016 - decodeURIComponent -> decodeURI (bryc)
	---------------------------
  * decodeURIComponent will fail to open URLs with certain characters (e.g. #)
    ---------------------------
	Modified Jul 14 2015 - webkitAudioContext -> AudioContext (bryc)
	---------------------------
  * webkitAudioContext is now depreciated, so use AudioContext
  * Main Volume is no longer initialized on every subsong.
	---------------------------
	Modified Aug 07 2014 - A number of quick workarounds (bryc)
	---------------------------
  * Changed createJavaScriptNode() to createScriptProcessor(). Apparently browsers no
	longer recognize the former, causing an error and breaking the entire script.
  * In dataType.readStringAt(), an additional check was added to fix undefined being
	accessed with charCodeAt() in some AHX tunes e.g. Buzzer-Sunstone.ahx.
  * A fair amount of songs were crashing due to undefined array offsets. I wrote a function
	toSixtyTwo() to ensure a range of 0 to 62, and applied it to both instances of
	this.Voices[v].FilterPos-1. This issue seems to occur mostly with files in AHX2 format.
	A good example of this is : AceMan - Jesus Stole My Jelly Beans.ahx
  * Fixed about 10 remaining files by checking out-of-range Instrument numbers, and
    adjusting accordingly. In ProcessStep.
  * introaac.ahx caused a unique error with track positions. I added a workaround in PlayIRQ()
*/
// ahx-player.js - Complete ES6 Module Version

// --- Global Config & Helpers ---

let useOversampling = false;

export function setAHXOversampling(enabled) {
  useOversampling = enabled;
}

const toSixtyTwo = (a) => {
  if (a < 0) return 0;
  if (a > 62) return 62;
  return a;
};

// --- Helper Classes (Data Structures) ---

class AHXStream {
  constructor(uint8Array) {
    this.data = uint8Array;
    this.pos = 0;
  }

  readByte() {
    return this.data[this.pos++] & 0xff;
  }

  readByteAt(p) {
    return this.data[p] & 0xff;
  }

  readShort() {
    const b1 = this.readByte();
    const b2 = this.readByte();
    return (b1 << 8) | b2;
  }

  readStringAt(p) {
    let str = '';
    let i = p;
    while (i < this.data.length && this.data[i] !== 0) {
      str += String.fromCharCode(this.data[i]);
      i++;
    }
    return str;
  }
}

// Struct Factories (kept as helpers for cleaner object creation)
const createEnvelope = () => ({
  aFrames: 0,
  aVolume: 0,
  dFrames: 0,
  dVolume: 0,
  sFrames: 0,
  rFrames: 0,
  rVolume: 0,
});

const createInstrument = () => ({
  Name: '',
  Volume: 0,
  WaveLength: 0,
  Envelope: createEnvelope(),
  FilterLowerLimit: 0,
  FilterUpperLimit: 0,
  FilterSpeed: 0,
  SquareLowerLimit: 0,
  SquareUpperLimit: 0,
  SquareSpeed: 0,
  VibratoDelay: 0,
  VibratoDepth: 0,
  VibratoSpeed: 0,
  HardCutRelease: 0,
  HardCutReleaseFrames: 0,
  PList: { Speed: 0, Length: 0, Entries: [] },
});

// --- Core Classes ---

class AHXWaves {
  constructor() {
    this.FilterSets = new Array(63); // 31 + 1 + 31
    this.init();
  }

  generateTriangle(Len) {
    const Buffer = [];
    const d2 = Len;
    const d5 = d2 >> 2;
    const d1 = 128 / d5;
    const d4 = -(d2 >> 1);
    let eax = 0;
    for (let ecx = 0; ecx < d5; ecx++) {
      Buffer.push(eax);
      eax += d1;
    }
    Buffer.push(0x7f);
    if (d5 !== 1) {
      eax = 128;
      for (let ecx = 0; ecx < d5 - 1; ecx++) {
        eax -= d1;
        Buffer.push(eax);
      }
    }
    let esi = Buffer.length + d4;
    for (let ecx = 0; ecx < d5 * 2; ecx++) {
      let neu = Buffer[esi++];
      if (neu === 0x7f) neu = -0x80;
      else neu = -neu;
      Buffer.push(neu);
    }
    return Buffer;
  }

  generateSquare() {
    const Buffer = [];
    for (let ebx = 1; ebx <= 0x20; ebx++) {
      for (let ecx = 0; ecx < (0x40 - ebx) * 2; ecx++) Buffer.push(-0x80);
      for (let ecx = 0; ecx < ebx * 2; ecx++) Buffer.push(0x7f);
    }
    return Buffer;
  }

  generateSawtooth(Len) {
    const Buffer = [];
    const ebx = Math.floor(256 / (Len - 1));
    let eax = -128;
    for (let ecx = 0; ecx < Len; ecx++) {
      Buffer.push(eax);
      eax += ebx;
    }
    return Buffer;
  }

  generateWhiteNoise(Len) {
    // Original static noise data
    const noise = [
      0x7f, 0x7f, 0xa8, 0xe2, 0x78, 0x3e, 0x2c, 0x92, 0x52, 0xd5, 0x80, 0x80,
      0xab, 0x80, 0x7f, 0x37, 0x7f, 0x7f, 0x15, 0x3b, 0xbc, 0x66, 0xf3, 0x7f,
      0x80, 0x80, 0x80, 0x80, 0x42, 0xe5, 0xf8, 0x80, 0x7f, 0x7f, 0x26, 0x7f,
      0x80, 0x97, 0x80, 0x5f, 0xa7, 0x7f, 0x80, 0x80, 0x80, 0x7f, 0x7f, 0x7f,
      0xce, 0x79, 0x8c, 0x80, 0x4a, 0x7f, 0x80, 0x16, 0x7f, 0x7f, 0x80, 0x80,
      0x09, 0xf1, 0x80, 0x95, 0x78, 0x78, 0x7f, 0xb8, 0xe2, 0x52, 0x7f, 0x08,
      0x93, 0x7f, 0x7f, 0x80, 0xfb, 0xa8, 0x44, 0xe5, 0xca, 0x09, 0x7f, 0x80,
      0x7f, 0x80, 0xcb, 0x80, 0x7f, 0xf7, 0x80, 0x80, 0xb7, 0x7f, 0x5b, 0x80,
      0x3b, 0x14, 0xcf, 0x80, 0x7f, 0x80, 0x16, 0x1f, 0x67, 0xa1, 0x62, 0x71,
      0x71, 0xa7, 0x7f, 0x44, 0x41, 0x80, 0x7f, 0xcd, 0x41, 0x43, 0x4b, 0xf3,
      0x80, 0xc7, 0xdf, 0xdf, 0xd5, 0x27, 0x1f, 0x1f, 0x9f, 0x36, 0x24, 0x73,
      0x71, 0x7f, 0x80, 0x7f, 0x79, 0x42, 0x7f, 0x7f, 0x80, 0x80, 0x80, 0x2e,
      0x22, 0x7f, 0xf2, 0x46, 0x80, 0x80, 0xb4, 0xd2, 0x35, 0x2e, 0x80, 0x8f,
      0xb5, 0xbc, 0x80, 0x38, 0xf2, 0x7f, 0x10, 0x2d, 0x7f, 0x7f, 0x26, 0x91,
      0x7f, 0xf0, 0x7f, 0xdf, 0x2b, 0x7f, 0x80, 0x3e, 0x7f, 0x7f, 0x80, 0x80,
      0xab, 0xae, 0x7f, 0xca, 0x80, 0x80, 0xf3, 0xba, 0x34, 0x80, 0x80, 0x7f,
      0x7f, 0x80, 0x3e, 0x66, 0x80, 0x17, 0x80, 0xab, 0x80, 0x09, 0xf3, 0x7f,
      0x29, 0x80, 0xc4, 0x7f, 0x80, 0xd3, 0x7f, 0xba, 0x80, 0x7f, 0x80, 0x9d,
      0x7f, 0x80, 0x38, 0x80, 0x7f, 0x7f, 0x7f, 0x69, 0x7f, 0x7f, 0x15, 0x4f,
      0x80, 0x7c, 0x8c, 0x1b, 0x7f, 0x7f, 0x80, 0x80, 0x70, 0x2b, 0x80, 0x7f,
      0x5a, 0xc1, 0x7f, 0x80, 0x7f, 0x45, 0xbb, 0x80, 0x7f, 0xf7, 0xce, 0x80,
      0x80, 0x80, 0xda, 0x9d, 0x7f, 0x80, 0x7f, 0xba, 0xe2, 0x02, 0x80, 0x95,
      0xba, 0x80, 0xfa, 0xfe, 0x80, 0xb4, 0x80, 0x80, 0x88, 0x7f, 0x7f, 0x12,
      0x80, 0x80, 0x0e, 0x9b, 0x80, 0x80, 0x4f, 0xc9, 0x2b, 0x80, 0x77, 0xb5,
      0x7f, 0x51, 0x7f, 0x7f, 0x7f, 0x7f, 0x80, 0x7f, 0xf1, 0x80, 0x31, 0xe6,
      0x80, 0x7f, 0x80, 0xa5, 0x80, 0x7f, 0xca, 0x7f, 0x25, 0x80, 0x92, 0xb4,
      0x7f, 0x80, 0x97, 0x7f, 0x7f, 0x94, 0x20, 0x1b, 0x3b, 0x7f, 0xee, 0xca,
      0x80, 0x80, 0x42, 0x80, 0x80, 0xa3, 0x80, 0xc5, 0xf1, 0x80, 0x7f, 0x7f,
      0x7f, 0x51, 0xaf, 0x7f, 0x35, 0x42, 0x80, 0x7f, 0xf1, 0x80, 0xc5, 0x7f,
      0x7f, 0x7f, 0x80, 0x28, 0x7f, 0xb3, 0x2c, 0x2c, 0xea, 0x7f, 0x7f, 0x80,
      0x7f, 0x21, 0xa9, 0x7f, 0x34, 0x7f, 0xae, 0x1e, 0xc5, 0xbf, 0xae, 0x7f,
      0x8b, 0x37, 0x7f, 0x0d, 0x80, 0x73, 0x23, 0xbb, 0x80, 0x80, 0xc6, 0x80,
      0xb6, 0x80, 0x7f, 0x80, 0x80, 0x7f, 0x7f, 0x80, 0x21, 0x7f, 0x20, 0x45,
      0xa7, 0xca, 0x7f, 0x80, 0x80, 0x80, 0x3d, 0x7f, 0x15, 0x45, 0xf3, 0xd8,
      0x8b, 0x9b, 0xce, 0x55, 0x80, 0x80, 0x7f, 0xbd, 0xce, 0x7f, 0x36, 0x80,
      0x7f, 0xbf, 0x62, 0x23, 0x07, 0x25, 0xf1, 0xca, 0x59, 0x7f, 0xaa, 0x7f,
      0x7f, 0x47, 0x93, 0x80, 0x1b, 0x21, 0x80, 0x9b, 0xca, 0x80, 0x2d, 0x80,
      0x98, 0x7f, 0x7f, 0x7f, 0xee, 0x80, 0x80, 0x80, 0x7f, 0x20, 0x3b, 0x80,
      0x3c, 0x22, 0xcf, 0x7f, 0x80, 0x80, 0x59, 0x9d, 0x7f, 0x2a, 0x7f, 0x80,
      0x7c, 0x80, 0xd3, 0x21, 0x80, 0xa7, 0x7f, 0x7f, 0x80, 0x09, 0x3d, 0x7f,
      0x7f, 0xae, 0x80, 0xa7, 0x80, 0x7f, 0x73, 0x05, 0x3d, 0x80, 0x7f, 0x7f,
      0x7f, 0x26, 0x3b, 0x7f, 0xf6, 0x80, 0x7f, 0x5e, 0x47, 0xdf, 0x80, 0x7c,
      0x36, 0x36, 0x7f, 0xff, 0xbc, 0xbc, 0xbc, 0x7f, 0x7f, 0x7f, 0x80, 0x80,
      0x4d, 0x21, 0x7f, 0x7f, 0x7f, 0x41, 0x4d, 0x80, 0x7f, 0x7f, 0x80, 0xc0,
      0xaf, 0x2c, 0x7f, 0x17, 0x35, 0x80, 0x80, 0x7f, 0xf0, 0x3c, 0x12, 0x87,
      0x7f, 0x80, 0x80, 0x13, 0x73, 0x2d, 0x3e, 0x80, 0x7f, 0x80, 0xa6, 0xd8,
      0x19, 0x80, 0x7f, 0x27, 0x80, 0x7f, 0x80, 0x7f, 0x80, 0x7f, 0x23, 0x80,
      0x4d, 0x80, 0x7f, 0x7f, 0x89, 0x7f, 0x80, 0xb5, 0x4a, 0x17, 0xaf, 0x88,
      0x95, 0x80, 0x70, 0x77, 0x97, 0x7f, 0x80, 0x80, 0x22, 0x9b, 0x02, 0x2f,
      0x80, 0x80, 0x98, 0x7f, 0x7f, 0x12, 0x2d, 0x28, 0xce, 0xaf, 0x90, 0x58,
      0xe9, 0x1a, 0x71, 0x2f, 0x5c, 0x7f, 0x80, 0x7f, 0x7f, 0x80, 0x7f, 0x47,
      0xcd, 0xaf, 0x2c, 0x06, 0x80, 0x2f, 0x80, 0xe8, 0x80, 0x2e, 0x58, 0x11,
      0xd7, 0xad, 0x58, 0x43, 0x17, 0x9f, 0x70, 0xc3, 0x80, 0x70, 0x19, 0xc3,
      0x37, 0x2e, 0x42, 0x80, 0x2c, 0xbc, 0x80, 0x7f, 0x7f, 0x7f, 0x10, 0x45,
      0x2d, 0x3e, 0x3e, 0x90, 0x80, 0xa6, 0xd8, 0x5b, 0x80, 0x7f, 0x27, 0x80,
      0x7f, 0x80, 0x33, 0x80, 0x75, 0x80, 0x7f, 0x7f, 0x94, 0x80, 0x21, 0xf1,
      0x7f, 0xee, 0x7f, 0xae, 0xf6, 0xae, 0x80, 0x41, 0x80, 0xa5, 0x7f, 0x40,
      0x7f, 0x8a, 0x3d, 0x12, 0xdd, 0x7f, 0x9e, 0x7f, 0x92, 0x36, 0x66, 0x19,
      0x80, 0x80, 0xa7, 0xa0, 0x90, 0x80, 0x5f, 0x23, 0x57, 0x80, 0x31, 0x80,
      0x2d, 0x36, 0xa0, 0xd2, 0x8f, 0xd9, 0x3f, 0x80, 0x3e, 0x80, 0x29, 0xd8,
      0xad, 0x7f, 0x7f, 0x51, 0xbb, 0x70, 0xcb, 0xb5, 0xdc, 0x3d, 0xc2, 0xb7,
      0x7f, 0xba, 0x80, 0x3e, 0x80, 0x7f, 0x3b, 0x44, 0x80, 0xa6, 0x7f, 0x80,
      0x80, 0x7c, 0x80, 0x61, 0x7f, 0xca, 0x7f, 0x7f, 0x80, 0xff, 0x34, 0x7f,
      0x46, 0x05, 0x7f, 0x24, 0x7f, 0x7f, 0x7f, 0x7f, 0xbc, 0x7f, 0x7f, 0x7f,
      0x80, 0x7f, 0x15, 0x7f, 0xce, 0xe5, 0x7f, 0x80, 0x7f, 0xbd, 0x58, 0x85,
      0x33, 0x7f, 0x7e, 0x80, 0x80, 0x80, 0x7f, 0x7f, 0x80, 0x7f, 0xf7, 0x32,
      0x94, 0x40, 0x73, 0x7f, 0x7f, 0xee, 0xdc, 0x7f, 0x24, 0x7f, 0x7f, 0xba,
      0xc6, 0x27, 0x21, 0x95, 0x80, 0x3d, 0xa4, 0x80, 0x7f, 0x7f, 0x80, 0x7f,
      0x7f, 0x94, 0x7f, 0x7f, 0x94, 0x80, 0x61, 0x7f, 0x80, 0x7f, 0x7f, 0x79,
      0x80, 0x42, 0x7f, 0xbe, 0x80, 0x80, 0xc2, 0x43, 0xf7, 0xac, 0xac, 0x80,
      0x7f, 0x7f, 0x7f, 0x80, 0x14, 0x7f, 0x15, 0x7f, 0xc2, 0x1d, 0x7f, 0x80,
      0x7f, 0xbb, 0x80, 0x80, 0x80, 0x80, 0xb6, 0x7f, 0x7f, 0x44, 0x7f, 0x09,
      0x07, 0x80, 0x7f, 0x80, 0x7f, 0x7f, 0x96, 0x7f, 0xce, 0x80, 0x80, 0x61,
      0x65, 0x80, 0x2d, 0x4a, 0x7f, 0x7f, 0x80, 0x7f, 0x46, 0x80, 0x7f, 0xaa,
      0x44, 0x80, 0xcb, 0x89, 0x7f, 0x80, 0x7f, 0x80, 0x7f, 0x8e, 0x9f, 0x80,
      0xc3, 0x43, 0x71, 0x99, 0x80, 0x7f, 0x47, 0x41, 0xaf, 0x80, 0x3b, 0xb6,
      0x7f, 0x72, 0x80, 0xd1, 0x80, 0x7f, 0x44, 0x80, 0x2f, 0x7f, 0x7f, 0x42,
      0x80, 0x7f, 0xf0, 0x7f, 0x45, 0x7f, 0x80, 0x7f, 0x80, 0xc0, 0xaf, 0x7f,
      0x9c, 0x1e, 0x35, 0x7f, 0xca, 0x65, 0xf1, 0x3c, 0x92, 0xb4, 0xa0, 0x80,
      0x7f, 0x7f, 0x0f, 0xd7, 0x73, 0x80, 0x0e, 0x80, 0x7f, 0x80, 0x7c, 0xca,
      0xc7, 0xad, 0x80, 0x80, 0x3d, 0x9e, 0xf0, 0x82, 0x8d, 0xd9, 0x19, 0x7f,
      0x93, 0x7f, 0x80, 0x80, 0x80, 0x98, 0x80, 0x80, 0x7f, 0x3b, 0x28, 0xce,
      0x09, 0x7f, 0x5e, 0xe9, 0x80, 0x80, 0x7f, 0x45, 0x80, 0xfa, 0x7f, 0x7f,
      0x80, 0x7f, 0x80, 0x7f, 0x7f, 0x11, 0x80, 0xb4, 0x2c, 0x80, 0x13, 0x7f,
      0x80, 0x80, 0xc5, 0x7f, 0x7f, 0xee, 0x82, 0x80, 0x80, 0x41, 0x80, 0x11,
      0x7f, 0x80, 0xc1, 0x7f, 0xad, 0x7f, 0x7f, 0x7f, 0x81, 0xf1, 0x80, 0x31,
      0xa0, 0x80, 0x7f, 0x7f, 0x25, 0x57, 0x7f, 0xc4, 0x80, 0x2d, 0x36, 0x7f,
      0xbd, 0x80, 0xd9, 0x7f, 0xbb, 0x7f, 0x80, 0x2f, 0x7f, 0x36, 0x80, 0x3e,
      0x58, 0x80, 0x80, 0x41, 0x5f, 0x80, 0x22, 0x80, 0x80, 0xcc, 0x7f, 0x7f,
      0x24, 0xc5, 0x29, 0xe6, 0xc4, 0x7f, 0x80, 0xd1, 0x80, 0x3a, 0x0c, 0xa1,
      0x80, 0xb7, 0x7f, 0xbe, 0x80, 0x14, 0x95, 0x80, 0xf3, 0x7f, 0x89, 0x80,
      0xc1, 0x7f, 0x80, 0x7f, 0x7f, 0xa8, 0x1e, 0xc3, 0x43, 0x21, 0x80, 0x80,
      0x7f, 0x47, 0xcd, 0x7b, 0x80, 0x3b, 0x80, 0x7f, 0x25, 0x80, 0xd1, 0x27,
      0x89, 0x7f, 0x80, 0x28, 0xa4, 0x90, 0x7f, 0x59, 0x7f, 0x24, 0x7f, 0xb1,
      0x5c, 0x7f, 0xbf, 0x7f, 0x7f, 0x80, 0x16, 0x80, 0xdb, 0x80, 0x7f, 0x80,
      0x7f, 0x7f, 0xf5, 0xb2, 0x7f, 0x7f, 0x80, 0x7f, 0x0f, 0x80, 0x80, 0x80,
      0x77, 0x80, 0x2e, 0x80, 0x3c, 0xa0, 0x7f, 0x2b, 0x7f, 0x68, 0x80, 0xc0,
      0x7f, 0x7f, 0x7f, 0x10, 0xb5, 0x7f, 0xca, 0x11, 0x91, 0x80, 0x95, 0x7f,
      0x7f, 0x7f, 0x7f, 0x80, 0x80, 0xcb, 0x80, 0x7f, 0x81, 0x7f, 0xac, 0xaa,
      0x7f, 0x7f, 0x80, 0x93, 0x3a, 0xc0, 0x80, 0x80, 0x98, 0x52, 0x80, 0x7f,
      0xe1, 0xa8, 0xdc, 0x85, 0xb3, 0x76, 0x7f, 0xba, 0x80, 0x7f, 0xa3, 0x80,
      0xb4, 0x80, 0xc6, 0x21, 0x7f, 0x0f, 0x7f, 0x7f, 0x80, 0x09, 0x7f, 0x7f,
      0x7f, 0xa1, 0xf8, 0x7f, 0xa3, 0x7f, 0x26, 0x80, 0xc3, 0x80, 0x41, 0x2b,
      0x7f, 0x7f, 0x80, 0xc1, 0x55, 0x7f, 0x7f, 0x7f, 0xaf, 0x80, 0x80, 0x80,
      0x31, 0x80, 0x7f, 0x7f, 0xbf, 0x52, 0x39, 0x66, 0x73, 0xf7, 0x5c, 0xe9,
      0x80, 0x7f, 0x7f, 0x42, 0x55, 0x80, 0x80, 0x92, 0x7f, 0x7f, 0x80, 0x97,
      0x7f, 0x15, 0x80, 0x23, 0x1b, 0xbb, 0x9a, 0x80, 0x80, 0x80, 0xb6, 0x28,
      0xbe, 0x80, 0x7f, 0x0f, 0xeb, 0xf0, 0x80, 0x5f, 0xc9, 0x21, 0x6b, 0x7f,
      0x4c, 0x80, 0x7f, 0xad, 0xc4, 0xc1, 0x7f, 0x96, 0x7f, 0x7f, 0xaf, 0x7f,
      0xe1, 0x9e, 0x80, 0x7f, 0xb3, 0xf6, 0x80, 0x80, 0x80, 0x80, 0xab, 0xf0,
      0x80, 0x80, 0xfa, 0x3a, 0x7f, 0x80, 0x80, 0x89, 0x7f, 0x08, 0x7f, 0x80,
      0x7f, 0x80, 0xfa, 0x44, 0x8f, 0x09, 0x7f, 0x80, 0x7f, 0x80, 0x80, 0x22,
      0x9b, 0x7f, 0xb8, 0x80, 0x7f, 0x7f, 0x80, 0x7f, 0x15, 0x2d, 0x7f, 0x7f,
      0x7f, 0x95, 0x58, 0x93, 0x7f, 0xf0, 0xe2, 0xdc, 0x7f, 0x15, 0x7f, 0x80,
      0x7f, 0x81, 0x7f, 0xf2, 0x94, 0x80, 0x80, 0x7f, 0x80, 0x7f, 0xce, 0x80,
      0x80, 0x80, 0x80, 0x80, 0x9b, 0x80, 0x3f, 0xa2, 0x80, 0x98, 0x02, 0x7f,
      0x20, 0x29, 0xa8, 0x78, 0x7f, 0x44, 0x69, 0x11, 0x7f, 0xca, 0x41, 0x4d,
      0x17, 0x7f, 0x7f, 0x80, 0x80, 0x70, 0xf7, 0x7f, 0xfc, 0x80, 0x80, 0x7f,
      0xce, 0x7f, 0x80, 0x80, 0x4a, 0x1d, 0x80, 0x4d, 0x7f, 0x80, 0x7f, 0xf2,
      0x80, 0xfe, 0x80, 0x80, 0xec, 0x62, 0x7f, 0x7f, 0xff, 0x80, 0xcb, 0x80,
      0x7f, 0x80, 0xc0, 0x7f, 0x80, 0x4e, 0x21, 0x35, 0x0c, 0xaf, 0xb2, 0x7f,
      0x80, 0x3e, 0xf0, 0x96, 0xac, 0x7f, 0x2b, 0xea, 0x80, 0x80, 0x80, 0x80,
      0xa0, 0x7f, 0x44, 0x7f, 0x7f, 0x6d, 0xc7, 0x7f, 0x24, 0x80, 0x2a, 0x7f,
      0x80, 0x3c, 0x80, 0xec, 0x7f, 0x80, 0xe8, 0x80, 0xa4, 0x2a, 0x3e, 0x56,
      0x80, 0x80, 0xd3, 0xdb, 0xb5, 0xc0, 0x80, 0x7f, 0xaf, 0x14, 0x35, 0x80,
      0x38, 0x7f, 0x96, 0x7f, 0x7f, 0x68, 0x7f, 0x7f, 0x41, 0x7f, 0x44, 0x7f,
      0x80, 0xc7, 0xc7, 0x80, 0x80, 0x80, 0x14, 0x80, 0x7f, 0x7f, 0xdc, 0x1d,
      0x7f, 0x7f, 0x7f, 0xbf, 0x80, 0x5c, 0x80, 0x77, 0xf7, 0xc0, 0xc1, 0x80,
      0x23, 0x59, 0x80, 0x80, 0x7f, 0xad, 0xdc, 0x7f, 0x8a, 0x89, 0x7f, 0xba,
      0x7f, 0x7f, 0x80, 0xa9, 0x80, 0x80, 0x7f, 0x4b, 0x91, 0x7f, 0x4c, 0x7f,
      0x44, 0xaf, 0x7f, 0x7f, 0x80, 0x7f, 0x7f, 0xb8, 0x80, 0x3c, 0x7f, 0x3b,
      0x7f, 0x80, 0xe8, 0x80, 0x7f, 0x7a, 0x2c, 0x56, 0x80, 0x7f, 0x80, 0xe8,
      0x7f, 0x7f, 0x17, 0x3f, 0x7f, 0xd8, 0x05, 0x73, 0xdf, 0x2d, 0xb4, 0x80,
      0x7f, 0x95, 0x80, 0x8c, 0x7f, 0x7f, 0xe3, 0x80, 0x09, 0x25, 0x7f, 0x7f,
      0x7f, 0x7f, 0xaa, 0x7f, 0x15, 0xc3, 0xaf, 0xba, 0x80, 0x80, 0x2c, 0xf0,
      0xba, 0x7f, 0x7f, 0x68, 0x7f, 0x7f, 0x7f, 0x17, 0x4f, 0x85, 0x80, 0x80,
      0x70, 0x7f, 0x9b, 0x62, 0x2d, 0x80, 0x80, 0x9b, 0x80, 0x80, 0x95, 0x80,
      0x98, 0x7f, 0xf7, 0x7f, 0x36, 0x80, 0x80, 0x80, 0x7f, 0x27, 0x80, 0x7f,
      0xca, 0x27, 0x80, 0x0e, 0x80, 0x3a, 0x80, 0x80, 0x31, 0xf0, 0x7f, 0x94,
      0xb2, 0x52, 0x7f, 0x80, 0x80, 0x88, 0x5d, 0x05, 0xa3, 0x14, 0x91, 0x80,
      0xcc, 0x7f, 0x80, 0x7f, 0x7f, 0x80, 0x80, 0x7f, 0x80, 0x7f, 0x7f, 0x4c,
      0x7f, 0xf6, 0x7f, 0x7f, 0x80, 0xa4, 0x7f, 0x7f, 0x95, 0x7f, 0x24, 0x7f,
      0xf7, 0x62, 0x7f, 0x80, 0x21, 0x7f, 0x44, 0x7f, 0x43, 0x4d, 0xcb, 0x80,
      0x7f, 0x80, 0xc0, 0x80, 0x7f, 0x7f, 0x12, 0x35, 0x24, 0x4b, 0x93, 0x90,
      0x80, 0x80, 0xc7, 0x2b, 0x80, 0x3b, 0x08, 0x7f, 0x5e, 0x7f, 0x51, 0x80,
      0xa1, 0xb2, 0x80, 0x7f, 0xae, 0x80, 0x7f, 0x5a, 0x4b, 0xf7, 0x80, 0x80,
      0xc2, 0x7f, 0x80, 0x80, 0x92, 0x34, 0x80, 0x95, 0xac, 0x80, 0xa7, 0x7f,
      0x7f, 0x11, 0x3b, 0x3c, 0x7f, 0x80, 0x7f, 0x80, 0xe8, 0x66, 0x7f, 0x7f,
      0x17, 0xd7, 0xa3, 0x3a, 0x80, 0x70, 0x80, 0x80, 0x7f, 0x7f, 0x80, 0x80,
      0x80, 0x5c, 0x2d, 0x80, 0x17, 0x7f, 0x7f, 0x80, 0x38, 0x80, 0xab, 0x7f,
      0x0f, 0x80, 0x7f, 0x80, 0x80, 0xc8, 0xf1, 0xaa, 0x7f, 0x7f, 0x80, 0x7f,
      0x7f, 0x80, 0x4f, 0xa7, 0xc4, 0x80, 0x02, 0x37, 0x80, 0x3d, 0x80, 0x7f,
      0x7f, 0xb8, 0x7f, 0x80, 0x2f, 0x14, 0x13, 0x80, 0x38, 0x80, 0x7f, 0xf0,
      0x7f, 0x68, 0x7f, 0x59, 0xe9, 0x2a, 0xce, 0x7b, 0x5c, 0x80, 0xec, 0x7f,
      0x7f, 0x7f, 0xf8, 0x80, 0x80, 0x88, 0x2d, 0x7f, 0x43, 0x13, 0x91, 0xd8,
      0x80, 0xc4, 0x7f, 0x3b, 0x7f, 0x80, 0x80, 0xcb, 0x80, 0x80, 0x80, 0x7f,
      0xac, 0x7f, 0x26, 0x7f, 0x80, 0x80, 0xd9, 0x27, 0x1b, 0x7f, 0x7a, 0x34,
      0x7f, 0x80, 0x7f, 0x7f, 0x7f, 0x0c, 0x7f, 0x7f, 0x7f, 0x80, 0x7f, 0x80,
      0x17, 0x80, 0x6e, 0x80, 0x76, 0x80, 0x80, 0x5f, 0xa1, 0xa0, 0x9e, 0x7f,
      0x4d, 0x55, 0xd5, 0x19, 0x7f, 0x7f, 0x7f, 0x80, 0x13, 0xe7, 0x2c, 0x2c,
    ];
    const outNoise = [];
    for (let x = 0; x < Len; x++) {
      if (noise[x] & 0x80)
        outNoise.push((noise[x] & 0x7f) - 0x80); // signed char
      else outNoise.push(noise[x]);
    }
    return outNoise;
  }

  filter(input, fre, lowOrHigh) {
    let high;
    let mid = 0.0;
    let low = 0.0;
    const output = [];
    // Warm up
    for (let i = 0; i < input.length; i++) {
      high = input[i] - mid - low;
      high = Math.min(127.0, Math.max(-128.0, high));
      mid += high * fre;
      mid = Math.min(127.0, Math.max(-128.0, mid));
      low += mid * fre;
      low = Math.min(127.0, Math.max(-128.0, low));
    }
    // Real pass
    for (let i = 0; i < input.length; i++) {
      high = input[i] - mid - low;
      high = Math.min(127.0, Math.max(-128.0, high));
      mid += high * fre;
      mid = Math.min(127.0, Math.max(-128.0, mid));
      low += mid * fre;
      low = Math.min(127.0, Math.max(-128.0, low));
      if (lowOrHigh) output.push(Math.floor(high));
      else output.push(Math.floor(low));
    }
    return output;
  }

  init() {
    this.FilterSets[31] = {};
    this.FilterSets[31].Sawtooth04 = this.generateSawtooth(0x04);
    this.FilterSets[31].Sawtooth08 = this.generateSawtooth(0x08);
    this.FilterSets[31].Sawtooth10 = this.generateSawtooth(0x10);
    this.FilterSets[31].Sawtooth20 = this.generateSawtooth(0x20);
    this.FilterSets[31].Sawtooth40 = this.generateSawtooth(0x40);
    this.FilterSets[31].Sawtooth80 = this.generateSawtooth(0x80);
    this.FilterSets[31].Triangle04 = this.generateTriangle(0x04);
    this.FilterSets[31].Triangle08 = this.generateTriangle(0x08);
    this.FilterSets[31].Triangle10 = this.generateTriangle(0x10);
    this.FilterSets[31].Triangle20 = this.generateTriangle(0x20);
    this.FilterSets[31].Triangle40 = this.generateTriangle(0x40);
    this.FilterSets[31].Triangle80 = this.generateTriangle(0x80);
    this.FilterSets[31].Squares = this.generateSquare();
    this.FilterSets[31].WhiteNoiseBig = this.generateWhiteNoise(0x280 * 3);

    this.generateFilterWaveforms();
  }

  generateFilterWaveforms() {
    const src = this.FilterSets[31];
    let freq = 8;
    let temp = 0;
    while (temp < 31) {
      const dstLow = {};
      const dstHigh = {};
      const fre = (freq * 1.25) / 100.0;
      dstLow.Sawtooth04 = this.filter(src.Sawtooth04, fre, 0);
      dstLow.Sawtooth08 = this.filter(src.Sawtooth08, fre, 0);
      dstLow.Sawtooth10 = this.filter(src.Sawtooth10, fre, 0);
      dstLow.Sawtooth20 = this.filter(src.Sawtooth20, fre, 0);
      dstLow.Sawtooth40 = this.filter(src.Sawtooth40, fre, 0);
      dstLow.Sawtooth80 = this.filter(src.Sawtooth80, fre, 0);
      dstLow.Triangle04 = this.filter(src.Triangle04, fre, 0);
      dstLow.Triangle08 = this.filter(src.Triangle08, fre, 0);
      dstLow.Triangle10 = this.filter(src.Triangle10, fre, 0);
      dstLow.Triangle20 = this.filter(src.Triangle20, fre, 0);
      dstLow.Triangle40 = this.filter(src.Triangle40, fre, 0);
      dstLow.Triangle80 = this.filter(src.Triangle80, fre, 0);
      dstHigh.Sawtooth04 = this.filter(src.Sawtooth04, fre, 1);
      dstHigh.Sawtooth08 = this.filter(src.Sawtooth08, fre, 1);
      dstHigh.Sawtooth10 = this.filter(src.Sawtooth10, fre, 1);
      dstHigh.Sawtooth20 = this.filter(src.Sawtooth20, fre, 1);
      dstHigh.Sawtooth40 = this.filter(src.Sawtooth40, fre, 1);
      dstHigh.Sawtooth80 = this.filter(src.Sawtooth80, fre, 1);
      dstHigh.Triangle04 = this.filter(src.Triangle04, fre, 1);
      dstHigh.Triangle08 = this.filter(src.Triangle08, fre, 1);
      dstHigh.Triangle10 = this.filter(src.Triangle10, fre, 1);
      dstHigh.Triangle20 = this.filter(src.Triangle20, fre, 1);
      dstHigh.Triangle40 = this.filter(src.Triangle40, fre, 1);
      dstHigh.Triangle80 = this.filter(src.Triangle80, fre, 1);

      dstLow.Squares = [];
      dstHigh.Squares = [];
      for (let i = 0; i < 0x20; i++) {
        dstLow.Squares = dstLow.Squares.concat(
          this.filter(src.Squares.slice(i * 0x80, (i + 1) * 0x80), fre, 0),
        );
        dstHigh.Squares = dstHigh.Squares.concat(
          this.filter(src.Squares.slice(i * 0x80, (i + 1) * 0x80), fre, 1),
        );
      }
      dstLow.WhiteNoiseBig = this.filter(src.WhiteNoiseBig, fre, 0);
      dstHigh.WhiteNoiseBig = this.filter(src.WhiteNoiseBig, fre, 1);

      this.FilterSets[temp] = dstLow;
      this.FilterSets[temp + 32] = dstHigh;

      temp++;
      freq += 3;
    }
  }
}

class AHXVoice {
  constructor() {
    this.VoiceVolume = 0;
    this.VoicePeriod = 0;
    this.VoiceBuffer = [];
    this.Track = 0;
    this.Transpose = 0;
    this.NextTrack = 0;
    this.NextTranspose = 0;
    this.ADSRVolume = 0;
    this.ADSR = createEnvelope();
    this.Instrument = null;
    this.InstrPeriod = 0;
    this.TrackPeriod = 0;
    this.VibratoPeriod = 0;
    this.NoteMaxVolume = 0;
    this.PerfSubVolume = 0;
    this.TrackMasterVolume = 0x40;
    this.NewWaveform = 0;
    this.Waveform = 0;
    this.PlantSquare = 0;
    this.PlantPeriod = 0;
    this.IgnoreSquare = 0;
    this.TrackOn = 1;
    this.FixedNote = 0;
    this.VolumeSlideUp = 0;
    this.VolumeSlideDown = 0;
    this.HardCut = 0;
    this.HardCutRelease = 0;
    this.HardCutReleaseF = 0;
    this.PeriodSlideSpeed = 0;
    this.PeriodSlidePeriod = 0;
    this.PeriodSlideLimit = 0;
    this.PeriodSlideOn = 0;
    this.PeriodSlideWithLimit = 0;
    this.PeriodPerfSlideSpeed = 0;
    this.PeriodPerfSlidePeriod = 0;
    this.PeriodPerfSlideOn = 0;
    this.VibratoDelay = 0;
    this.VibratoCurrent = 0;
    this.VibratoDepth = 0;
    this.VibratoSpeed = 0;
    this.SquareOn = 0;
    this.SquareInit = 0;
    this.SquareWait = 0;
    this.SquareLowerLimit = 0;
    this.SquareUpperLimit = 0;
    this.SquarePos = 0;
    this.SquareSign = 0;
    this.SquareSlidingIn = 0;
    this.SquareReverse = 0;
    this.FilterOn = 0;
    this.FilterInit = 0;
    this.FilterWait = 0;
    this.FilterLowerLimit = 0;
    this.FilterUpperLimit = 0;
    this.FilterPos = 0;
    this.FilterSign = 0;
    this.FilterSpeed = 0;
    this.FilterSlidingIn = 0;
    this.IgnoreFilter = 0;
    this.PerfCurrent = 0;
    this.PerfSpeed = 0;
    this.PerfWait = 0;
    this.WaveLength = 0;
    this.PerfList = null;
    this.NoteDelayWait = 0;
    this.NoteDelayOn = 0;
    this.NoteCutWait = 0;
    this.NoteCutOn = 0;
    this.AudioSource = [];
    this.AudioPeriod = 0;
    this.AudioVolume = 0;
  }

  calcADSR() {
    this.ADSR.aFrames = this.Instrument.Envelope.aFrames;
    this.ADSR.aVolume =
      (this.Instrument.Envelope.aVolume * 256) / this.ADSR.aFrames;
    this.ADSR.dFrames = this.Instrument.Envelope.dFrames;
    this.ADSR.dVolume =
      ((this.Instrument.Envelope.dVolume - this.Instrument.Envelope.aVolume) *
        256) /
      this.ADSR.dFrames;
    this.ADSR.sFrames = this.Instrument.Envelope.sFrames;
    this.ADSR.rFrames = this.Instrument.Envelope.rFrames;
    this.ADSR.rVolume =
      ((this.Instrument.Envelope.rVolume - this.Instrument.Envelope.dVolume) *
        256) /
      this.ADSR.rFrames;
  }
}

class AHXSong {
  constructor() {
    this.Name = '';
    this.Restart = 0;
    this.PositionNr = 0;
    this.TrackLength = 0;
    this.TrackNr = 0;
    this.InstrumentNr = 0;
    this.SubsongNr = 0;
    this.Revision = 0;
    this.SpeedMultiplier = 0;
    this.Positions = [];
    this.Tracks = [];
    this.Instruments = [];
    this.Subsongs = [];
  }

  async LoadSong(url) {
    try {
      const response = await fetch(url);
      const buffer = await response.arrayBuffer();
      const bytes = new Uint8Array(buffer);
      const stream = new AHXStream(bytes);
      this.InitSong(stream);
    } catch (err) {
      console.error('AHX Load Error:', err);
      throw err;
    }
  }

  InitSong(stream) {
    stream.pos = 3;
    this.Revision = stream.readByte();
    let SBPtr = 14;

    // Header
    const NamePtr = stream.readShort();
    this.Name = stream.readStringAt(NamePtr);
    this.SpeedMultiplier = ((stream.readByteAt(6) >> 5) & 3) + 1;

    this.PositionNr =
      ((stream.readByteAt(6) & 0xf) << 8) | stream.readByteAt(7);
    this.Restart = (stream.readByteAt(8) << 8) | stream.readByteAt(9);
    this.TrackLength = stream.readByteAt(10);
    this.TrackNr = stream.readByteAt(11);
    this.InstrumentNr = stream.readByteAt(12);
    this.SubsongNr = stream.readByteAt(13);

    // Subsongs
    for (let i = 0; i < this.SubsongNr; i++) {
      this.Subsongs.push(
        (stream.readByteAt(SBPtr + 0) << 8) | stream.readByteAt(SBPtr + 1),
      );
      SBPtr += 2;
    }

    // Position List
    for (let i = 0; i < this.PositionNr; i++) {
      const Pos = { Track: [], Transpose: [] };
      for (let j = 0; j < 4; j++) {
        Pos.Track.push(stream.readByteAt(SBPtr++));
        let Transpose = stream.readByteAt(SBPtr++);
        if (Transpose & 0x80) Transpose = (Transpose & 0x7f) - 0x80; // signed char
        Pos.Transpose.push(Transpose);
      }
      this.Positions.push(Pos);
    }

    // Tracks
    const MaxTrack = this.TrackNr;
    for (let i = 0; i < MaxTrack + 1; i++) {
      const Track = [];
      if ((stream.readByteAt(6) & 0x80) == 0x80 && i == 0) {
        // empty track
        for (let j = 0; j < this.TrackLength; j++) {
          Track.push({ Note: 0, Instrument: 0, FX: 0, FXParam: 0 });
        }
      } else {
        for (let j = 0; j < this.TrackLength; j++) {
          const Step = {
            Note: (stream.readByteAt(SBPtr) >> 2) & 0x3f,
            Instrument:
              ((stream.readByteAt(SBPtr) & 0x3) << 4) |
              (stream.readByteAt(SBPtr + 1) >> 4),
            FX: stream.readByteAt(SBPtr + 1) & 0xf,
            FXParam: stream.readByteAt(SBPtr + 2),
          };
          Track.push(Step);
          SBPtr += 3;
        }
      }
      this.Tracks.push(Track);
    }

    // Instruments
    // Pointer-Logik fixen: Wir starten nach dem Songnamen
    let currentNamePtr = (stream.readByteAt(4) << 8) | stream.readByteAt(5);
    currentNamePtr += this.Name.length + 1;

    // Resetting instruments array
    // Instrument 0 ist immer leer/dummy
    this.Instruments = [this._createDefaultInstrument()];

    for (let i = 1; i < this.InstrumentNr + 1; i++) {
      const Instrument = this._createDefaultInstrument();

      // Name lesen und Pointer weiterschieben
      Instrument.Name = stream.readStringAt(currentNamePtr);
      currentNamePtr += Instrument.Name.length + 1;

      Instrument.Volume = stream.readByteAt(SBPtr + 0);
      Instrument.FilterSpeed =
        ((stream.readByteAt(SBPtr + 1) >> 3) & 0x1f) |
        ((stream.readByteAt(SBPtr + 12) >> 2) & 0x20);
      Instrument.WaveLength = stream.readByteAt(SBPtr + 1) & 0x7;
      Instrument.Envelope.aFrames = stream.readByteAt(SBPtr + 2);
      Instrument.Envelope.aVolume = stream.readByteAt(SBPtr + 3);
      Instrument.Envelope.dFrames = stream.readByteAt(SBPtr + 4);
      Instrument.Envelope.dVolume = stream.readByteAt(SBPtr + 5);
      Instrument.Envelope.sFrames = stream.readByteAt(SBPtr + 6);
      Instrument.Envelope.rFrames = stream.readByteAt(SBPtr + 7);
      Instrument.Envelope.rVolume = stream.readByteAt(SBPtr + 8);
      Instrument.FilterLowerLimit = stream.readByteAt(SBPtr + 12) & 0x7f;
      Instrument.VibratoDelay = stream.readByteAt(SBPtr + 13);
      Instrument.HardCutReleaseFrames =
        (stream.readByteAt(SBPtr + 14) >> 4) & 7;
      Instrument.HardCutRelease = stream.readByteAt(SBPtr + 14) & 0x80 ? 1 : 0;
      Instrument.VibratoDepth = stream.readByteAt(SBPtr + 14) & 0xf;
      Instrument.VibratoSpeed = stream.readByteAt(SBPtr + 15);
      Instrument.SquareLowerLimit = stream.readByteAt(SBPtr + 16);
      Instrument.SquareUpperLimit = stream.readByteAt(SBPtr + 17);
      Instrument.SquareSpeed = stream.readByteAt(SBPtr + 18);
      Instrument.FilterUpperLimit = stream.readByteAt(SBPtr + 19) & 0x3f;
      Instrument.PList.Speed = stream.readByteAt(SBPtr + 20);
      Instrument.PList.Length = stream.readByteAt(SBPtr + 21);
      SBPtr += 22;

      for (let j = 0; j < Instrument.PList.Length; j++) {
        const Entry = {
          Note: 0,
          Fixed: 0,
          Waveform: 0,
          FX: [0, 0],
          FXParam: [0, 0],
        };
        Entry.FX[0] = (stream.readByteAt(SBPtr + 0) >> 2) & 7;
        Entry.FX[1] = (stream.readByteAt(SBPtr + 0) >> 5) & 7;
        Entry.Waveform =
          ((stream.readByteAt(SBPtr + 0) << 1) & 6) |
          (stream.readByteAt(SBPtr + 1) >> 7);
        Entry.Fixed = (stream.readByteAt(SBPtr + 1) >> 6) & 1;
        Entry.Note = stream.readByteAt(SBPtr + 1) & 0x3f;
        Entry.FXParam[0] = stream.readByteAt(SBPtr + 2);
        Entry.FXParam[1] = stream.readByteAt(SBPtr + 3);
        Instrument.PList.Entries.push(Entry);
        SBPtr += 4;
      }
      this.Instruments.push(Instrument);
    }
  }

  // Hilfsmethode, damit der Code sauberer bleibt
  _createDefaultInstrument() {
    return {
      Name: '',
      Volume: 0,
      WaveLength: 0,
      Envelope: {
        aFrames: 0,
        aVolume: 0,
        dFrames: 0,
        dVolume: 0,
        sFrames: 0,
        rFrames: 0,
        rVolume: 0,
      },
      FilterLowerLimit: 0,
      FilterUpperLimit: 0,
      FilterSpeed: 0,
      SquareLowerLimit: 0,
      SquareUpperLimit: 0,
      SquareSpeed: 0,
      VibratoDelay: 0,
      VibratoDepth: 0,
      VibratoSpeed: 0,
      HardCutRelease: 0,
      HardCutReleaseFrames: 0,
      PList: { Speed: 0, Length: 0, Entries: [] },
    };
  }
}

class AHXPlayer {
  constructor(waves) {
    this.StepWaitFrames = 0;
    this.GetNewPosition = 0;
    this.SongEndReached = 0;
    this.TimingValue = 0;
    this.PatternBreak = 0;
    this.MainVolume = 0x40;
    this.Playing = 0;
    this.Tempo = 0;
    this.PosNr = 0;
    this.PosJump = 0;
    this.NoteNr = 0;
    this.PosJumpNote = 0;
    this.Waves = waves || new AHXWaves();
    this.Voices = [];
    this.WNRandom = 0;
    this.Song = new AHXSong();
    this.PlayingTime = 0;

    this.VibratoTable = [
      0, 24, 49, 74, 97, 120, 141, 161, 180, 197, 212, 224, 235, 244, 250, 253,
      255, 253, 250, 244, 235, 224, 212, 197, 180, 161, 141, 120, 97, 74, 49,
      24, 0, -24, -49, -74, -97, -120, -141, -161, -180, -197, -212, -224, -235,
      -244, -250, -253, -255, -253, -250, -244, -235, -224, -212, -197, -180,
      -161, -141, -120, -97, -74, -49, -24,
    ];

    this.PeriodTable = [
      0x0000, 0x0d60, 0x0ca0, 0x0be8, 0x0b40, 0x0a98, 0x0a00, 0x0970, 0x08e8,
      0x0868, 0x07f0, 0x0780, 0x0714, 0x06b0, 0x0650, 0x05f4, 0x05a0, 0x054c,
      0x0500, 0x04b8, 0x0474, 0x0434, 0x03f8, 0x03c0, 0x038a, 0x0358, 0x0328,
      0x02fa, 0x02d0, 0x02a6, 0x0280, 0x025c, 0x023a, 0x021a, 0x01fc, 0x01e0,
      0x01c5, 0x01ac, 0x0194, 0x017d, 0x0168, 0x0153, 0x0140, 0x012e, 0x011d,
      0x010d, 0x00fe, 0x00f0, 0x00e2, 0x00d6, 0x00ca, 0x00be, 0x00b4, 0x00aa,
      0x00a0, 0x0097, 0x008f, 0x0087, 0x007f, 0x0078, 0x0071,
    ];
  }

  InitSong(song) {
    this.Song = song;
  }

  InitSubsong(Nr) {
    if (Nr > this.Song.SubsongNr) return 0;

    if (Nr == 0) this.PosNr = 0;
    else this.PosNr = this.Song.Subsongs[Nr - 1];

    this.PosJump = 0;
    this.PatternBreak = 0;
    this.Playing = 1;
    this.NoteNr = this.PosJumpNote = 0;
    this.Tempo = 6;
    this.StepWaitFrames = 0;
    this.GetNewPosition = 1;
    this.SongEndReached = 0;
    this.TimingValue = this.PlayingTime = 0;

    this.Voices = [
      new AHXVoice(),
      new AHXVoice(),
      new AHXVoice(),
      new AHXVoice(),
    ];
    return 1;
  }

  PlayIRQ() {
    if (this.Tempo > 0 && this.StepWaitFrames <= 0) {
      if (this.GetNewPosition) {
        let NextPos =
          this.PosNr + 1 == this.Song.PositionNr ? 0 : this.PosNr + 1;
        if (this.PosNr >= this.Song.Positions.length) {
          this.PosNr = this.Song.PositionNr - 1;
        }
        if (NextPos >= this.Song.Positions.length) {
          NextPos = this.Song.PositionNr - 1;
        }
        for (let i = 0; i < 4; i++) {
          this.Voices[i].Track = this.Song.Positions[this.PosNr].Track[i];
          this.Voices[i].Transpose =
            this.Song.Positions[this.PosNr].Transpose[i];
          this.Voices[i].NextTrack = this.Song.Positions[NextPos].Track[i];
          this.Voices[i].NextTranspose =
            this.Song.Positions[NextPos].Transpose[i];
        }
        this.GetNewPosition = 0;
      }
      for (let i = 0; i < 4; i++) this.ProcessStep(i);
      this.StepWaitFrames = this.Tempo;
    }

    for (let i = 0; i < 4; i++) this.ProcessFrame(i);
    this.PlayingTime++;

    if (this.Tempo > 0 && --this.StepWaitFrames <= 0) {
      if (!this.PatternBreak) {
        this.NoteNr++;
        if (this.NoteNr >= this.Song.TrackLength) {
          this.PosJump = this.PosNr + 1;
          this.PosJumpNote = 0;
          this.PatternBreak = 1;
        }
      }
      if (this.PatternBreak) {
        this.PatternBreak = 0;
        this.NoteNr = this.PosJumpNote;
        this.PosJumpNote = 0;
        this.PosNr = this.PosJump;
        this.PosJump = 0;
        if (this.PosNr == this.Song.PositionNr) {
          this.SongEndReached = 1;
          this.PosNr = this.Song.Restart;
        }
        this.GetNewPosition = 1;
      }
    }

    for (let a = 0; a < 4; a++) this.SetAudio(a);
  }

  ProcessStep(v) {
    if (!this.Voices[v].TrackOn) return;
    this.Voices[v].VolumeSlideUp = this.Voices[v].VolumeSlideDown = 0;

    let Note =
      this.Song.Tracks[this.Song.Positions[this.PosNr].Track[v]][this.NoteNr]
        .Note;
    let Instrument =
      this.Song.Tracks[this.Song.Positions[this.PosNr].Track[v]][this.NoteNr]
        .Instrument;
    let FX =
      this.Song.Tracks[this.Song.Positions[this.PosNr].Track[v]][this.NoteNr]
        .FX;
    let FXParam =
      this.Song.Tracks[this.Song.Positions[this.PosNr].Track[v]][this.NoteNr]
        .FXParam;

    switch (FX) {
      case 0x0: // Position Jump HI
        if ((FXParam & 0xf) > 0 && (FXParam & 0xf) <= 9)
          this.PosJump = FXParam & 0xf;
        break;
      case 0x5: // Volume Slide + Tone Portamento
      case 0xa: // Volume Slide
        this.Voices[v].VolumeSlideDown = FXParam & 0x0f;
        this.Voices[v].VolumeSlideUp = FXParam >> 4;
        break;
      case 0xb: // Position Jump
        this.PosJump =
          this.PosJump * 100 + (FXParam & 0x0f) + (FXParam >> 4) * 10;
        this.PatternBreak = 1;
        break;
      case 0xd: // Patternbreak
        this.PosJump = this.PosNr + 1;
        this.PosJumpNote = (FXParam & 0x0f) + (FXParam >> 4) * 10;
        if (this.PosJumpNote > this.Song.TrackLength) this.PosJumpNote = 0;
        this.PatternBreak = 1;
        break;
      case 0xe: // Enhanced commands
        switch (FXParam >> 4) {
          case 0xc: // Note Cut
            if ((FXParam & 0x0f) < this.Tempo) {
              this.Voices[v].NoteCutWait = FXParam & 0x0f;
              if (this.Voices[v].NoteCutWait) {
                this.Voices[v].NoteCutOn = 1;
                this.Voices[v].HardCutRelease = 0;
              }
            }
            break;
          case 0xd: // Note Delay
            if (this.Voices[v].NoteDelayOn) {
              this.Voices[v].NoteDelayOn = 0;
            } else {
              if ((FXParam & 0x0f) < this.Tempo) {
                this.Voices[v].NoteDelayWait = FXParam & 0x0f;
                if (this.Voices[v].NoteDelayWait) {
                  this.Voices[v].NoteDelayOn = 1;
                  return;
                }
              }
            }
            break;
        }
        break;
      case 0xf: // Speed
        this.Tempo = FXParam;
        break;
    }
    if (Instrument) {
      this.Voices[v].PerfSubVolume = 0x40;
      this.Voices[v].PeriodSlideSpeed =
        this.Voices[v].PeriodSlidePeriod =
        this.Voices[v].PeriodSlideLimit =
          0;
      this.Voices[v].ADSRVolume = 0;
      if (Instrument < this.Song.Instruments.length) {
        this.Voices[v].Instrument = this.Song.Instruments[Instrument];
      } else {
        this.Voices[v].Instrument = this.Song.Instruments[0];
      }
      this.Voices[v].calcADSR();
      this.Voices[v].WaveLength = this.Voices[v].Instrument.WaveLength;
      this.Voices[v].NoteMaxVolume = this.Voices[v].Instrument.Volume;
      this.Voices[v].VibratoCurrent = 0;
      this.Voices[v].VibratoDelay = this.Voices[v].Instrument.VibratoDelay;
      this.Voices[v].VibratoDepth = this.Voices[v].Instrument.VibratoDepth;
      this.Voices[v].VibratoSpeed = this.Voices[v].Instrument.VibratoSpeed;
      this.Voices[v].VibratoPeriod = 0;
      this.Voices[v].HardCutRelease = this.Voices[v].Instrument.HardCutRelease;
      this.Voices[v].HardCut = this.Voices[v].Instrument.HardCutReleaseFrames;
      this.Voices[v].IgnoreSquare = this.Voices[v].SquareSlidingIn = 0;
      this.Voices[v].SquareWait = this.Voices[v].SquareOn = 0;
      let SquareLower =
        this.Voices[v].Instrument.SquareLowerLimit >>
        (5 - this.Voices[v].WaveLength);
      let SquareUpper =
        this.Voices[v].Instrument.SquareUpperLimit >>
        (5 - this.Voices[v].WaveLength);
      if (SquareUpper < SquareLower) {
        const t = SquareUpper;
        SquareUpper = SquareLower;
        SquareLower = t;
      }
      this.Voices[v].SquareUpperLimit = SquareUpper;
      this.Voices[v].SquareLowerLimit = SquareLower;
      this.Voices[v].IgnoreFilter =
        this.Voices[v].FilterWait =
        this.Voices[v].FilterOn =
          0;
      this.Voices[v].FilterSlidingIn = 0;
      let d6 = this.Voices[v].Instrument.FilterSpeed;
      let d3 = this.Voices[v].Instrument.FilterLowerLimit;
      let d4 = this.Voices[v].Instrument.FilterUpperLimit;
      if (d3 & 0x80) d6 |= 0x20;
      if (d4 & 0x80) d6 |= 0x40;
      this.Voices[v].FilterSpeed = d6;
      d3 &= ~0x80;
      d4 &= ~0x80;
      if (d3 > d4) {
        const t = d3;
        d3 = d4;
        d4 = t;
      }
      this.Voices[v].FilterUpperLimit = d4;
      this.Voices[v].FilterLowerLimit = d3;
      this.Voices[v].FilterPos = 32;
      this.Voices[v].PerfWait = this.Voices[v].PerfCurrent = 0;
      this.Voices[v].PerfSpeed = this.Voices[v].Instrument.PList.Speed;
      this.Voices[v].PerfList = this.Voices[v].Instrument.PList;
    }

    this.Voices[v].PeriodSlideOn = 0;

    switch (FX) {
      case 0x4:
        break;
      case 0x9: // Set Squarewave-Offset
        this.Voices[v].SquarePos = FXParam >> (5 - this.Voices[v].WaveLength);
        this.Voices[v].PlantSquare = 1;
        this.Voices[v].IgnoreSquare = 1;
        break;
      case 0x5: // Tone Portamento + Volume Slide
      case 0x3: // Tone Portamento
        if (FXParam != 0) this.Voices[v].PeriodSlideSpeed = FXParam;
        if (Note) {
          let Neue = this.PeriodTable[Note];
          let Alte = this.PeriodTable[this.Voices[v].TrackPeriod];
          Alte -= Neue;
          Neue = Alte + this.Voices[v].PeriodSlidePeriod;
          if (Neue) this.Voices[v].PeriodSlideLimit = -Alte;
        }
        this.Voices[v].PeriodSlideOn = 1;
        this.Voices[v].PeriodSlideWithLimit = 1;
        Note = 0;
        break;
    }

    if (Note) {
      this.Voices[v].TrackPeriod = Note;
      this.Voices[v].PlantPeriod = 1;
    }

    switch (FX) {
      case 0x1: // Portamento up
        this.Voices[v].PeriodSlideSpeed = -FXParam;
        this.Voices[v].PeriodSlideOn = 1;
        this.Voices[v].PeriodSlideWithLimit = 0;
        break;
      case 0x2: // Portamento down
        this.Voices[v].PeriodSlideSpeed = FXParam;
        this.Voices[v].PeriodSlideOn = 1;
        this.Voices[v].PeriodSlideWithLimit = 0;
        break;
      case 0xc: // Volume
        if (FXParam <= 0x40) this.Voices[v].NoteMaxVolume = FXParam;
        else {
          FXParam -= 0x50;
          if (FXParam <= 0x40)
            for (let i = 0; i < 4; i++)
              this.Voices[i].TrackMasterVolume = FXParam;
          else {
            FXParam -= 0xa0 - 0x50;
            if (FXParam <= 0x40) this.Voices[v].TrackMasterVolume = FXParam;
          }
        }
        break;
      case 0xe: // Enhanced commands
        switch (FXParam >> 4) {
          case 0x1:
            this.Voices[v].PeriodSlidePeriod = -(FXParam & 0x0f);
            this.Voices[v].PlantPeriod = 1;
            break;
          case 0x2:
            this.Voices[v].PeriodSlidePeriod = FXParam & 0x0f;
            this.Voices[v].PlantPeriod = 1;
            break;
          case 0x4:
            this.Voices[v].VibratoDepth = FXParam & 0x0f;
            break;
          case 0xa:
            this.Voices[v].NoteMaxVolume += FXParam & 0x0f;
            if (this.Voices[v].NoteMaxVolume > 0x40)
              this.Voices[v].NoteMaxVolume = 0x40;
            break;
          case 0xb:
            this.Voices[v].NoteMaxVolume -= FXParam & 0x0f;
            if (this.Voices[v].NoteMaxVolume < 0)
              this.Voices[v].NoteMaxVolume = 0;
            break;
        }
        break;
    }
  }

  ProcessFrame(v) {
    if (!this.Voices[v].TrackOn) return;

    if (this.Voices[v].NoteDelayOn) {
      if (this.Voices[v].NoteDelayWait <= 0) this.ProcessStep(v);
      else this.Voices[v].NoteDelayWait--;
    }
    if (this.Voices[v].HardCut) {
      let NextInstrument;
      if (this.NoteNr + 1 < this.Song.TrackLength)
        NextInstrument =
          this.Song.Tracks[this.Voices[v].Track][this.NoteNr + 1].Instrument;
      else
        NextInstrument =
          this.Song.Tracks[this.Voices[v].NextTrack][0].Instrument;
      if (NextInstrument) {
        let d1 = this.Tempo - this.Voices[v].HardCut;
        if (d1 < 0) d1 = 0;
        if (!this.Voices[v].NoteCutOn) {
          this.Voices[v].NoteCutOn = 1;
          this.Voices[v].NoteCutWait = d1;
          this.Voices[v].HardCutReleaseF = -(d1 - this.Tempo);
        } else this.Voices[v].HardCut = 0;
      }
    }
    if (this.Voices[v].NoteCutOn) {
      if (this.Voices[v].NoteCutWait <= 0) {
        this.Voices[v].NoteCutOn = 0;
        if (this.Voices[v].HardCutRelease) {
          this.Voices[v].ADSR.rVolume =
            -(
              this.Voices[v].ADSRVolume -
              (this.Voices[v].Instrument.Envelope.rVolume << 8)
            ) / this.Voices[v].HardCutReleaseF;
          this.Voices[v].ADSR.rFrames = this.Voices[v].HardCutReleaseF;
          this.Voices[v].ADSR.aFrames =
            this.Voices[v].ADSR.dFrames =
            this.Voices[v].ADSR.sFrames =
              0;
        } else this.Voices[v].NoteMaxVolume = 0;
      } else this.Voices[v].NoteCutWait--;
    }
    //adsrEnvelope
    if (this.Voices[v].ADSR.aFrames) {
      this.Voices[v].ADSRVolume += this.Voices[v].ADSR.aVolume;
      if (--this.Voices[v].ADSR.aFrames <= 0)
        this.Voices[v].ADSRVolume =
          this.Voices[v].Instrument.Envelope.aVolume << 8;
    } else if (this.Voices[v].ADSR.dFrames) {
      this.Voices[v].ADSRVolume += this.Voices[v].ADSR.dVolume;
      if (--this.Voices[v].ADSR.dFrames <= 0)
        this.Voices[v].ADSRVolume =
          this.Voices[v].Instrument.Envelope.dVolume << 8;
    } else if (this.Voices[v].ADSR.sFrames) {
      this.Voices[v].ADSR.sFrames--;
    } else if (this.Voices[v].ADSR.rFrames) {
      this.Voices[v].ADSRVolume += this.Voices[v].ADSR.rVolume;
      if (--this.Voices[v].ADSR.rFrames <= 0)
        this.Voices[v].ADSRVolume =
          this.Voices[v].Instrument.Envelope.rVolume << 8;
    }

    //VolumeSlide
    this.Voices[v].NoteMaxVolume =
      this.Voices[v].NoteMaxVolume +
      this.Voices[v].VolumeSlideUp -
      this.Voices[v].VolumeSlideDown;
    if (this.Voices[v].NoteMaxVolume < 0) this.Voices[v].NoteMaxVolume = 0;
    if (this.Voices[v].NoteMaxVolume > 0x40)
      this.Voices[v].NoteMaxVolume = 0x40;

    //Portamento
    if (this.Voices[v].PeriodSlideOn) {
      if (this.Voices[v].PeriodSlideWithLimit) {
        let d0 =
          this.Voices[v].PeriodSlidePeriod - this.Voices[v].PeriodSlideLimit;
        let d2 = this.Voices[v].PeriodSlideSpeed;
        if (d0 > 0) d2 = -d2;
        if (d0) {
          let d3 = (d0 + d2) ^ d0;
          if (d3 >= 0) d0 = this.Voices[v].PeriodSlidePeriod + d2;
          else d0 = this.Voices[v].PeriodSlideLimit;
          this.Voices[v].PeriodSlidePeriod = d0;
          this.Voices[v].PlantPeriod = 1;
        }
      } else {
        this.Voices[v].PeriodSlidePeriod += this.Voices[v].PeriodSlideSpeed;
        this.Voices[v].PlantPeriod = 1;
      }
    }

    //Vibrato
    if (this.Voices[v].VibratoDepth) {
      if (this.Voices[v].VibratoDelay <= 0) {
        this.Voices[v].VibratoPeriod =
          (this.VibratoTable[this.Voices[v].VibratoCurrent] *
            this.Voices[v].VibratoDepth) >>
          7;
        this.Voices[v].PlantPeriod = 1;
        this.Voices[v].VibratoCurrent =
          (this.Voices[v].VibratoCurrent + this.Voices[v].VibratoSpeed) & 0x3f;
      } else this.Voices[v].VibratoDelay--;
    }

    //PList
    if (
      this.Voices[v].Instrument &&
      this.Voices[v].PerfCurrent < this.Voices[v].Instrument.PList.Length
    ) {
      if (--this.Voices[v].PerfWait <= 0) {
        let Cur = this.Voices[v].PerfCurrent++;
        this.Voices[v].PerfWait = this.Voices[v].PerfSpeed;
        if (this.Voices[v].PerfList.Entries[Cur].Waveform) {
          this.Voices[v].Waveform =
            this.Voices[v].PerfList.Entries[Cur].Waveform - 1;
          this.Voices[v].NewWaveform = 1;
          this.Voices[v].PeriodPerfSlideSpeed = this.Voices[
            v
          ].PeriodPerfSlidePeriod = 0;
        }
        this.Voices[v].PeriodPerfSlideOn = 0;
        for (let i = 0; i < 2; i++)
          this.PListCommandParse(
            v,
            this.Voices[v].PerfList.Entries[Cur].FX[i],
            this.Voices[v].PerfList.Entries[Cur].FXParam[i],
          );
        if (this.Voices[v].PerfList.Entries[Cur].Note) {
          this.Voices[v].InstrPeriod =
            this.Voices[v].PerfList.Entries[Cur].Note;
          this.Voices[v].PlantPeriod = 1;
          this.Voices[v].FixedNote = this.Voices[v].PerfList.Entries[Cur].Fixed;
        }
      }
    } else {
      if (this.Voices[v].PerfWait) this.Voices[v].PerfWait--;
      else this.Voices[v].PeriodPerfSlideSpeed = 0;
    }

    //PerfPortamento
    if (this.Voices[v].PeriodPerfSlideOn) {
      this.Voices[v].PeriodPerfSlidePeriod -=
        this.Voices[v].PeriodPerfSlideSpeed;
      if (this.Voices[v].PeriodPerfSlidePeriod) this.Voices[v].PlantPeriod = 1;
    }

    if (this.Voices[v].Waveform == 2 && this.Voices[v].SquareOn) {
      // 3-1 = 2
      if (--this.Voices[v].SquareWait <= 0) {
        let d1 = this.Voices[v].SquareLowerLimit;
        let d2 = this.Voices[v].SquareUpperLimit;
        let d3 = this.Voices[v].SquarePos;
        if (this.Voices[v].SquareInit) {
          this.Voices[v].SquareInit = 0;
          if (d3 <= d1) {
            this.Voices[v].SquareSlidingIn = 1;
            this.Voices[v].SquareSign = 1;
          } else if (d3 >= d2) {
            this.Voices[v].SquareSlidingIn = 1;
            this.Voices[v].SquareSign = -1;
          }
        }
        if (d1 == d3 || d2 == d3) {
          if (this.Voices[v].SquareSlidingIn) {
            this.Voices[v].SquareSlidingIn = 0;
          } else {
            this.Voices[v].SquareSign = -this.Voices[v].SquareSign;
          }
        }
        d3 += this.Voices[v].SquareSign;
        this.Voices[v].SquarePos = d3;
        this.Voices[v].PlantSquare = 1;
        this.Voices[v].SquareWait = this.Voices[v].Instrument.SquareSpeed;
      }
    }

    if (this.Voices[v].FilterOn && --this.Voices[v].FilterWait <= 0) {
      let d1 = this.Voices[v].FilterLowerLimit;
      let d2 = this.Voices[v].FilterUpperLimit;
      let d3 = this.Voices[v].FilterPos;
      if (this.Voices[v].FilterInit) {
        this.Voices[v].FilterInit = 0;
        if (d3 <= d1) {
          this.Voices[v].FilterSlidingIn = 1;
          this.Voices[v].FilterSign = 1;
        } else if (d3 >= d2) {
          this.Voices[v].FilterSlidingIn = 1;
          this.Voices[v].FilterSign = -1;
        }
      }
      let FMax =
        this.Voices[v].FilterSpeed < 3 ? 5 - this.Voices[v].FilterSpeed : 1;
      for (let i = 0; i < FMax; i++) {
        if (d1 == d3 || d2 == d3) {
          if (this.Voices[v].FilterSlidingIn) {
            this.Voices[v].FilterSlidingIn = 0;
          } else {
            this.Voices[v].FilterSign = -this.Voices[v].FilterSign;
          }
        }
        d3 += this.Voices[v].FilterSign;
      }
      this.Voices[v].FilterPos = d3;
      this.Voices[v].NewWaveform = 1;
      this.Voices[v].FilterWait = this.Voices[v].FilterSpeed - 3;
      if (this.Voices[v].FilterWait < 1) this.Voices[v].FilterWait = 1;
    }

    if (this.Voices[v].Waveform == 2 || this.Voices[v].PlantSquare) {
      let SquarePtr =
        this.Waves.FilterSets[toSixtyTwo(this.Voices[v].FilterPos - 1)].Squares;
      let SquareOfs = 0;
      let X = this.Voices[v].SquarePos << (5 - this.Voices[v].WaveLength);
      if (X > 0x20) {
        X = 0x40 - X;
        this.Voices[v].SquareReverse = 1;
      }
      if (X--) SquareOfs = X * 0x80;
      let Delta = 32 >> this.Voices[v].WaveLength;
      let AudioLen = (1 << this.Voices[v].WaveLength) * 4;
      this.Voices[v].AudioSource = [];
      for (let i = 0; i < AudioLen; i++) {
        this.Voices[v].AudioSource[i] = SquarePtr[SquareOfs];
        SquareOfs += Delta;
      }
      this.Voices[v].NewWaveform = 1;
      this.Voices[v].Waveform = 2;
      this.Voices[v].PlantSquare = 0;
    }

    if (this.Voices[v].Waveform == 3) this.Voices[v].NewWaveform = 1; // White Noise

    if (this.Voices[v].NewWaveform) {
      if (this.Voices[v].Waveform != 2) {
        let FilterSet = toSixtyTwo(this.Voices[v].FilterPos - 1);
        if (this.Voices[v].Waveform == 3) {
          let WNStart = this.WNRandom & (2 * 0x280 - 1) & ~1;
          this.Voices[v].AudioSource = this.Waves.FilterSets[
            FilterSet
          ].WhiteNoiseBig.slice(WNStart, WNStart + 0x280);
          this.WNRandom += 2239384;
          this.WNRandom =
            ((((this.WNRandom >> 8) | (this.WNRandom << 24)) + 782323) ^ 75) -
            6735;
        } else if (this.Voices[v].Waveform == 0) {
          // Triangle
          const map = [
            this.Waves.FilterSets[FilterSet].Triangle04,
            this.Waves.FilterSets[FilterSet].Triangle08,
            this.Waves.FilterSets[FilterSet].Triangle10,
            this.Waves.FilterSets[FilterSet].Triangle20,
            this.Waves.FilterSets[FilterSet].Triangle40,
            this.Waves.FilterSets[FilterSet].Triangle80,
          ];
          this.Voices[v].AudioSource = map[this.Voices[v].WaveLength]
            ? map[this.Voices[v].WaveLength].slice()
            : [];
        } else if (this.Voices[v].Waveform == 1) {
          // Sawtooth
          const map = [
            this.Waves.FilterSets[FilterSet].Sawtooth04,
            this.Waves.FilterSets[FilterSet].Sawtooth08,
            this.Waves.FilterSets[FilterSet].Sawtooth10,
            this.Waves.FilterSets[FilterSet].Sawtooth20,
            this.Waves.FilterSets[FilterSet].Sawtooth40,
            this.Waves.FilterSets[FilterSet].Sawtooth80,
          ];
          this.Voices[v].AudioSource = map[this.Voices[v].WaveLength]
            ? map[this.Voices[v].WaveLength].slice()
            : [];
        }
      }
    }

    this.Voices[v].AudioPeriod = this.Voices[v].InstrPeriod;
    if (!this.Voices[v].FixedNote)
      this.Voices[v].AudioPeriod +=
        this.Voices[v].Transpose + this.Voices[v].TrackPeriod - 1;
    if (this.Voices[v].AudioPeriod > 5 * 12)
      this.Voices[v].AudioPeriod = 5 * 12;
    if (this.Voices[v].AudioPeriod < 0) this.Voices[v].AudioPeriod = 0;
    this.Voices[v].AudioPeriod = this.PeriodTable[this.Voices[v].AudioPeriod];
    if (!this.Voices[v].FixedNote)
      this.Voices[v].AudioPeriod += this.Voices[v].PeriodSlidePeriod;
    this.Voices[v].AudioPeriod +=
      this.Voices[v].PeriodPerfSlidePeriod + this.Voices[v].VibratoPeriod;
    if (this.Voices[v].AudioPeriod > 0x0d60)
      this.Voices[v].AudioPeriod = 0x0d60;
    if (this.Voices[v].AudioPeriod < 0x0071)
      this.Voices[v].AudioPeriod = 0x0071;

    this.Voices[v].AudioVolume =
      ((((((((this.Voices[v].ADSRVolume >> 8) * this.Voices[v].NoteMaxVolume) >>
        6) *
        this.Voices[v].PerfSubVolume) >>
        6) *
        this.Voices[v].TrackMasterVolume) >>
        6) *
        this.MainVolume) >>
      6;
  }

  SetAudio(v) {
    if (!this.Voices[v].TrackOn) {
      this.Voices[v].VoiceVolume = 0;
      return;
    }

    this.Voices[v].VoiceVolume = this.Voices[v].AudioVolume;
    if (this.Voices[v].PlantPeriod) {
      this.Voices[v].PlantPeriod = 0;
      this.Voices[v].VoicePeriod = this.Voices[v].AudioPeriod;
    }
    if (this.Voices[v].NewWaveform) {
      if (this.Voices[v].Waveform == 3) {
        this.Voices[v].VoiceBuffer = this.Voices[v].AudioSource.slice();
      } else {
        let WaveLoops = (1 << (5 - this.Voices[v].WaveLength)) * 5;
        let LoopLen = 4 * (1 << this.Voices[v].WaveLength);
        if (!this.Voices[v].AudioSource.length) {
          this.Voices[v].VoiceBuffer = new Array(WaveLoops * LoopLen).fill(0);
        } else {
          this.Voices[v].VoiceBuffer = [];
          for (let i = 0; i < WaveLoops; i++) {
            this.Voices[v].VoiceBuffer = this.Voices[v].VoiceBuffer.concat(
              this.Voices[v].AudioSource.slice(0, LoopLen),
            );
          }
        }
      }
      this.Voices[v].VoiceBuffer[0x280] = this.Voices[v].VoiceBuffer[0];
    }
  }

  PListCommandParse(v, FX, FXParam) {
    switch (FX) {
      case 0:
        if (this.Song.Revision > 0 && FXParam != 0) {
          if (this.Voices[v].IgnoreFilter) {
            this.Voices[v].FilterPos = this.Voices[v].IgnoreFilter;
            this.Voices[v].IgnoreFilter = 0;
          } else this.Voices[v].FilterPos = FXParam;
          this.Voices[v].NewWaveform = 1;
        }
        break;
      case 1:
        this.Voices[v].PeriodPerfSlideSpeed = FXParam;
        this.Voices[v].PeriodPerfSlideOn = 1;
        break;
      case 2:
        this.Voices[v].PeriodPerfSlideSpeed = -FXParam;
        this.Voices[v].PeriodPerfSlideOn = 1;
        break;
      case 3:
        if (!this.Voices[v].IgnoreSquare) {
          this.Voices[v].SquarePos = FXParam >> (5 - this.Voices[v].WaveLength);
        } else this.Voices[v].IgnoreSquare = 0;
        break;
      case 4:
        if (this.Song.Revision == 0 || FXParam == 0) {
          this.Voices[v].SquareInit = this.Voices[v].SquareOn ^= 1;
          this.Voices[v].SquareSign = 1;
        } else {
          if (FXParam & 0x0f) {
            this.Voices[v].SquareInit = this.Voices[v].SquareOn ^= 1;
            this.Voices[v].SquareSign = 1;
            if ((FXParam & 0x0f) == 0x0f) this.Voices[v].SquareSign = -1;
          }
          if (FXParam & 0xf0) {
            this.Voices[v].FilterInit = this.Voices[v].FilterOn ^= 1;
            this.Voices[v].FilterSign = 1;
            if ((FXParam & 0xf0) == 0xf0) this.Voices[v].FilterSign = -1;
          }
        }
        break;
      case 5:
        this.Voices[v].PerfCurrent = FXParam;
        break;
      case 6:
        if (FXParam > 0x40) {
          if ((FXParam -= 0x50) >= 0) {
            if (FXParam <= 0x40) this.Voices[v].PerfSubVolume = FXParam;
            else if ((FXParam -= 0xa0 - 0x50) >= 0)
              if (FXParam <= 0x40) this.Voices[v].TrackMasterVolume = FXParam;
          }
        } else this.Voices[v].NoteMaxVolume = FXParam;
        break;
      case 7:
        this.Voices[v].PerfSpeed = this.Voices[v].PerfWait = FXParam;
        break;
    }
  }
}

class AHXOutput {
  constructor(player) {
    this.Player = player;
    this.pos = [0, 0, 0, 0];
    this.MixingBuffer = [];
    this.BufferSize = 0;
    this.Frequency = 44100;
  }

  Init(Frequency) {
    this.Frequency = Frequency;
    this.BufferSize = Math.floor(Frequency / 50);
    this.MixingBuffer = new Array(this.BufferSize).fill(0);
  }

  MixChunk(NrSamples, mb) {
    for (let v = 0; v < 4; v++) {
      if (this.Player.Voices[v].VoiceVolume == 0) continue;
      const freq = 3579545.25 / this.Player.Voices[v].VoicePeriod;
      const delta = Math.floor((freq * (1 << 16)) / this.Frequency);
      let samples_to_mix = NrSamples;
      let mixpos = 0;
      while (samples_to_mix) {
        if (this.pos[v] >= 0x280 << 16) this.pos[v] -= 0x280 << 16;
        const thiscount = Math.min(
          samples_to_mix,
          Math.floor(((0x280 << 16) - this.pos[v] - 1) / delta) + 1,
        );
        samples_to_mix -= thiscount;

        if (useOversampling) {
          for (let i = 0; i < thiscount; i++) {
            const offset = this.pos[v] >>> 16;
            const frac1 = this.pos[v] & 0xffff;
            const frac2 = 0x10000 - frac1;

            const s1 = this.Player.Voices[v].VoiceBuffer[offset] | 0;
            const s2 = this.Player.Voices[v].VoiceBuffer[offset + 1] | 0;

            const smp = (s1 * frac2 + s2 * frac1) >> 16;
            this.MixingBuffer[mb + mixpos++] +=
              (smp * this.Player.Voices[v].VoiceVolume) >> 6;
            this.pos[v] += delta;
          }
        } else {
          for (let i = 0; i < thiscount; i++) {
            this.MixingBuffer[mb + mixpos++] +=
              (this.Player.Voices[v].VoiceBuffer[this.pos[v] >> 16] *
                this.Player.Voices[v].VoiceVolume) >>
              6;
            this.pos[v] += delta;
          }
        }
      }
    }
    mb += NrSamples;
    return mb;
  }

  MixBuffer() {
    this.MixingBuffer.fill(0);
    let mb = 0;
    const NrSamples = Math.floor(
      this.BufferSize / this.Player.Song.SpeedMultiplier,
    );
    for (let f = 0; f < this.Player.Song.SpeedMultiplier; f++) {
      this.Player.PlayIRQ();
      mb = this.MixChunk(NrSamples, mb);
    }
  }
}

class AHXMasterBase {
  constructor() {
    this.Output = new AHXOutput(new AHXPlayer());
    this.AudioContext = null;
    this.AudioNode = null;
    this.bufferSize = 8192;
    this.bufferFull = 0;
    this.bufferOffset = 0;
  }

  Play(song) {
    this.Output.Player.InitSong(song);
    this.Output.Player.InitSubsong(0);

    // Initialisierung des AudioContext erst bei Play-Aufruf
    if (!this.AudioContext) {
      const AudioCtxClass = window.AudioContext || window.webkitAudioContext;
      this.AudioContext = new AudioCtxClass();
    }

    // Sicherstellen, dass der Context läuft (Browser Autoplay Policy)
    if (this.AudioContext.state === 'suspended') {
      this.AudioContext.resume();
    }

    this.Output.Init(this.AudioContext.sampleRate);

    this.bufferFull = 0;
    this.bufferOffset = 0;

    if (this.AudioNode) this.AudioNode.disconnect();

    // ScriptProcessor ist deprecated, aber für diesen Port die einfachste Lösung
    // ohne kompletten Rewrite auf AudioWorklet
    this.AudioNode = this.AudioContext.createScriptProcessor(
      this.bufferSize,
      0,
      2,
    );

    const self = this;
    this.AudioNode.onaudioprocess = function (e) {
      self.mixer(e);
    };

    this.AudioNode.connect(this.AudioContext.destination);
  }

  Stop() {
    if (this.AudioNode) {
      this.AudioNode.disconnect();
      this.AudioNode = null;
    }
    if (this.AudioContext) {
      this.AudioContext.suspend();
    }
  }

  mixer(e) {
    let want = this.bufferSize;
    const buffer = e.outputBuffer;
    const left = buffer.getChannelData(0);
    const right = buffer.getChannelData(1);
    let out = 0;

    while (want > 0) {
      if (this.bufferFull == 0) {
        this.Output.MixBuffer();
        this.bufferFull = this.Output.BufferSize;
        this.bufferOffset = 0;
      }

      let can = Math.min(this.bufferFull - this.bufferOffset, want);
      want -= can;
      while (can-- > 0) {
        // Simple Stereo-Expansion/Volume Normalization
        const thissample =
          this.Output.MixingBuffer[this.bufferOffset++] / (128 * 4);
        left[out] = right[out] = thissample;
        out++;
      }
      if (this.bufferOffset >= this.bufferFull) {
        this.bufferOffset = this.bufferFull = 0;
      }
    }
  }
}

// --- Exports ---

export { AHXMasterBase as AHXMaster, AHXSong };
