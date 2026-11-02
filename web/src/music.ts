// Cozy lo-fi music, made on the fly with Web Audio (no audio files). Six original tracks:
// soft electric-piano 7th/9th chords, a kalimba melody, round bass, swung brushy drums,
// vinyl crackle and a warm low-pass. Each track plays ~2.5 min, then crossfades into the next.
// Looks and sounds only: nothing here touches the game.

type Chord = { root: number; tones: number[] }; // root as semitones above the key; tones relative to root

interface Track {
  name: string;
  bpm: number;
  key: number;          // MIDI note of the key's tonic (bass octave)
  chords: Chord[];      // one chord per bar, looped
  seed: number;         // melody and fills
  feel: { swing: number; kick: number[]; snare: number[]; hats: number; melody: number; bright: number };
}

// chord shapes (semitones above the chord root)
const MAJ9 = [0, 4, 7, 11, 14], MIN9 = [0, 3, 7, 10, 14], DOM9 = [0, 4, 7, 10, 14], MIN7 = [0, 3, 7, 10], MAJ7 = [0, 4, 7, 11], SUS = [0, 5, 7, 10, 14], M6 = [0, 4, 7, 9, 14];
const c = (root: number, tones: number[]): Chord => ({ root, tones });

export const TRACKS: Track[] = [
  { name: "Morning Commute", bpm: 84, key: 41, seed: 11, chords: [c(0, MAJ9), c(9, MIN9), c(2, MIN7), c(7, DOM9)],
    feel: { swing: 0.16, kick: [0, 7, 10], snare: [4, 12], hats: 1, melody: 0.55, bright: 1 } },
  { name: "Bridge Over Brook", bpm: 76, key: 43, seed: 23, chords: [c(5, MAJ7), c(4, MIN7), c(2, MIN9), c(0, M6)],
    feel: { swing: 0.2, kick: [0, 9], snare: [4, 12], hats: 0.7, melody: 0.45, bright: 0.85 } },
  { name: "Café Terrace", bpm: 88, key: 38, seed: 37, chords: [c(2, MIN9), c(7, DOM9), c(0, MAJ9), c(9, MIN7)],
    feel: { swing: 0.12, kick: [0, 6, 8], snare: [4, 12], hats: 1, melody: 0.6, bright: 1.1 } },
  { name: "Rainy Rooftops", bpm: 72, key: 45, seed: 41, chords: [c(0, MIN9), c(5, MIN7), c(10, MAJ9), c(3, MAJ7)],
    feel: { swing: 0.22, kick: [0, 10], snare: [4, 12], hats: 0.5, melody: 0.4, bright: 0.75 } },
  { name: "Park Bench Nap", bpm: 70, key: 40, seed: 53, chords: [c(0, MAJ7), c(0, SUS), c(5, MAJ9), c(7, SUS)],
    feel: { swing: 0.18, kick: [0, 11], snare: [12], hats: 0.45, melody: 0.35, bright: 0.8 } },
  { name: "Lanterns at Dusk", bpm: 80, key: 42, seed: 67, chords: [c(9, MIN9), c(5, MAJ9), c(0, MAJ7), c(7, DOM9)],
    feel: { swing: 0.17, kick: [0, 7, 9], snare: [4, 12], hats: 0.85, melody: 0.5, bright: 0.95 } },
];

const TRACK_SECONDS = 150;
const midiHz = (m: number) => 440 * Math.pow(2, (m - 69) / 12);

function rng(seed: number) {
  let a = seed >>> 0;
  return () => { a = (a + 0x6d2b79f5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
}

/** A 2-bar melody per chord pair: notes from the chord's pentatonic, rests, gentle steps. */
function composeMelody(t: Track): (number | null)[][] {
  const r = rng(t.seed);
  const bars: (number | null)[][] = [];
  let last = 7;
  // two phrases (A and B) of 8 bars, each bar 8 eighth-notes
  for (let b = 0; b < 16; b++) {
    const ch = t.chords[b % t.chords.length];
    const scale = [0, 2, 4, 7, 9].map((x) => x + (ch.tones[1] === 3 ? (x === 4 ? -1 : x === 9 ? 1 : 0) : 0));
    const bar: (number | null)[] = [];
    for (let s = 0; s < 8; s++) {
      const rest = r() > t.feel.melody * (s % 2 === 0 ? 1.2 : 0.7) || (b % 4 === 3 && s > 4);
      if (rest) { bar.push(null); continue; }
      // small steps mostly, an occasional leap
      const step = r() < 0.75 ? Math.round((r() - 0.5) * 3) : Math.round((r() - 0.5) * 8);
      last = Math.max(0, Math.min(scale.length * 2 - 1, last + step));
      const oct = Math.floor(last / scale.length), deg = last % scale.length;
      bar.push(ch.root + scale[deg] + 12 * oct);
    }
    bars.push(bar);
  }
  return bars;
}

const RATE = 22050;
const LOOP_BARS = 32;

/** Renders one track into a seamless, loopable mono buffer (offline, so frame hitches can't touch it). */
async function renderTrack(t: Track): Promise<AudioBuffer> {
  const bar = (60 / t.bpm) * 4, loop = bar * LOOP_BARS, tail = 4;
  const ctx = new OfflineAudioContext(1, Math.ceil((loop + tail) * RATE), RATE);
  const warm = ctx.createBiquadFilter();
  warm.type = "lowpass"; warm.frequency.value = 2600 + 1100 * t.feel.bright; warm.Q.value = 0.4;
  const comp = ctx.createDynamicsCompressor();
  comp.threshold.value = -18; comp.ratio.value = 3; comp.attack.value = 0.02; comp.release.value = 0.3;
  warm.connect(comp).connect(ctx.destination);
  const noise = ctx.createBuffer(1, RATE, RATE), nd = noise.getChannelData(0);
  const r = rng(t.seed * 977 + 5);
  for (let i = 0; i < nd.length; i++) nd[i] = r() * 2 - 1;
  const ins = new Instruments(ctx, warm, noise, r);
  const melody = composeMelody(t);
  const s16 = 60 / t.bpm / 4;
  for (let step = 0; step < LOOP_BARS * 16; step++) {
    const inBar = step % 16, b = Math.floor(step / 16);
    const when = step * s16 + (inBar % 2 === 1 ? s16 * t.feel.swing : 0) + 0.002;
    playStep(ins, t, melody, b, inBar, when, s16, r);
  }
  const out = await ctx.startRendering();
  // fold the tail (notes ringing past the loop end) back onto the start: a seamless loop
  const d = out.getChannelData(0), n = Math.floor(loop * RATE);
  for (let i = n; i < d.length; i++) d[i - n] += d[i];
  const buf = new AudioBuffer({ numberOfChannels: 1, length: n, sampleRate: RATE });
  buf.copyToChannel(d.subarray(0, n), 0);
  return buf;
}

function playStep(ins: Instruments, t: Track, melody: (number | null)[][], bar: number, s: number, when: number, s16: number, r: () => number) {
  const ch = t.chords[bar % t.chords.length];
  const root = t.key + ch.root;
  const breakdown = bar % 16 >= 12 && bar % 16 < 14; // every 16 bars the drums rest for two bars
  if (s === 0) ins.rhodes(ch.tones.map((x) => root + 24 + x), when, s16 * 15, 0.11);
  if (s === 10 && bar % 2 === 1) ins.rhodes(ch.tones.slice(1).map((x) => root + 24 + x), when, s16 * 6, 0.06);
  if (s === 0) ins.bass(root, when, s16 * 7);
  if (s === 10) ins.bass(root + (bar % 2 ? 7 : 12), when, s16 * 4);
  if (s % 2 === 0) {
    const nt = melody[bar % melody.length][s / 2];
    if (nt !== null && nt !== undefined) ins.kalimba(t.key + 36 + nt, when);
  }
  if (breakdown) return;
  if (t.feel.kick.includes(s)) ins.kick(when);
  if (t.feel.snare.includes(s)) ins.snare(when);
  if (s % 2 === 0 && r() < t.feel.hats) ins.hat(when, s % 4 === 0 ? 0.05 : 0.03);
}

/** The instruments, each note with a short attack and release (no pops). */
class Instruments {
  constructor(private ctx: BaseAudioContext, private out: AudioNode, private noise: AudioBuffer, private r: () => number) {}

  rhodes(notes: number[], when: number, dur: number, vol: number) {
    const ctx = this.ctx;
    const g = ctx.createGain();
    const peak = vol / Math.sqrt(notes.length) * notes.length * 0.55;
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(peak, when + 0.015);
    g.gain.setTargetAtTime(peak * 0.35, when + 0.05, dur * 0.4);
    g.gain.setTargetAtTime(0, when + dur, 0.25);
    const lfo = ctx.createOscillator(), lg = ctx.createGain();
    lfo.frequency.value = 4.2; lg.gain.value = 0.12 * peak;
    lfo.connect(lg).connect(g.gain);
    g.connect(this.out);
    const end = when + dur + 1.6;
    for (const [k, m] of notes.entries()) {
      const f = midiHz(m);
      const o1 = this.ctx.createOscillator(), o2 = this.ctx.createOscillator(), g1 = ctx.createGain(), g2 = ctx.createGain();
      o1.frequency.value = f; o2.frequency.value = f * 2; o2.detune.value = 4;
      g1.gain.value = 1 / notes.length; g2.gain.value = 0.18 / notes.length;
      o1.connect(g1).connect(g); o2.connect(g2).connect(g);
      o1.start(when + k * 0.012); o2.start(when + k * 0.012); o1.stop(end); o2.stop(end);
    }
    lfo.start(when); lfo.stop(end);
  }

  kalimba(m: number, when: number) {
    const ctx = this.ctx, f = midiHz(m);
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(0.07, when + 0.006);
    g.gain.setTargetAtTime(0, when + 0.01, 0.22);
    const o = ctx.createOscillator(); o.type = "triangle"; o.frequency.value = f;
    const o2 = ctx.createOscillator(); o2.frequency.value = f * 4.02;
    const g2 = ctx.createGain(); g2.gain.setValueAtTime(0, when); g2.gain.linearRampToValueAtTime(0.25, when + 0.004); g2.gain.setTargetAtTime(0, when + 0.006, 0.035);
    o.connect(g); o2.connect(g2).connect(g); g.connect(this.out);
    o.start(when); o2.start(when); o.stop(when + 1.6); o2.stop(when + 0.4);
  }

  bass(m: number, when: number, dur: number) {
    const ctx = this.ctx;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(0.22, when + 0.02);
    g.gain.setTargetAtTime(0, when + dur * 0.7, 0.08);
    const o = ctx.createOscillator(); o.type = "triangle"; o.frequency.value = midiHz(m);
    const lp = ctx.createBiquadFilter(); lp.type = "lowpass"; lp.frequency.value = 420;
    o.connect(lp).connect(g).connect(this.out);
    o.start(when); o.stop(when + dur + 0.8);
  }

  kick(when: number) {
    const ctx = this.ctx, o = ctx.createOscillator(), g = ctx.createGain();
    o.frequency.setValueAtTime(110, when); o.frequency.exponentialRampToValueAtTime(42, when + 0.12);
    g.gain.setValueAtTime(0, when); g.gain.linearRampToValueAtTime(0.32, when + 0.003); g.gain.setTargetAtTime(0, when + 0.01, 0.06);
    o.connect(g).connect(this.out);
    o.start(when); o.stop(when + 0.45);
  }

  private noiseHit(when: number, type: BiquadFilterType, freq: number, q: number, vol: number, len: number) {
    const ctx = this.ctx, src = ctx.createBufferSource(); src.buffer = this.noise;
    const f = ctx.createBiquadFilter(); f.type = type; f.frequency.value = freq; f.Q.value = q;
    const g = ctx.createGain(); g.gain.setValueAtTime(0, when); g.gain.linearRampToValueAtTime(vol, when + 0.003); g.gain.setTargetAtTime(0, when + 0.005, len / 4);
    src.connect(f).connect(g).connect(this.out);
    src.start(when, this.r() * 0.5); src.stop(when + len + 0.15);
  }
  snare(when: number) { this.noiseHit(when, "bandpass", 1900, 0.7, 0.09, 0.22); }
  hat(when: number, vol: number) { this.noiseHit(when, "highpass", 7200, 0.5, vol, 0.05); }
}

/**
 * The player. Each track is rendered once into a looping buffer (current first, the next one
 * in the background); playback is a single looping source per track, so busy frames can't make
 * it stutter. Tracks change with a crossfade; pausing fades out.
 */
export class Music {
  private ctx: AudioContext | null = null;
  private master!: GainNode;
  private buffers = new Map<number, Promise<AudioBuffer>>();
  private current: { src: AudioBufferSourceNode; gain: GainNode } | null = null;
  private advance = 0;
  private index = 0;
  playing = false;
  volume = Number(localStorage.getItem("sb-music-vol") ?? "0.6");
  /** The player turned the music off (remembered). */
  muted = localStorage.getItem("sb-music-on") === "0";
  onChange: () => void = () => {};

  get track(): Track { return TRACKS[this.index]; }

  private ensure() {
    if (this.ctx) return;
    const ctx = new AudioContext();
    this.ctx = ctx;
    this.master = ctx.createGain();
    this.master.gain.value = 0;
    this.master.connect(ctx.destination);
    // vinyl crackle: sparse clicks over a faint hiss, looped (cheap, shared by all tracks)
    const cr = ctx.createBuffer(1, RATE * 4, RATE), cd = cr.getChannelData(0);
    for (let i = 0; i < cd.length; i++) cd[i] = (Math.random() * 2 - 1) * 0.01 + (Math.random() < 0.0012 ? (Math.random() - 0.5) * 0.7 : 0);
    const src = ctx.createBufferSource(); src.buffer = cr; src.loop = true;
    const hp = ctx.createBiquadFilter(); hp.type = "highpass"; hp.frequency.value = 900;
    const lp = ctx.createBiquadFilter(); lp.type = "lowpass"; lp.frequency.value = 5000;
    const g = ctx.createGain(); g.gain.value = 0.2;
    src.connect(hp).connect(lp).connect(g).connect(this.master);
    src.start();
  }

  private buffer(i: number): Promise<AudioBuffer> {
    let b = this.buffers.get(i);
    if (!b) { b = renderTrack(TRACKS[i]); this.buffers.set(i, b); }
    // keep memory low: only the current track and its neighbours stay rendered
    for (const k of [...this.buffers.keys()]) {
      const d = Math.min((k - i + TRACKS.length) % TRACKS.length, (i - k + TRACKS.length) % TRACKS.length);
      if (d >= 2) this.buffers.delete(k);
    }
    return b;
  }

  /** Start (or resume). The first call must come from a click or key (browser autoplay rules). */
  play() {
    this.ensure();
    const ctx = this.ctx!;
    void ctx.resume();
    this.muted = false;
    localStorage.setItem("sb-music-on", "1");
    if (!this.playing) {
      this.playing = true;
      const now = ctx.currentTime;
      this.master.gain.cancelScheduledValues(now);
      this.master.gain.setValueAtTime(this.master.gain.value, now);
      this.master.gain.linearRampToValueAtTime(this.volume * 0.5, now + 0.8);
      if (!this.current) void this.startTrack(this.index, 0.6);
      this.onChange();
    }
  }

  pause() {
    if (!this.ctx || !this.playing) return;
    this.playing = false;
    this.muted = true;
    localStorage.setItem("sb-music-on", "0");
    const now = this.ctx.currentTime, ctx = this.ctx;
    this.master.gain.cancelScheduledValues(now);
    this.master.gain.setValueAtTime(this.master.gain.value, now);
    this.master.gain.linearRampToValueAtTime(0, now + 0.6);
    setTimeout(() => { if (!this.playing) void ctx.suspend(); }, 800);
    this.onChange();
  }

  toggle() { if (this.playing) this.pause(); else this.play(); }

  setVolume(v: number) {
    this.volume = Math.max(0, Math.min(1, v));
    localStorage.setItem("sb-music-vol", String(this.volume));
    if (this.ctx && this.playing) this.master.gain.setTargetAtTime(this.volume * 0.5, this.ctx.currentTime, 0.08);
  }

  /** Crossfade into the next track (in order; the playlist loops). */
  next() {
    const i = (this.index + 1) % TRACKS.length;
    if (!this.ctx) { this.index = i; this.onChange(); return; }
    void this.startTrack(i, 3);
  }

  private async startTrack(i: number, fade: number) {
    this.index = i;
    this.onChange();
    clearTimeout(this.advance);
    const buf = await this.buffer(i);
    if (this.index !== i || !this.ctx) return; // skipped again while rendering
    const ctx = this.ctx, now = ctx.currentTime;
    if (this.current) {
      const old = this.current;
      old.gain.gain.cancelScheduledValues(now);
      old.gain.gain.setValueAtTime(old.gain.gain.value, now);
      old.gain.gain.linearRampToValueAtTime(0, now + fade);
      old.src.stop(now + fade + 0.05);
    }
    const gain = ctx.createGain();
    gain.gain.setValueAtTime(0, now);
    gain.gain.linearRampToValueAtTime(1, now + fade);
    const src = ctx.createBufferSource();
    src.buffer = buf; src.loop = true;
    src.connect(gain).connect(this.master);
    src.start(now);
    this.current = { src, gain };
    // after ~2.5 minutes, move on; meanwhile render the next track in the background
    this.advance = window.setTimeout(() => { if (this.playing) this.next(); }, TRACK_SECONDS * 1000);
    setTimeout(() => void this.buffer((i + 1) % TRACKS.length), 1500);
  }
}

/** The music pill in the HUD: ♪ track name, play/pause, next, volume. Starts on the first click. */
export function musicPill(host: HTMLElement, music: Music) {
  const el = document.createElement("div");
  el.id = "music";
  el.className = "music";
  host.appendChild(el);
  const icon = (play: boolean) => play
    ? `<svg viewBox="0 0 24 24"><path d="M8 5.5v13l10-6.5z" fill="currentColor"/></svg>`
    : `<svg viewBox="0 0 24 24"><rect x="7" y="5.5" width="3.6" height="13" rx="1.2" fill="currentColor"/><rect x="13.4" y="5.5" width="3.6" height="13" rx="1.2" fill="currentColor"/></svg>`;
  el.innerHTML = `<span class="mu-note" aria-hidden="true"><svg viewBox="0 0 24 24"><path d="M9 17.5V6l10-2v11.5" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/><circle cx="6.5" cy="17.5" r="2.5" fill="currentColor"/><circle cx="16.5" cy="15.5" r="2.5" fill="currentColor"/></svg></span>
    <span class="mu-name"></span>
    <button class="mu-btn" data-mu="toggle" title="Play or pause the music"></button>
    <button class="mu-btn" data-mu="next" title="Next song"><svg viewBox="0 0 24 24"><path d="M6 6v12l8-6zM15 6h3v12h-3z" fill="currentColor"/></svg></button>
    <input class="mu-vol" type="range" min="0" max="1" step="0.01" title="Music volume" aria-label="Music volume"/>`;
  const name = el.querySelector<HTMLElement>(".mu-name")!, toggle = el.querySelector<HTMLButtonElement>("[data-mu='toggle']")!;
  const vol = el.querySelector<HTMLInputElement>(".mu-vol")!;
  vol.value = String(music.volume);
  const render = () => {
    name.textContent = music.track.name;
    name.title = music.track.name;
    toggle.innerHTML = icon(!music.playing);
    el.classList.toggle("on", music.playing);
    el.dataset.state = music.playing ? "on" : music.muted ? "off" : "ready";
  };
  music.onChange = render;
  render();
  el.addEventListener("click", (e) => {
    const b = (e.target as HTMLElement).closest<HTMLElement>("[data-mu]");
    if (!b) return;
    e.stopPropagation();
    if (b.dataset.mu === "toggle") music.toggle();
    else music.next();
  });
  const paintVol = () => vol.style.setProperty("--v", `${Math.round(Number(vol.value) * 100)}%`);
  paintVol();
  vol.addEventListener("input", () => { music.setVolume(Number(vol.value)); paintVol(); });
  // autoplay rules: the music starts with the first click anywhere (unless the player turned it off)
  const first = () => { if (!music.muted && !music.playing) music.play(); };
  window.addEventListener("pointerdown", first, { once: true, capture: true });
  window.addEventListener("keydown", first, { once: true, capture: true });
  // also try right away (works where autoplay is allowed)
  if (!music.muted) try { music.play(); } catch { /* blocked until a click */ }
  return el;
}
