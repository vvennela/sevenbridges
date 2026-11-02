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

export class Music {
  private ctx: AudioContext | null = null;
  private master!: GainNode;
  private warm!: BiquadFilterNode;
  private bus: GainNode | null = null;
  private noise!: AudioBuffer;
  private crackle: AudioBufferSourceNode | null = null;
  private timer = 0;
  private index = 0;
  private trackStart = 0;
  private nextStep = 0;
  private step = 0;
  private melody: (number | null)[][] = [];
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
    // tape warmth: a gentle low-pass and a soft compressor
    this.warm = ctx.createBiquadFilter();
    this.warm.type = "lowpass"; this.warm.frequency.value = 3400; this.warm.Q.value = 0.4;
    const comp = ctx.createDynamicsCompressor();
    comp.threshold.value = -18; comp.ratio.value = 3; comp.attack.value = 0.02; comp.release.value = 0.3;
    this.master = ctx.createGain();
    this.master.gain.value = 0;
    this.warm.connect(comp).connect(this.master).connect(ctx.destination);
    // shared noise for drums and crackle
    const len = ctx.sampleRate * 2;
    this.noise = ctx.createBuffer(1, len, ctx.sampleRate);
    const d = this.noise.getChannelData(0);
    for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
    // vinyl crackle: sparse clicks over a faint hiss, looped
    const cr = ctx.createBuffer(1, ctx.sampleRate * 4, ctx.sampleRate), cd = cr.getChannelData(0);
    for (let i = 0; i < cd.length; i++) cd[i] = (Math.random() * 2 - 1) * 0.012 + (Math.random() < 0.0009 ? (Math.random() - 0.5) * 0.9 : 0);
    const src = ctx.createBufferSource(); src.buffer = cr; src.loop = true;
    const hp = ctx.createBiquadFilter(); hp.type = "highpass"; hp.frequency.value = 900;
    const g = ctx.createGain(); g.gain.value = 0.22;
    src.connect(hp).connect(g).connect(this.warm);
    src.start();
    this.crackle = src;
  }

  /** Start (or resume) playing. Call from a user gesture the first time (autoplay rules). */
  play() {
    this.ensure();
    const ctx = this.ctx!;
    void ctx.resume();
    if (this.playing) return;
    this.playing = true;
    this.muted = false;
    localStorage.setItem("sb-music-on", "1");
    this.master.gain.cancelScheduledValues(ctx.currentTime);
    this.master.gain.setTargetAtTime(this.volume * 0.5, ctx.currentTime, 0.4);
    if (!this.bus) this.startTrack(this.index, 0.5);
    this.timer = window.setInterval(() => this.schedule(), 50);
    this.onChange();
  }

  pause() {
    if (!this.ctx || !this.playing) return;
    this.playing = false;
    this.muted = true;
    localStorage.setItem("sb-music-on", "0");
    this.master.gain.setTargetAtTime(0, this.ctx.currentTime, 0.25);
    clearInterval(this.timer);
    const ctx = this.ctx;
    setTimeout(() => { if (!this.playing) void ctx.suspend(); }, 1200);
    this.onChange();
  }

  toggle() { if (this.playing) this.pause(); else this.play(); }

  setVolume(v: number) {
    this.volume = Math.max(0, Math.min(1, v));
    localStorage.setItem("sb-music-vol", String(this.volume));
    if (this.ctx && this.playing) this.master.gain.setTargetAtTime(this.volume * 0.5, this.ctx.currentTime, 0.1);
  }

  /** Crossfade into the next track (in order; the playlist loops). */
  next() {
    if (!this.ctx) { this.index = (this.index + 1) % TRACKS.length; this.onChange(); return; }
    this.startTrack((this.index + 1) % TRACKS.length, 3);
    this.onChange();
  }

  private startTrack(i: number, fade: number) {
    const ctx = this.ctx!;
    const now = ctx.currentTime;
    if (this.bus) { const old = this.bus; old.gain.cancelScheduledValues(now); old.gain.setValueAtTime(old.gain.value, now); old.gain.linearRampToValueAtTime(0, now + fade); setTimeout(() => old.disconnect(), (fade + 2) * 1000); }
    this.index = i;
    const bus = ctx.createGain();
    bus.gain.setValueAtTime(0, now);
    bus.gain.linearRampToValueAtTime(1, now + fade);
    bus.connect(this.warm);
    this.bus = bus;
    this.warm.frequency.setTargetAtTime(2600 + 1100 * this.track.feel.bright, now, 1);
    this.melody = composeMelody(this.track);
    this.trackStart = now + 0.05;
    this.nextStep = now + 0.05;
    this.step = 0;
  }

  /** Lookahead scheduler: queue every 16th note that starts in the next 0.25 s. */
  private schedule() {
    const ctx = this.ctx!;
    const t = this.track, s16 = 60 / t.bpm / 4;
    if (ctx.currentTime - this.trackStart > TRACK_SECONDS) { this.next(); return; }
    while (this.nextStep < ctx.currentTime + 0.25) {
      const step = this.step, inBar = step % 16, bar = Math.floor(step / 16);
      // swing: every second 16th is late
      const when = this.nextStep + (inBar % 2 === 1 ? s16 * t.feel.swing : 0);
      this.playStep(t, bar, inBar, when, s16);
      this.nextStep += s16;
      this.step++;
    }
  }

  private playStep(t: Track, bar: number, s: number, when: number, s16: number) {
    const ch = t.chords[bar % t.chords.length];
    const root = t.key + ch.root;
    const intro = bar < 2;               // a soft start: piano only
    const breakdown = bar % 16 >= 12 && bar % 16 < 14; // every 16 bars: drums drop out
    // electric piano: chord on beat 1, a softer push before beat 3 now and then
    if (s === 0) this.rhodes(ch.tones.map((x) => root + 24 + x), when, s16 * 15, 0.11);
    if (s === 10 && bar % 2 === 1) this.rhodes(ch.tones.slice(1).map((x) => root + 24 + x), when, s16 * 6, 0.06);
    // bass: root on 1, fifth or octave on the "and" of 3
    if (!intro) {
      if (s === 0) this.bass(root, when, s16 * 7);
      if (s === 10) this.bass(root + (bar % 2 ? 7 : 12), when, s16 * 4);
    }
    // kalimba melody on eighth notes (two phrases of 8 bars)
    if (!intro && s % 2 === 0) {
      const n = this.melody[bar % this.melody.length][s / 2];
      if (n !== null && n !== undefined) this.kalimba(t.key + 36 + n, when);
    }
    // drums
    if (intro || breakdown) return;
    if (t.feel.kick.includes(s)) this.kick(when);
    if (t.feel.snare.includes(s)) this.snare(when);
    if (s % 2 === 0 && Math.random() < t.feel.hats) this.hat(when, s % 4 === 0 ? 0.05 : 0.03);
  }

  // ---------- instruments ----------

  private rhodes(notes: number[], when: number, dur: number, vol: number) {
    const ctx = this.ctx!, out = this.bus!;
    for (const [k, m] of notes.entries()) {
      const f = midiHz(m);
      const g = ctx.createGain();
      g.gain.setValueAtTime(0, when);
      g.gain.linearRampToValueAtTime(vol / Math.sqrt(notes.length), when + 0.012 + k * 0.012);
      g.gain.setTargetAtTime(0, when + 0.05, dur * 0.45);
      const o1 = ctx.createOscillator(), o2 = ctx.createOscillator();
      o1.type = "sine"; o1.frequency.value = f;
      o2.type = "sine"; o2.frequency.value = f * 2.0; o2.detune.value = 4;
      const g2 = ctx.createGain(); g2.gain.value = 0.18; // a little bell overtone
      // gentle tremolo
      const lfo = ctx.createOscillator(), lg = ctx.createGain();
      lfo.frequency.value = 4.2; lg.gain.value = 0.15 * vol;
      lfo.connect(lg).connect(g.gain);
      o1.connect(g); o2.connect(g2).connect(g); g.connect(out);
      const end = when + dur + 1.2;
      for (const o of [o1, o2, lfo]) { o.start(when); o.stop(end); }
    }
  }

  private kalimba(m: number, when: number) {
    const ctx = this.ctx!;
    const f = midiHz(m);
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(0.07, when + 0.004);
    g.gain.exponentialRampToValueAtTime(0.0008, when + 0.9);
    const o = ctx.createOscillator(); o.type = "triangle"; o.frequency.value = f;
    const o2 = ctx.createOscillator(); o2.type = "sine"; o2.frequency.value = f * 4.02; // the tine's ping
    const g2 = ctx.createGain(); g2.gain.setValueAtTime(0.25, when); g2.gain.exponentialRampToValueAtTime(0.001, when + 0.15);
    o.connect(g); o2.connect(g2).connect(g); g.connect(this.bus!);
    o.start(when); o2.start(when); o.stop(when + 1); o2.stop(when + 0.2);
  }

  private bass(m: number, when: number, dur: number) {
    const ctx = this.ctx!;
    const g = ctx.createGain();
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(0.22, when + 0.02);
    g.gain.setTargetAtTime(0.0, when + dur * 0.6, dur * 0.25);
    const o = ctx.createOscillator(); o.type = "triangle"; o.frequency.value = midiHz(m);
    const lp = ctx.createBiquadFilter(); lp.type = "lowpass"; lp.frequency.value = 420;
    o.connect(lp).connect(g).connect(this.bus!);
    o.start(when); o.stop(when + dur + 0.6);
  }

  private kick(when: number) {
    const ctx = this.ctx!;
    const o = ctx.createOscillator(), g = ctx.createGain();
    o.frequency.setValueAtTime(110, when); o.frequency.exponentialRampToValueAtTime(42, when + 0.12);
    g.gain.setValueAtTime(0.32, when); g.gain.exponentialRampToValueAtTime(0.001, when + 0.28);
    o.connect(g).connect(this.bus!);
    o.start(when); o.stop(when + 0.3);
  }

  private noiseHit(when: number, type: BiquadFilterType, freq: number, q: number, vol: number, len: number) {
    const ctx = this.ctx!;
    const src = ctx.createBufferSource(); src.buffer = this.noise;
    const f = ctx.createBiquadFilter(); f.type = type; f.frequency.value = freq; f.Q.value = q;
    const g = ctx.createGain(); g.gain.setValueAtTime(vol, when); g.gain.exponentialRampToValueAtTime(0.0005, when + len);
    src.connect(f).connect(g).connect(this.bus!);
    src.start(when, Math.random() * 1.5); src.stop(when + len + 0.02);
  }
  private snare(when: number) { this.noiseHit(when, "bandpass", 1900, 0.7, 0.09, 0.22); } // brushy
  private hat(when: number, vol: number) { this.noiseHit(when, "highpass", 7200, 0.5, vol, 0.045); }

  stopAll() { clearInterval(this.timer); this.crackle?.stop(); void this.ctx?.close(); }
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
  el.innerHTML = `<span class="mu-note" aria-hidden="true">♪</span>
    <span class="mu-name"></span>
    <button class="mu-btn" data-mu="toggle" title="Play or pause the music"></button>
    <button class="mu-btn" data-mu="next" title="Next song"><svg viewBox="0 0 24 24"><path d="M6 6v12l8-6zM15 6h3v12h-3z" fill="currentColor"/></svg></button>
    <input class="mu-vol" type="range" min="0" max="1" step="0.05" title="Music volume" aria-label="Music volume"/>`;
  const name = el.querySelector<HTMLElement>(".mu-name")!, toggle = el.querySelector<HTMLButtonElement>("[data-mu='toggle']")!;
  const vol = el.querySelector<HTMLInputElement>(".mu-vol")!;
  vol.value = String(music.volume);
  const render = () => {
    name.textContent = music.track.name;
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
  vol.addEventListener("input", () => music.setVolume(Number(vol.value)));
  // autoplay rules: the music starts with the first click anywhere (unless the player turned it off)
  const first = () => { if (!music.muted && !music.playing) music.play(); };
  window.addEventListener("pointerdown", first, { once: true, capture: true });
  window.addEventListener("keydown", first, { once: true, capture: true });
  // also try right away (works where autoplay is allowed)
  if (!music.muted) try { music.play(); } catch { /* blocked until a click */ }
  return el;
}
