// The game engine in the browser: the Lean backend compiled to WebAssembly, run
// in Web Workers (engine-worker.ts). Same API as the WebSocket Engine in api.ts.
//
// Towns are ready before the player asks:
// - the starter pack (web/public/pack, made by wasm/make-pack.mjs with the native
//   Lean program): a town not played yet on this device is opened with Lean's
//   `load` command, which checks the stored best plan before accepting it;
// - one town per size made in the background (Lean's `generate`, in its own
//   worker); when the player takes one, the next one of that size is started.
import type { EvalReply, GenerateReply, PuzzleReply, Reply, Solution, SolveReply } from "./types";

type Size = "easy" | "medium" | "hard";
const SIZES: Record<Size, number> = { easy: 5, medium: 7, hard: 8 };
const PLAYED_KEY = "sb-played-seeds";

class LeanWorker {
  private w = new Worker(new URL("./engine-worker.ts", import.meta.url), { type: "module" });
  private next = 0;
  private waiting = new Map<number, (reply: string) => void>();
  constructor() {
    this.w.onmessage = (ev) => { const { id, reply } = ev.data; this.waiting.get(id)?.(reply); this.waiting.delete(id); };
  }
  private post(msg: object): Promise<string> {
    const id = this.next++;
    return new Promise((res) => { this.waiting.set(id, res); this.w.postMessage({ id, ...msg }); });
  }
  ask(line: string) { return this.post({ line }); }
  make(seed: number, blocks: number) { return this.post({ make: { seed, blocks } }); }
  stop() { this.w.terminate(); }
}

interface PackTown { seed: number; puzzle: unknown; best: Solution; bestScore: number; randomMedian?: number }

function played(): Set<number> {
  try { return new Set(JSON.parse(localStorage.getItem(PLAYED_KEY) ?? "[]") as number[]); } catch { return new Set(); }
}
const freshSeed = () => crypto.getRandomValues(new Uint32Array(1))[0] || 1;

function unwrap<T>(line: string): T {
  const r = JSON.parse(line) as Reply<T>;
  if (r.ok) return r.data;
  throw new Error(r.error);
}

export class WasmEngine {
  onStatus: (connected: boolean) => void = () => {};
  private current = new LeanWorker();
  private chain: Promise<unknown> = Promise.resolve();
  private ready: Partial<Record<Size, { w: LeanWorker; reply: Promise<string> }>> = {};
  private packs: Partial<Record<Size, Promise<PackTown[]>>> = {};

  constructor() {
    for (const size of ["medium", "easy", "hard"] as Size[]) this.prepare(size);
    setTimeout(() => this.onStatus(true), 0);
  }

  /** Make one town of this size in the background, in its own worker. */
  private prepare(size: Size) {
    if (this.ready[size]) return;
    const w = new LeanWorker();
    this.ready[size] = { w, reply: w.make(freshSeed(), SIZES[size]) };
  }

  private pack(size: Size): Promise<PackTown[]> {
    return (this.packs[size] ??= fetch(`${import.meta.env.BASE_URL}pack/${size}.json`)
      .then((r) => (r.ok ? r.json() : { towns: [] }))
      .then((j: { towns: PackTown[] }) => j.towns)
      .catch(() => []));
  }

  /** Requests run one at a time, in order, like the bridge. */
  private serial<T>(f: () => Promise<T>): Promise<T> {
    const p = this.chain.then(f, f);
    this.chain = p.catch(() => {});
    return p;
  }
  private call<T>(req: object): Promise<T> {
    return this.serial(async () => unwrap<T>(await this.current.ask(JSON.stringify(req))));
  }

  puzzle() { return this.call<PuzzleReply>({ cmd: "puzzle" }); }
  demo() { return this.call<PuzzleReply>({ cmd: "demo" }); }
  evaluate(solution: Solution, rate = false) { return this.call<EvalReply>({ cmd: "evaluate", solution, rate }); }
  solve() { return this.call<SolveReply>({ cmd: "solve" }); }

  newPuzzle(seed: number, size: Size = "medium", replay = false): Promise<GenerateReply> {
    return this.serial(async () => {
      if (replay) {
        // exactly this seed's town, in a new worker
        const w = new LeanWorker();
        const g = unwrap<GenerateReply>(await w.make(seed >>> 0, SIZES[size]));
        this.swap(w);
        return g;
      }
      // a pack town not played yet on this device
      const seen = played();
      const t = (await this.pack(size)).find((x) => !seen.has(x.seed));
      const fromPack = t && (await this.load(t));
      if (fromPack) return fromPack;
      // the town made in the background
      const r = this.ready[size]!;
      delete this.ready[size];
      const line = await r.reply;
      this.prepare(size);
      const g = unwrap<GenerateReply>(line);
      if (g.generated) this.swap(r.w); else r.w.stop();
      return g;
    });
  }

  /** One starter-pack town by its seed (the tutorial town), played before or not. */
  packTown(size: Size, seed: number): Promise<GenerateReply> {
    return this.serial(async () => {
      const t = (await this.pack(size)).find((x) => x.seed === seed);
      const g = t && (await this.load(t));
      if (g) return g;
      const w = new LeanWorker();
      const r = unwrap<GenerateReply>(await w.make(seed >>> 0, SIZES[size]));
      if (r.generated) this.swap(w); else w.stop();
      return r;
    });
  }

  /** Open a pack town with Lean's `load`, which checks its stored best plan first. */
  private async load(t: PackTown): Promise<GenerateReply | null> {
    const w = new LeanWorker();
    try {
      const l = unwrap<{ verified: GenerateReply["verified"]; puzzle: PuzzleReply }>(
        await w.ask(JSON.stringify({ cmd: "load", puzzle: t.puzzle, best: t.best, bestScore: t.bestScore })));
      this.swap(w);
      return { generated: true, seed: t.seed, verified: l.verified, puzzle: l.puzzle,
        info: { attempts: 0, work: 0, workBudget: 0, randomPlay: t.randomMedian === undefined ? undefined : { median: t.randomMedian, p95: 0, rated: 0 } } };
    } catch { w.stop(); return null; /* fall back to a town made here */ }
  }

  private swap(w: LeanWorker) { this.current.stop(); this.current = w; }
}
