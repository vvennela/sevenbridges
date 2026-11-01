// WebSocket client for the bridge. The bridge answers requests in the order
// they were sent, so a simple FIFO of pending promises matches replies.
import type { EvalReply, GenerateReply, PuzzleReply, Reply, Request, Solution, SolveReply } from "./types";

type Pending = { resolve: (v: unknown) => void; reject: (e: Error) => void };

export class Engine {
  private ws!: WebSocket;
  private pending: Pending[] = [];
  private opened!: Promise<void>;
  onStatus: (connected: boolean) => void = () => {};

  constructor(private url: string) {
    this.connect();
  }

  private connect() {
    this.ws = new WebSocket(this.url);
    this.opened = new Promise((res, rej) => {
      this.ws.onopen = () => { this.onStatus(true); res(); };
      this.ws.onerror = () => rej(new Error(`cannot reach the engine at ${this.url}`));
    });
    this.opened.catch(() => {});
    this.ws.onmessage = (ev) => {
      const p = this.pending.shift();
      if (!p) return;
      try {
        const reply = JSON.parse(String(ev.data)) as Reply<unknown>;
        if (reply.ok) p.resolve(reply.data);
        else p.reject(new Error(reply.error));
      } catch (e) {
        p.reject(e as Error);
      }
    };
    this.ws.onclose = () => {
      this.onStatus(false);
      for (const p of this.pending.splice(0)) p.reject(new Error("connection to the engine closed"));
      setTimeout(() => this.connect(), 1500);
    };
  }

  private async call<T>(req: Request): Promise<T> {
    await this.opened;
    return new Promise<T>((resolve, reject) => {
      this.pending.push({ resolve: resolve as (v: unknown) => void, reject });
      this.ws.send(JSON.stringify(req));
    });
  }

  puzzle() { return this.call<PuzzleReply>({ cmd: "puzzle" }); }
  /** Reset the engine to the hand-made demo puzzle (Old Harbor). */
  demo() { return this.call<PuzzleReply>({ cmd: "demo" }); }
  /** `rate`: also get the rating out of 100 (solves the puzzle the first time). */
  evaluate(solution: Solution, rate = false) { return this.call<EvalReply>({ cmd: "evaluate", solution, rate }); }
  /** `size`: easy / medium / hard = 5 / 7 / 9 blocks. */
  /** `replay`: rebuild exactly this seed's town; otherwise any fresh random town (often ready at once). */
  newPuzzle(seed: number, size: "easy" | "medium" | "hard" = "medium", replay = false) { return this.call<GenerateReply>({ cmd: "newPuzzle", seed, size, replay }); }
  solve() { return this.call<SolveReply>({ cmd: "solve" }); }
}

/** The bridge URL: `?ws=ws://host:port` overrides; default is the Vite proxy at /ws. */
export function engineUrl(): string {
  const q = new URLSearchParams(location.search).get("ws");
  if (q) return q;
  return `${location.protocol === "https:" ? "wss" : "ws"}://${location.host}/ws`;
}
