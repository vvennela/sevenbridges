// A Web Worker that runs the Lean backend compiled to WebAssembly
// (web/public/engine, built by wasm/build.sh). One worker = one game state.
// Messages in:  { id, line }                 -> one request line, answered by Lean
//               { id, make: { seed, blocks } } -> make a town (up to 3 maps, as the bridge does)
// Messages out: { id, reply }                 -> the reply line
import { generateMap } from "../../tools/genmap.mjs";

type LeanModule = { _sb_init(): number; ccall(name: string, ret: string, args: string[], vals: unknown[]): string };

const ready: Promise<LeanModule> = (async () => {
  const url = new URL(`${import.meta.env.BASE_URL}engine/sevenbridges.mjs`, self.location.origin).href;
  const mod = await import(/* @vite-ignore */ url);
  const M = (await mod.default()) as LeanModule;
  M._sb_init();
  return M;
})();

function generateLine(seed: number, blocks: number): string {
  const m = generateMap(seed, blocks);
  return JSON.stringify({ cmd: "generate", seed, routes: m.routes, map: { points: m.points, segments: m.segments, blocks: m.blocks } });
}

self.onmessage = async (ev: MessageEvent) => {
  const { id, line, make } = ev.data as { id: number; line?: string; make?: { seed: number; blocks: number } };
  let reply = "";
  try {
    const M = await ready;
    const ask = (l: string) => M.ccall("sb_request", "string", ["string"], [l]);
    if (make) {
      for (let tries = 0; tries < 3; tries++) {
        reply = ask(generateLine((make.seed + 7919 * tries) >>> 0, make.blocks));
        try {
          const j = JSON.parse(reply);
          if (!(j.ok && j.data && j.data.generated === false)) break;
        } catch { break; }
      }
    } else reply = ask(line ?? "");
  } catch (e) {
    reply = JSON.stringify({ ok: false, error: `engine: ${(e as Error).message}` });
  }
  (self as unknown as Worker).postMessage({ id, reply });
};
