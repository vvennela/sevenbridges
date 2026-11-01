// Round-trip check: puzzle, evaluate (the first fixture solution), solve, and a bad command.
// Start the bridge first (npm start), then: node test-bridge.mjs [port]
import WebSocket from "ws";
const ws = new WebSocket(`ws://localhost:${process.argv[2] ?? 8787}`);
const pending = [];
const ask = (req) => new Promise((res) => { pending.push(res); ws.send(JSON.stringify(req)); });
ws.on("message", (m) => pending.shift()(JSON.parse(m.toString())));
ws.on("open", async () => {
  const pz = await ask({ cmd: "puzzle" });
  console.log("puzzle:", pz.ok, pz.data.puzzle.name, pz.data.puzzle.map.blocks.length, "blocks");
  const build = pz.data.puzzle.fixed.map((f) => f ?? { kind: "empty", stories: 0 });
  const routesOn = pz.data.puzzle.routes.map(() => false);
  // Fire evaluate, solve and a bogus command at once to check reply order.
  const [ev, sv, bad] = await Promise.all([
    ask({ cmd: "evaluate", solution: { build, routesOn, station: null } }),
    ask({ cmd: "solve" }),
    ask({ cmd: "nope" }),
  ]);
  console.log("evaluate:", ev.ok, "valid", ev.data?.valid, "cost", ev.data?.report?.cost, "score", ev.data?.score);
  console.log("solve:", sv.ok, "best score", sv.data?.best?.score, sv.data?.theorem);
  console.log("bad:", bad.ok, bad.error);
  const good = pz.ok && ev.ok && sv.ok && !bad.ok && "best" in sv.data && "valid" in ev.data;
  console.log(good ? "OK" : "FAIL");
  process.exit(good ? 0 : 1);
});
