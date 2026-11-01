import * as THREE from "three";
// Game flow and HUD. Rule: nothing here decides an outcome. Cost, validity,
// rating, happiness, feelings, riders and trips are all read from Lean's
// replies. Turning Lean's facts into friendly sentences is the only "logic".
import "@fontsource/fredoka/500.css";
import "@fontsource/fredoka/600.css";
import "@fontsource/nunito/400.css";
import "@fontsource/nunito/600.css";
import "@fontsource/nunito/700.css";
import "./style.css";
import { Engine, engineUrl } from "./api";
import { FACTOR_ICON, ICON } from "./icons";
import { AVATAR_FUR, C, FACTOR, KIND_NAME, ROUTE_COLORS, SUBWAY_COLOR, groupColor, say } from "./palette";
import { renderThumbs } from "./thumbs";
import type { Building, CatDay, EvalReply, Kind, Personality, PuzzleReply, Resident, Solution, Trip } from "./types";
import backdropFixture from "../fixtures/puzzle.json";
import { Transit } from "./transit";
import type { Link } from "./overlays";
import { World, type Feeling, type Target } from "./world";
import type { CrimeSpot, Cue, IdleMode } from "./transit";
import type { V2 } from "./geom";

const $ = <T extends HTMLElement = HTMLElement>(id: string) => document.getElementById(id) as T;

type Tool = Kind | "subway" | "bridge" | null;

interface State {
  pr: PuzzleReply | null;
  build: Building[];
  routesOn: boolean[];
  station: number | null;
  mode: "edit" | "built";
  live: EvalReply | null;    // latest evaluate (cost, feelings, trips; the rating stays hidden)
  built: EvalReply | null;   // evaluate at the last Build (with the rating)
  tool: Tool;
  error: string | null;
  postcardOpen: boolean;
  bridges: boolean[];
}

const st: State = {
  pr: null, build: [], routesOn: [], station: null, mode: "edit", live: null, built: null,
  tool: null, error: null, postcardOpen: false, bridges: [],
};

const world = new World($("scene"));
const engine = new Engine(engineUrl());
let thumbs: Record<string, string> = {};

// ---------- helpers ----------

const money = (k: number) => `$${Math.abs(k).toLocaleString()}k`;
const esc = (s: string) => s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!);
const sameB = (a: Building, b: Building) => a.kind === b.kind && (a.stories === b.stories || a.kind === "empty");
const hasFloors = (k: string) => k === "housing" || k === "office" || k === "shop" || k === "food";
const floorsText = (b: Building) => `${b.stories} ${b.stories === 1 ? "floor" : "floors"}`;
const plural = (g: string) => g;

/** Set innerHTML only when it changed, so buttons aren't replaced mid-click. */
const lastHTML = new Map<string, string>();
function setHTML(id: string, html: string) {
  if (lastHTML.get(id) !== html) { $(id).innerHTML = html; lastHTML.set(id, html); }
}

function solution(): Solution {
  // `?mock` previews food and tall offices before Lean has them: Lean is sent the nearest V1 building
  const build = MOCK && mockedKinds ? st.build.map((b) => b.kind === "food" ? { kind: "shop" as Kind, stories: 1 } : b.kind === "office" && b.stories > 3 ? { kind: "office" as Kind, stories: 3 } : b) : st.build;
  const s: Solution = { build, routesOn: st.routesOn, station: st.station };
  // bridges go to Lean only when the puzzle has them (and not when they're mocked locally)
  if (st.pr?.puzzle.bridgeSites?.length && !MOCK) s.bridges = st.bridges;
  return s;
}
/** For drawing: includes the bridges even in mock mode. */
function drawnBridges(): boolean[] { return st.bridges; }

/** `?mock`: add a river, bridge sites and personalities locally, to try the UI before Lean sends them. */
const MOCK = new URLSearchParams(location.search).has("mock");
function mockPuzzle(pr: PuzzleReply) {
  const pz = pr.puzzle, segs = pz.map.segments;
  const owners = new Map<number, number>();
  const key = (a: number, b: number) => (a < b ? `${a},${b}` : `${b},${a}`);
  const idx = new Map(segs.map((s, i) => [key(s.a, s.b), i]));
  for (const bl of pz.map.blocks) bl.corners.forEach((c0, k) => { const i = idx.get(key(c0, bl.corners[(k + 1) % bl.corners.length])); if (i !== undefined) owners.set(i, (owners.get(i) ?? 0) + 1); });
  const inner = segs.map((_s, i) => i).filter((i) => owners.get(i) === 2);
  const ring = new Set(segs.flatMap((s, i) => (owners.get(i) === 1 ? [s.a, s.b] : [])));
  // a river: the shortest chain of inner streets from the ring road back to the ring road
  const adj = new Map<number, [number, number][]>();
  for (const i of inner) for (const [u, v] of [[segs[i].a, segs[i].b], [segs[i].b, segs[i].a]]) adj.set(u, [...(adj.get(u) ?? []), [v, i]]);
  let best: number[] = [];
  for (const start of ring) {
    const prev = new Map<number, [number, number]>([[start, [-1, -1]]]);
    const q = [start];
    while (q.length) {
      const u = q.shift()!;
      if (u !== start && ring.has(u)) {
        const path: number[] = [];
        for (let v = u; v !== start; v = prev.get(v)![0]) path.push(prev.get(v)![1]);
        if (path.length >= 2 && (!best.length || path.length < best.length)) best = path;
        continue;
      }
      for (const [v, i] of adj.get(u) ?? []) if (!prev.has(v)) { prev.set(v, [u, i]); q.push(v); }
    }
  }
  for (const i of best) segs[i].terrain = "stream";
  // every river segment (Lean's own, if any, plus the mock ones) gets a bridge site
  pz.bridgeSites = segs.map((s, i) => (s.terrain === "stream" ? i : -1)).filter((i) => i >= 0);
  pr.numbers.bridgeCost = 90;
  const T = [
    [{ name: "Gardeners", share: 50, cares: ["parks"], hates: [] }, { name: "Bookworms", share: 30, cares: ["quiet"], hates: ["nightlife"] }, { name: "Shoppers", share: 20, cares: ["shops"], hates: [] }],
    [{ name: "Night owls", share: 60, cares: ["nightlife"], hates: [] }, { name: "Commuters", share: 40, cares: ["transit"], hates: [] }],
  ];
  pz.groups.forEach((g, i) => { if (!g.types?.length) g.types = T[i % T.length]; });
  // Version 2 previews: food places and offices up to 5 floors (costs here are placeholders)
  mockedKinds = !pr.options.some((o) => o.building.kind === "food");
  if (mockedKinds) {
    const at = pr.options.findIndex((o) => o.building.kind === "park" || o.building.kind === "bar");
    pr.options.splice(at < 0 ? pr.options.length : at, 0, { building: { kind: "food", stories: 1 }, cost: 90, jobs: 0, residents: 0 }, { building: { kind: "food", stories: 2 }, cost: 200, jobs: 0, residents: 0 });
  }
  const o3 = pr.options.find((o) => o.building.kind === "office" && o.building.stories === 3);
  if (o3 && !pr.options.some((o) => o.building.kind === "office" && o.building.stories > 3)) pr.options.splice(pr.options.indexOf(o3) + 1, 0, { building: { kind: "office", stories: 4 }, cost: o3.cost + 150, jobs: 80, residents: 0 }, { building: { kind: "office", stories: 5 }, cost: o3.cost + 300, jobs: 100, residents: 0 });
  pz.simSeed ??= 7351;
  pz.verified ??= true;
}

/** True when ?mock added food/tall offices that Lean doesn't know yet (they're translated when sent). */
let mockedKinds = false;

/** `?mock`: pollution, traffic and a simulated day made up from Lean's trips, to preview the V2 look. */
function mockV2(r: EvalReply) {
  const rep = r.report, pz = st.pr!.puzzle;
  const n = pz.map.blocks.length;
  const real = !!rep.cats || !!rep.streets || rep.blocks?.some((b) => typeof b.polluted === "boolean");
  if (real) return r; // Lean sends the real day, streets and air: no mock data
  if (!rep.pollution) {
    const p = new Array<number>(n).fill(0);
    for (const t of rep.trips) if (String(t.mode) === "car" && t.fromBlock !== null && t.fromBlock !== undefined) { p[t.fromBlock] += t.people; for (const j of world.linkedNeighbors(t.fromBlock)) p[j] += t.people / 2; }
    st.build.forEach((b, i) => { if (b.kind === "office") p[i] += b.stories * 6; if (b.kind === "park") { p[i] = 0; for (const j of world.linkedNeighbors(i)) p[j] *= 0.5; } });
    rep.pollution = p.map(Math.round);
  }
  if (!rep.traffic) {
    const segs = pz.map.segments;
    const tr = segs.map(() => 0);
    for (const t of rep.trips) if (String(t.mode) === "car") for (const b of [t.fromBlock, t.toBlock]) {
      if (b === null || b === undefined) continue;
      const cs = pz.map.blocks[b].corners;
      segs.forEach((sg, si) => { if (cs.includes(sg.a) && cs.includes(sg.b)) tr[si] += t.people; });
    }
    rep.traffic = tr;
  }
  if (!rep.cats && rep.residents?.length) {
    const cats: CatDay[] = [];
    let id = 0;
    const shopsNear = (b: number, kinds: Kind[]) => [b, ...world.linkedNeighbors(b)].find((j) => kinds.includes(st.build[j]?.kind));
    for (const res of rep.residents) {
      const out = rep.trips.filter((t) => t.fromBlock === res.block && t.group === res.group);
      for (let k = 0; k < Math.min(4, Math.ceil(res.people / 8)); k++) {
        const trip: Trip | undefined = out[k % Math.max(1, out.length)];
        const mode = String(trip?.mode ?? "walk");
        const work = trip?.toBlock ?? null;
        const legs: CatDay["legs"] = [];
        if (trip) {
          legs.push({ from: res.block, to: work, mode, phase: "morning", route: trip.routes[0] });
          const lunch = work !== null ? shopsNear(work, ["food", "shop"]) : undefined;
          if (lunch !== undefined && lunch !== work) legs.push({ from: work, to: lunch, mode: "walk", phase: "lunch" }, { from: lunch, to: work, mode: "walk", phase: "lunch" });
          const night = (k % 2) ? shopsNear(res.block, ["bar", "park", "food"]) : undefined;
          if (night !== undefined && night !== res.block) {
            legs.push({ from: work, to: night, mode: mode === "car" ? "car" : "walk", phase: "evening" }, { from: night, to: res.block, mode: "walk", phase: "home" });
          } else legs.push({ from: work, to: res.block, mode, phase: "evening", route: trip.routes[0] });
        } else {
          const park = shopsNear(res.block, ["park", "shop", "food"]);
          if (park !== undefined && park !== res.block) legs.push({ from: res.block, to: park, mode: "walk", phase: "lunch" }, { from: park, to: res.block, mode: "walk", phase: "evening" });
        }
        if (legs.length) cats.push({ id: id++, home: res.block, group: res.group, type: res.type, mobility: mode === "car" ? "driver" : mode === "bus" ? "bus" : "walker", legs });
      }
    }
    rep.cats = cats;
  }
  return r;
}
/** In mock mode, give each resident entry a personality so the mood hover can group by it. */
function mockTypes(r: EvalReply) {
  if (!MOCK) return r;
  for (const x of r.report.residents ?? []) x.type ??= (x.block + x.group) % (st.pr!.puzzle.groups[x.group].types?.length ?? 1);
  return mockV2(r);
}

const CUE_OF: Record<string, Cue> = { nightlife: "moon", parks: "leaf", quiet: "book", shops: "bag", transit: "ticket", shortCommute: "star", walkability: "leaf" };
const cueOf = (t: Personality) => CUE_OF[t.cares[0] ?? ""] ?? null;
/** What's on the map right now. */
function shownSolution(): Solution {
  return solution();
}
function shownReply(): EvalReply | null {
  return st.mode === "built" ? st.built ?? st.live : st.live;
}

/** The heights Lean offers for a kind, lowest first. Picking the next one is UI, not a rule. */
function heights(kind: Kind): Building[] {
  return st.pr!.options.map((o) => o.building).filter((b) => b.kind === kind).sort((a, b) => a.stories - b.stories);
}
const emptyB = (): Building => st.pr!.options.find((o) => o.building.kind === "empty")?.building ?? { kind: "empty", stories: 0 };
const costOf = (b: Building) => (st.pr!.options.find((o) => sameB(o.building, b)) ?? st.pr!.fixedOptions.find((o) => sameB(o.building, b)))?.cost;
/** Building types in the order Lean lists them. */
function kinds(): Kind[] {
  const ks: Kind[] = [];
  for (const o of st.pr!.options) if (o.building.kind !== "empty" && !ks.includes(o.building.kind)) ks.push(o.building.kind);
  return ks;
}

// ---------- engine calls ----------

let liveBusy = false, liveDirty = false;
async function refreshLive() {
  if (liveBusy) { liveDirty = true; return; }
  liveBusy = true;
  try {
    st.live = mockTypes(await engine.evaluate(solution()));
    st.error = null;
  } catch (e) {
    st.error = (e as Error).message;
  }
  liveBusy = false;
  if (liveDirty) { liveDirty = false; void refreshLive(); return; }
  if (st.mode === "edit") showLife(st.live);
  render();
}

const SIZES = ["easy", "medium", "hard"] as const;
type Size = (typeof SIZES)[number];
/** `?size=easy|medium|hard` (5 / 7 / 8 blocks) for new neighborhoods. */
const wantedSize: Size = (() => { const s = new URLSearchParams(location.search).get("size"); return (SIZES as readonly string[]).includes(s ?? "") ? (s as Size) : "medium"; })();
const wantedSeed = (() => {
  const s = new URLSearchParams(location.search).get("seed");
  return s !== null && /^\d+$/.test(s) ? Number(s) : null;
})();

/** The level being played: its seed, size, and what Lean says about it. */
interface LevelInfo { seed: number; size: Size; simSeed?: number; verified?: boolean; randomMedian?: number }
let level: LevelInfo | null = null;
const params = new URLSearchParams(location.search);

/** Keep debug flags (?mock, ?test, ...) when the URL changes. */
function urlWith(extra: Record<string, string | null>): string {
  const q = new URLSearchParams(location.search);
  for (const [k, v] of Object.entries(extra)) if (v === null) q.delete(k); else q.set(k, v);
  const str = q.toString().replace(/=(&|$)/g, "$1");
  return str ? `?${str}` : location.pathname;
}

/** Ask Lean for a new random town of this size (a few seeds, in case one can't be planned). */
async function newTown(seed: number, size: Size): Promise<{ pr: PuzzleReply; info: LevelInfo }> {
  for (let s2 = seed, tries = 0; tries < 6; s2++, tries++) {
    const g = await engine.newPuzzle(s2, size);
    if (g.generated && g.puzzle) {
      const pz = g.puzzle.puzzle;
      const v = g.verified;
      const proof = typeof v === "object" && v !== null ? v : null;
      return { pr: g.puzzle, info: { seed: g.seed ?? s2, size, simSeed: g.simSeed ?? proof?.simSeed ?? pz.simSeed, verified: !!(proof ?? v ?? pz.verified), randomMedian: g.info.randomPlay?.median } };
    }
  }
  throw new Error("Couldn't plan a town this time");
}

const randomSeed = () => 1 + Math.floor(Math.random() * 99998);

// ---------- title screen ----------

type Screen = "home" | "rules" | "size" | "wait";
function showScreen(sc: Screen) {
  document.body.classList.add("titling");
  $("title").classList.remove("hidden");
  $("title").dataset.screen = sc;
  for (const el of document.querySelectorAll<HTMLElement>(".title-card")) el.classList.toggle("on", el.dataset.screen === sc);
}

/** The title backdrop: a sample town, fully built, buses running and cats out for a walk. Looks only. */
function loadBackdrop() {
  const pr = structuredClone((backdropFixture as unknown as { data: PuzzleReply }).data);
  pr.puzzle.name = "Backdrop";
  world.load(pr);
  const look: Building[] = [
    { kind: "housing", stories: 2 }, { kind: "office", stories: 5 }, { kind: "park", stories: 1 }, { kind: "food", stories: 1 },
    { kind: "housing", stories: 3 }, { kind: "shop", stories: 2 }, { kind: "bar", stories: 1 }, { kind: "housing", stories: 1 }, { kind: "office", stories: 3 },
  ];
  const build = pr.puzzle.map.blocks.map((_b, i) => look[i % look.length]);
  world.setBuild(build, pr.puzzle.stationSites[0] ?? null, true);
  world.transit?.setRoutes(pr.puzzle.routes.map(() => true));
  if (world.transit) world.transit.downtownDir = world.downtown;
  const homes = build.map((b, i) => (b.kind === "housing" ? i : -1)).filter((i) => i >= 0);
  const others = build.map((b, i) => (b.kind !== "housing" ? i : -1)).filter((i) => i >= 0);
  const trips: Trip[] = [];
  homes.forEach((h, k) => others.forEach((o, j) => trips.push({ cost: 0, fromBlock: h, toBlock: o, group: (k + j) % 2, mode: (k + j) % 3 === 0 ? "car" : "walk", people: 10, routes: [] })));
  world.transit?.setTrips(trips);
  world.orbit = 0.035;
  world.titleView();
}

function startTitle() {
  loadBackdrop();
  showScreen("home");
  $("loading").classList.add("gone");
  document.querySelectorAll<HTMLElement>(".rule-ic").forEach((el) => {
    const ic = el.dataset.ic;
    el.innerHTML = ic === "heart" ? ICON.heart() : ic === "bus" ? ICON.bus("#6FC3E8") : ic === "coin" ? ICON.coin() : ic === "star" ? ICON.star(true) : `<img src="${renderThumbs(["housing"])["housing"]}" alt=""/>`;
  });
  document.querySelectorAll<HTMLElement>(".size-blocks").forEach((el) => {
    const n = Number(el.dataset.n);
    el.innerHTML = Array.from({ length: n }, (_, k) => `<i style="--k:${k}"></i>`).join("");
  });
}

/** Start → pick a size → Lean makes the town and proves its best plan → play. */
async function playNew(size: Size, seed = randomSeed()) {
  showScreen("wait");
  $("wait-text").textContent = "Building your town…";
  try {
    const { pr, info } = await newTown(seed, size);
    history.replaceState(null, "", urlWith({ seed: String(info.seed), size: info.size }));
    enterLevel(pr, info);
  } catch (e) {
    $("wait-text").textContent = `${(e as Error).message}. Trying again…`;
    setTimeout(() => void playNew(size), 2000);
  }
}

/** Open a level: draw the town, set up the tray, and show its title card. */
function enterLevel(pr: PuzzleReply, info: LevelInfo | null) {
  if (MOCK) mockPuzzle(pr);
  if (info) { info.simSeed ??= pr.puzzle.simSeed; info.verified ??= pr.puzzle.verified; }
  level = info;
  pickSize = info?.size ?? pickSize;
  st.pr = pr;
  st.mode = "edit"; st.live = null; st.built = null; st.tool = null; st.station = null; st.postcardOpen = false;
  const pz = pr.puzzle;
  st.bridges = (pz.bridgeSites ?? []).map(() => false);
  // Lean may send `fixed: []` (no starting blocks): every block starts as an open lot
  st.build = pz.map.blocks.map((_b, i) => pz.fixed[i] ?? emptyB());
  st.routesOn = pz.routes.map(() => false);
  if (!pz.stationSites?.length && pz.metroSites?.length) pz.stationSites = pz.metroSites;
  world.orbit = 0;
  world.load(pr);
  if (world.transit) world.transit.downtownDir = world.downtown;
  document.body.dataset.setting = world.setting;
  thumbs = renderThumbs(kinds());
  world.setBuild(st.build, st.station, true);
  world.transit?.setRoutes(st.routesOn);
  world.setBridges(st.bridges);
  if (world.transit) world.transit.typeCues = pz.groups.map((g) => (g.types ?? []).map((t) => ({ cue: cueOf(t), share: t.share })));
  for (const k of ["town", "meter", "tools", "transit"]) lastHTML.delete(k);
  document.body.classList.remove("titling");
  $("title").classList.add("hidden");
  renderTown();
  render();
  showIntro();
  $("loading").classList.add("gone");
  void refreshLive();
}

/** The level's title card: its seeds, and that Lean has proven its best plan. */
function showIntro() {
  if (!st.pr || params.has("nointro")) { coach(); return; }
  const pz = st.pr.puzzle;
  const meta = [
    level ? `Town #${level.seed}` : pz.name,
    level?.simSeed !== undefined ? `simulation #${level.simSeed}` : null,
  ].filter(Boolean).join(" · ");
  const sizeName = level ? `${level.size[0].toUpperCase()}${level.size.slice(1)} town, ${pz.map.blocks.length} blocks` : `${pz.map.blocks.length} blocks`;
  const who = pz.groups.map((g, i) => `<span class="intro-who">${ICON.avatar(groupColor(i), AVATAR_FUR[i % AVATAR_FUR.length], i % 2 ? "scarf" : "tie")}${esc(g.name)} <small>${g.share}%</small></span>`).join("");
  setHTML("intro", `<div class="intro-card">
    <div class="intro-kicker">${esc(sizeName)}</div>
    <h2>${esc(level ? `Town #${level.seed}` : pz.name)}</h2>
    ${level?.simSeed !== undefined || level?.verified ? `<div class="intro-meta">${esc(meta)}</div>` : ""}

    <div class="intro-whos">${who}</div>
    <button class="tbtn primary" data-act="go">Let's build</button></div>`);
  $("intro").classList.remove("hidden");
}
function hideIntro() { $("intro").classList.add("hidden"); coach(); }

async function boot() {
  try {
    if (wantedSeed !== null) {
      $("loading-text").textContent = "Building your town…";
      const { pr, info } = await newTown(wantedSeed, wantedSize);
      if (info.seed !== wantedSeed) history.replaceState(null, "", urlWith({ seed: String(info.seed), size: info.size }));
      enterLevel(pr, info);
    } else if (params.has("demo")) {
      enterLevel(await engine.demo(), null);
    } else startTitle();
  } catch (e) {
    $("loading-text").textContent = `${(e as Error).message}. Retrying…`;
    setTimeout(boot, 2500);
  }
}

// ---------- the living town: feelings, residents, buses ----------

function feelingsFrom(r: EvalReply | null): Feeling[] {
  const out: Feeling[] = st.build.map(() => null);
  for (const res of r?.report.residents ?? []) {
    if (res.unhappy) out[res.block] = "unhappy";
    else if (out[res.block] !== "unhappy") out[res.block] = "happy";
  }
  return out;
}

/** Pollution per block from Lean (report.pollution, or the per-block entries), or null. */
function pollutionOf(r: EvalReply | null): number[] | null {
  const rep = r?.report;
  if (rep?.pollution?.length) return rep.pollution;
  if (rep?.blocks?.some((b) => typeof b.polluted === "boolean")) {
    const out = st.build.map(() => 0);
    for (const b of rep.blocks) out[b.block] = b.polluted ? 1 : 0;
    return out;
  }
  if (rep?.blocks?.some((b) => b.pollution !== undefined)) {
    const out = st.build.map(() => 0);
    for (const b of rep.blocks) out[b.block] = b.pollution ?? 0;
    return out;
  }
  return null;
}

/** Set by Build: the next showLife starts Lean's day over from the morning. */
let restartDay = false;

function showLife(r: EvalReply | null) {
  const s = shownSolution();
  world.setFeelings(feelingsFrom(r));
  const rep0 = r?.report;
  // Lean's simulated day when it sends one; otherwise the trips, looping
  if (rep0?.cats?.length) {
    world.transit?.setTrips(null);
    // edits keep the time of day; only Build starts the day over from the morning
    world.transit?.setDay(rep0.cats, undefined, restartDay);
    restartDay = false;
  } else {
    world.transit?.setDay(null);
    world.transit?.setTrips(rep0?.trips ?? null);
  }
  // air: haze over polluted blocks, fresh air over parks (only when Lean reports pollution)
  const pol = pollutionOf(r);
  const top = pol ? Math.max(1, ...pol) : 1;
  world.setAir(pol ? pol.map((v) => v / top) : null, s.build.map((b, i) => (b.kind === "park" ? i : -1)).filter((i) => i >= 0));
  // busy streets: cars looping and a warm wash, as much as Lean's traffic says
  // Lean's streets: [{segment, cars}] — a wash and that many looping cars on exactly those streets
  let tl: number[] | null = null;
  if (rep0?.streets) {
    const pz = st.pr!.puzzle;
    const cars = pz.map.segments.map(() => 0);
    for (const x of rep0.streets) if (x.segment >= 0 && x.segment < cars.length) cars[x.segment] = x.cars;
    const top = Math.max(1, ...cars);
    // no wash or cars on the river itself, except over a built bridge
    pz.map.segments.forEach((sg, i) => { if (sg.terrain === "stream" && !(pz.bridgeSites ?? []).some((seg, k) => seg === i && st.bridges[k])) cars[i] = 0; });
    tl = cars.map((c) => (c > 0 ? 0.25 + 0.75 * (c / top) : 0));
    world.transit?.setTraffic(cars, true);
  } else {
    const tr = rep0?.traffic;
    const tmax = tr ? Math.max(1, ...tr) : 1;
    tl = tr ? tr.map((v) => v / tmax) : null;
    world.transit?.setTraffic(tl);
  }
  // Lean's per-block fact "cats of this block or next door drive": wash the streets around those blocks
  if (!tl && !rep0?.streets && rep0?.blocks?.some((b) => b.traffic === true)) {
    const pz = st.pr!.puzzle;
    const busy = new Set(rep0.blocks.filter((b) => b.traffic === true).map((b) => b.block));
    tl = pz.map.segments.map((sg) => pz.map.blocks.some((bl, i) => busy.has(i) && bl.corners.includes(sg.a) && bl.corners.includes(sg.b)) ? 0.5 : 0);
  }
  world.setTraffic(tl);
  // residents idling: in their own yards, on benches and in parks (looks only)
  const res = r?.report.residents ?? [];
  const groups = [...new Set(res.map((x) => x.group))];
  const items: { p: V2; mode: IdleMode; ang: number; group: number; kid?: boolean; beer?: boolean; cig?: boolean; fightEvery?: number; cue?: Cue }[] = [];
  if (groups.length) {
    s.build.forEach((b, i) => {
      const sp = world.spotsOf(i);
      const here = res.filter((x) => x.block === i).map((x) => x.group);
      const who = here.length ? here : groups;
      let k = 0;
      if (b.kind === "housing" || b.kind === "park" || b.kind === "bar" || b.kind === "shop") {
        const n = b.kind === "housing" ? Math.min(5, 2 + b.stories) : b.kind === "park" ? 5 : 3;
        const modes: IdleMode[] = ["stroll", "wave", "nap", "stroll", "groom"];
        const typed = res.filter((x) => x.block === i && x.type !== undefined);
        const cueAt = (k2: number): Cue | undefined => { const x = typed[k2 % (typed.length || 1)]; const t = x ? st.pr!.puzzle.groups[x.group].types?.[x.type!] : undefined; return t ? cueOf(t) : undefined; };
        for (const p of sp.strolls.slice(0, n)) { items.push({ p, mode: modes[k % modes.length], ang: (k * 1.7 + i) % 6.28, group: typed.length ? typed[k % typed.length].group : who[k % who.length], cue: cueAt(k) }); k++; }
      }
      for (const bn of sp.benches) items.push({ p: bn.p, mode: "sit", ang: bn.ang, group: who[(k++) % who.length] });
    });
  }
  // kittens: with family-type groups, or now and then on any home block
  const pz = st.pr!.puzzle;
  const kidG = new Set(pz.groups.map((g, i) => (/famil|kid|parent|child/i.test(g.name) ? i : -1)).filter((i) => i >= 0));
  if (world.transit) world.transit.kidGroups = kidG;
  s.build.forEach((b, i) => {
    if (b.kind !== "housing" && b.kind !== "park") return;
    const here = res.filter((x) => x.block === i);
    const fam = here.find((x) => kidG.has(x.group)) ?? (b.kind === "park" ? res.find((x) => kidG.has(x.group)) : undefined);
    const g = fam?.group ?? (here.length && (i % 5 === 0) ? here[0].group : null);
    if (g === null || g === undefined) return;
    const sp = world.spotsOf(i).strolls;
    const spot = sp[sp.length - 1] ?? world.centerOf(i);
    for (let k = 0; k < (fam ? 3 : 1); k++) items.push({ p: spot, mode: "wave", ang: k * 2.1, group: g, kid: true });
  });
  // the bar: grown-ups with beers on the patio; scuffles happen as often as Lean's data says
  // the area is troubled (crime on the bar's block or next door, or unhappy neighbors)
  const rep = r?.report;
  s.build.forEach((b, i) => {
    if (b.kind !== "bar" || !groups.length) return;
    const area = [i, ...world.neighbors(i)];
    const crime = area.reduce((a, j) => a + (rep?.crime[j] ?? 0), 0);
    const unhappy = res.filter((x) => area.includes(x.block) && x.unhappy).reduce((a, x) => a + x.people, 0);
    const trouble = crime * 2 + (unhappy > 0 ? 1 : 0) + (unhappy > 20 ? 1 : 0);
    const c0 = world.centerOf(i);
    // spread the patrons over the patio and garden: pick spots far from each other and from the bar
    const pool = world.spotsOf(i).strolls.filter((q) => Math.hypot(q.x - c0.x, q.y - c0.y) > 0.9);
    const spots: V2[] = [];
    while (spots.length < 5 && pool.length) {
      let bi = 0, bd = -1;
      pool.forEach((q, k) => { const d = Math.min(...spots.map((s2) => Math.hypot(q.x - s2.x, q.y - s2.y)), 99); if (d > bd) { bd = d; bi = k; } });
      spots.push(pool.splice(bi, 1)[0]);
    }
    if (!spots.length) spots.push(c0);
    const who = [...new Set(res.filter((x) => area.includes(x.block)).map((x) => x.group))];
    const pickG = (k: number) => (who.length ? who : groups)[k % (who.length || groups.length)];
    // pairs stand side by side to the camera (angle ~ along the screen), clinking beers
    for (let k = 0; k < Math.min(3, spots.length); k++) items.push({ p: spots[k], mode: "groom", ang: -0.45, group: pickG(k), beer: true });
    if (spots[3]) items.push({ p: spots[3], mode: "nap" as IdleMode, ang: 0.5, group: pickG(2), cig: true });
    // one pair that might square up (calm, happy areas: never); ?fights forces it
    const every = FIGHTS ? 7 : trouble >= 3 ? 9 : trouble === 2 ? 16 : trouble === 1 ? 32 : 0;
    items.push({ p: spots[4] ?? spots[spots.length - 1] ?? c0, mode: "fight", ang: -0.45, group: pickG(1), beer: false, fightEvery: every });
  });
  world.transit?.setIdlers(items);
  // cartoon crime where Lean reports trouble: crime on a block, unhappy residents, a housing shortage
  const crimes: CrimeSpot[] = [];
  s.build.forEach((b, i) => {
    if (b.kind === "empty") return;
    const unhappy = res.filter((x) => x.block === i && x.unhappy).reduce((a, x) => a + x.people, 0);
    const shortage = (rep?.shortage ?? 0) > 0 && b.kind === "housing" ? 1 : 0;
    let trouble = (rep?.crime[i] ?? 0) * 2 + (unhappy > 0 ? 1 : 0) + shortage;
    if (CRIME && b.kind !== "park") trouble = Math.max(trouble, 4);
    if (trouble <= 0) return;
    crimes.push({ ring: world.sidewalkRing(i), every: Math.max(16, 60 / trouble), forceKO: CRIME, group: res.find((x) => x.block === i)?.group ?? 0 });
  });
  world.transit?.setCrime(crimes);
}

// ---------- player actions ----------

type Lens = "none" | "mood" | "jobs" | "transit";
let lens: Lens = "none";

/** `?fights`: debug flag, forces the most frequent bar scuffles. */
const FIGHTS = new URLSearchParams(location.search).has("fights");
/** `?crime`: debug flag, forces burglars on every built block (and the rare knockout). */
const CRIME = new URLSearchParams(location.search).has("crime");

let pickSize: Size = wantedSize;

let edits = 0;
function setBlock(i: number, b: Building) {
  st.build = st.build.map((x, k) => (k === i ? b : x));
  edits++;
  world.setBuild(st.build, st.station);
  void refreshLive();
  coach();
}

const canEdit = () => !!st.pr && st.mode === "edit";

/** Left-click builds or raises; right-click lowers, and clears at the lowest level. */
function editBlock(i: number, up: boolean, useTool: boolean) {
  if (!canEdit()) return;
  if (st.pr!.puzzle.fixed[i]) { world.shake(i); toast("This block is already built"); return; }
  const cur = st.build[i];
  const tool = useTool && st.tool && st.tool !== "subway" && st.tool !== "bridge" ? st.tool : null;
  if (up) {
    if (tool === "empty") { if (cur.kind !== "empty") setBlock(i, emptyB()); return; }
    const kind = tool ?? cur.kind;
    if (kind === "empty") { world.shake(i); toast("Pick a building below first"); return; }
    const hs = heights(kind);
    if (cur.kind !== kind) { setBlock(i, hs[0]); return; }
    const at = hs.findIndex((h) => sameB(h, cur));
    if (at >= 0 && at + 1 < hs.length) setBlock(i, hs[at + 1]);
    else { world.shake(i); toast(`${KIND_NAME[kind]} can't go higher here`); }
  } else if (cur.kind !== "empty") {
    const hs = heights(cur.kind);
    const at = hs.findIndex((h) => sameB(h, cur));
    setBlock(i, at > 0 ? hs[at - 1] : emptyB());
  }
}

function toggleRoute(i: number) {
  if (!canEdit()) return;
  st.routesOn = st.routesOn.map((on, k) => (k === i ? !on : on));
  world.transit?.setRoutes(st.routesOn);
  edits++;
  void refreshLive();
  render();
}

function toggleBridge(i: number) {
  if (!canEdit()) return;
  st.bridges = st.bridges.map((on, k) => (k === i ? !on : on));
  world.setBridges(drawnBridges());
  edits++;
  void refreshLive();
  render();
}

function setStation(s: number | null) {
  if (!canEdit()) return;
  st.station = s;
  world.setBuild(st.build, s);
  edits++;
  void refreshLive();
  render();
}

function pickTool(t: Tool) {
  if (!canEdit()) return;
  st.tool = st.tool === t ? null : t;
  render();
  coach();
}

async function build() {
  if (!st.pr) return;
  st.mode = "built";
  st.tool = null;
  st.postcardOpen = true;
  localStorage.setItem("sb-coach", "3");
  hideCard();
  world.setBuild(st.build, st.station, true);
  render();
  try {
    const r = mockTypes(await engine.evaluate(solution(), true));
    st.built = r;
    st.live = r;
    setTimeout(() => { restartDay = true; showLife(r); countUp(r.rating?.rating ?? 0); if ((r.rating?.rating ?? 0) >= 100) world.heartBurst(); }, 700);
  } catch (e) {
    st.error = (e as Error).message;
  }
  render();
  coach();
}

function keepBuilding() {
  st.mode = "edit";
  st.postcardOpen = false;
  world.setBuild(st.build, st.station);
  world.transit?.setRoutes(st.routesOn);
  showLife(st.live);
  render();
}

// ---------- rendering ----------

function render() {
  if (!st.pr) return;
  document.body.classList.toggle("built", st.mode === "built");
  renderMeter();
  renderTray();
  renderPostcard();
  const s = shownSolution();
  const open = s.build.map((_b, i) => (canEdit() && st.tool && st.tool !== "subway" && st.tool !== "bridge" && !st.pr!.puzzle.fixed[i] ? i : -1)).filter((i) => i >= 0);
  world.setGlow(open);
  world.transit?.setShowSites(canEdit() && st.tool === "subway");
  world.setBridgeTool(canEdit() && st.tool === "bridge");
  updateLens();
  if (cardTarget) renderCard(cardTarget);
}

/** Top-left: the neighborhood and its residents (what they love and dislike). */
function renderTown() {
  const pz = st.pr!.puzzle;
  const rows = pz.groups.map((g, i) => {
    const chips = [
      ...g.cares.map((f) => factorChip(f, true, g.name)),
      ...g.hates.map((f) => factorChip(f, false, g.name)),
    ].join("");
    return `<div class="group">
      <span class="avatar">${ICON.avatar(groupColor(i), AVATAR_FUR[i % AVATAR_FUR.length], i % 2 ? "scarf" : "tie")}</span>
      <span class="group-name">${esc(g.name)}<small>${g.share}%</small><i class="swatch" style="background:${groupColor(i)}" data-tip="${esc(g.name)} wear ${colorName(i)} ties and scarves"></i></span>
      <span class="chips">${chips}</span>
      ${g.types?.length ? `<span class="types">${g.types.map((t) => `<span class="ptype" data-tip="${esc(t.name)}: ${t.cares.map((f) => `loves ${(FACTOR[f]?.name ?? f).toLowerCase()}`).concat(t.hates.map((f) => `dislikes ${(FACTOR[f]?.name ?? f).toLowerCase()}`)).join(", ")}">${t.cares[0] ? FACTOR_ICON[t.cares[0]] ?? "" : ""}${esc(t.name)} <small>${t.share}%</small></span>`).join("")}</span>` : ""}
    </div>`;
  }).join("");
  const sizeName = level ? level.size[0].toUpperCase() + level.size.slice(1) : "Demo";
  const chips = [
    `<span class="diff">${sizeName}, ${pz.map.blocks.length} blocks</span>`,
    level?.simSeed !== undefined ? `<span class="chip" data-tip="The seed of this town's simulated day: every cat's traits and day come from it">Sim #${level.simSeed}</span>` : "",
    "",
  ].join("");
  setHTML("town", `<div class="town-head"><h1>${esc(level ? `Town #${level.seed}` : pz.name)}</h1>
      <span class="head-btns"><button class="icon-btn" data-act="new" data-tip="A new random town, same size">${ICON.dice()}</button>
      <button class="icon-btn" data-act="title" data-tip="Back to the title screen">${ICON.home()}</button></span></div>
    <div class="diff-row">${chips}</div>
    <p class="goal">Make your cats happy and your town productive, within budget.</p>
    ${rows}`);
}

const COLOR_NAMES = ["mustard", "teal", "plum", "olive", "coral"];
const colorName = (i: number) => COLOR_NAMES[i % COLOR_NAMES.length];

function factorChip(f: string, love: boolean, who: string) {
  const name = FACTOR[f]?.name ?? f;
  const tip = `${esc(who)} ${love ? "love" : "dislike"} ${name.toLowerCase()}`;
  return `<span class="factor ${love ? "love" : "hate"}" data-tip="${tip}">${FACTOR_ICON[f] ?? ""}<i>${love ? ICON.heart() : ICON.no()}</i></span>`;
}

let shownRating = 0;
function countUp(target: number) {
  const t0 = performance.now();
  const from = 0;
  const step = () => {
    const u = Math.min(1, (performance.now() - t0) / 1100);
    shownRating = Math.round(from + (target - from) * (1 - Math.pow(1 - u, 3)));
    renderMeter();
    if (u < 1) requestAnimationFrame(step);
  };
  step();
}

/** Top-right: rating ring with stars, then happiness and money left. */
function renderMeter() {
  const pz = st.pr!.puzzle;
  const r = shownReply();
  const rated = st.mode === "built" && st.built?.rating ? shownRating : null;
  const R = 38, L = 2 * Math.PI * R;
  const fill = rated === null ? 0 : rated / 100;
  const stars = [50, 80, 100].map((th) => `<span class="star">${ICON.star(rated !== null && rated >= th)}</span>`).join("");
  const cost = r?.report.cost;
  const left = cost === undefined ? null : pz.budget - cost;
  const spent = cost === undefined ? 0 : Math.min(1, cost / Math.max(1, pz.budget));
  setHTML("meter", `
    <div class="ring">
      <svg viewBox="0 0 100 100"><circle cx="50" cy="50" r="${R}" class="ring-bg"/>
        <circle cx="50" cy="50" r="${R}" class="ring-fill" style="stroke-dasharray:${L};stroke-dashoffset:${L * (1 - fill)}"/></svg>
      <div class="ring-num">${rated === null ? "?" : rated}</div>
    </div>
    <div class="stars">${stars}</div>
    <div class="ring-cap">${rated === null ? (st.mode === "built" ? "Rating…" : "Build to see your rating") : rated >= 100 ? "A perfect neighborhood" : "Your rating"}</div>
    <div class="pair">
      <div class="pair-cell" data-tip="Happiness: how much your cats like their homes and what's next door">${ICON.heart()}<b>${r ? r.report.happiness.toLocaleString() : "0"}</b><span>Happiness</span></div>
      <div class="pair-cell" data-tip="Productivity: the work done in offices by cats who can get there">${ICON.work()}<b>${r ? r.report.productivity.toLocaleString() : "0"}</b><span>Productivity</span></div>
    </div>
    <div class="bars">
      <div class="bar-row ${left !== null && left < 0 ? "over" : ""}" data-tip="Money left of ${money(pz.budget)}">${ICON.coin()}
        <span class="bar-val">${left === null ? money(pz.budget) : (left < 0 ? "−" : "") + money(left)}</span><span class="bar-label">${left !== null && left < 0 ? "over budget" : "left"}</span>
        <span class="money-bar"><span style="width:${spent * 100}%"></span></span></div>
    </div>`);
}

/** Bottom: the toy tray (building tiles, bus routes, subway) and the Build button. */
function renderTray() {
  const pr = st.pr!;
  const editing = canEdit();
  const tiles = kinds().map((k) => {
    const opts = pr.options.filter((o) => o.building.kind === k).sort((a, b) => a.cost - b.cost);
    // the cheapest height on the tile ("from" when there are taller ones); every height is in the tooltip
    const price = `${opts.length > 1 ? "from " : ""}${money(opts[0].cost)}`;
    const tip = hasFloors(k) && opts.length > 1
      ? `${KIND_NAME[k]}: ${opts.map((o) => `${o.building.stories} ${o.building.stories === 1 ? "floor" : "floors"} ${money(o.cost)}`).join(", ")}`
      : `${KIND_NAME[k]}: ${price}`;
    void tip;
    return `<button class="tile ${st.tool === k ? "picked" : ""}" data-tool="${k}" ${editing ? "" : "disabled"} data-info="${k}">
      <img src="${thumbs[k] ?? ""}" alt="" draggable="false"/><span class="tile-name">${KIND_NAME[k]}</span><span class="tile-price">${price}</span></button>`;
  }).join("") + `<button class="tile small ${st.tool === "empty" ? "picked" : ""}" data-tool="empty" ${editing ? "" : "disabled"} data-tip="Clear a block back to an open lot">
      <span class="tile-icon">${ICON.clear()}</span><span class="tile-name">Clear</span></button>`;
  setHTML("tools", tiles);
  const nb = pr.numbers;
  const routes = shownSolution().routesOn;
  const station = shownSolution().station;
  const bus = pr.puzzle.routes.map((r, i) => `<button class="tile small ${routes[i] ? "on" : ""} ${world.transit?.routeBlocked(i) ? "blocked" : ""}" data-route="${i}" ${editing ? "" : "disabled"}
      data-tip="${esc(r.name)} bus: ${money(nb.routeCost)}. It needs ${nb.minRouteRiders}+ riders a day, ${nb.minNewRiders}+ of them new. Click to turn it ${routes[i] ? "off" : "on"}.">
      <span class="tile-icon">${ICON.bus(ROUTE_COLORS[i % ROUTE_COLORS.length])}</span><span class="tile-name">${esc(r.name)}</span><span class="led"></span>${world.transit?.routeBlocked(i) ? `<span class="needs" data-tip="${esc(r.name)} crosses the river: it needs a bridge to run">${ICON.bridge()}</span>` : ""}</button>`).join("");
  const sub = pr.puzzle.stationSites.length ? `<button class="tile small ${station !== null ? "on" : ""} ${st.tool === "subway" ? "picked" : ""}" data-tool="subway" ${editing ? "" : "disabled"}
      data-tip="Metro station: ${money(nb.stationCost)}. The metro runs to downtown; it needs ${nb.minStationRiders}+ riders a day. Pick it, then click a faint entrance on the map.">
      <span class="tile-icon">${ICON.subway(SUBWAY_COLOR)}</span><span class="tile-name">Metro</span><span class="led"></span></button>` : "";
  const nBridge = st.bridges.filter(Boolean).length;
  const bridgeTile = pr.puzzle.bridgeSites?.length ? `<button class="tile small ${nBridge ? "on" : ""} ${st.tool === "bridge" ? "picked" : ""}" data-tool="bridge" ${editing ? "" : "disabled"}
      data-tip="Bridge${nb.bridgeCost !== undefined ? `: ${money(nb.bridgeCost)}` : ""}. Blocks across the river are neighbors only when a bridge joins them, and buses need one to cross. Pick it, then click a faint bridge on the river.">
      <span class="tile-icon">${ICON.bridge()}</span><span class="tile-name">Bridge</span>${nb.bridgeCost !== undefined ? `<span class="tile-price">${money(nb.bridgeCost)}</span>` : `<span class="led"></span>`}</button>` : "";
  setHTML("transit", bus + sub + bridgeTile);
  $("tray").dataset.hint = st.mode === "built" ? "Press Edit to change your plan" : "";
  const b = $<HTMLButtonElement>("build");
  b.classList.toggle("again", st.mode === "built");
  b.querySelector(".build-label")!.textContent = st.mode === "edit" ? "Build" : "Edit";
}

// ---------- the postcard after Build ----------

interface Note { icon: string; text: string }

/** Friendly sentences from Lean's resident facts. */
function notesFrom(r: EvalReply): { headline: string; notes: Note[] } {
  const pz = st.pr!.puzzle;
  const res: Resident[] = r.report.residents ?? [];
  const tally = (pick: (g: number, has: string[]) => string[]) => {
    const m = new Map<string, number>();
    for (const x of res) for (const f of pick(x.group, x.has)) m.set(`${x.group}:${f}`, (m.get(`${x.group}:${f}`) ?? 0) + x.people);
    return [...m.entries()].sort((a, b) => b[1] - a[1]).map(([k]) => { const [g, f] = k.split(":"); return { g: Number(g), f }; });
  };
  const loves = tally((g, has) => pz.groups[g].cares.filter((f) => has.includes(f)));
  const wishes = tally((g, has) => pz.groups[g].cares.filter((f) => !has.includes(f)));
  const dislikes = tally((g, has) => pz.groups[g].hates.filter((f) => has.includes(f)));
  const name = (g: number) => plural(pz.groups[g]?.name ?? "Residents");
  let headline = "";
  if (!r.valid) headline = r.problems.length > 1 ? "A few things need fixing first" : "One thing needs fixing first";
  else if (!res.length) headline = "No one lives here yet. Build some homes and they'll move in!";
  else if (loves[0]) headline = say(FACTOR[loves[0].f]?.love, name(loves[0].g), res.length);
  else headline = `${name(res[0].group)} are still settling in`;
  const notes: Note[] = [];
  for (const l of loves.slice(1, 2)) notes.push({ icon: ICON.heart(), text: say(FACTOR[l.f]?.love, name(l.g), 7) });
  for (const w of wishes.slice(0, 2)) notes.push({ icon: ICON.wish(), text: say(FACTOR[w.f]?.wish, name(w.g), res.length + 3) });
  for (const d of dislikes.slice(0, 1)) notes.push({ icon: ICON.no(), text: say(FACTOR[d.f]?.hate, name(d.g), 5) });
  for (const p of r.problems) notes.unshift({ icon: ICON.oops(), text: p });
  if (r.report.shortage > 0) notes.push({ icon: ICON.oops(), text: `There aren't enough homes for everyone who works here` });
  return { headline, notes: notes.slice(0, 4) };
}

function renderPostcard() {
  const el = $("postcard");
  const r = st.built;
  const show = st.mode === "built" && st.postcardOpen;
  el.classList.toggle("hidden", !show);
  document.body.classList.toggle("pc-open", show);
  if (!show) return;
  if (!r) { setHTML("postcard", `<div class="pc-wait">Rating your neighborhood…</div>`); return; }
  const rating = r.rating?.rating ?? 0;
  const { headline, notes } = notesFrom(r);
  const stars = [50, 80, 100].map((th) => `<span class="star big">${ICON.star(rating >= th)}</span>`).join("");
  setHTML("postcard", `
    <div class="pc-stamp">${rating >= 100 ? "A perfect neighborhood!" : rating >= 80 ? "What a lovely place" : rating >= 50 ? "A cozy start" : rating > 0 ? "Room to grow" : "Not quite working yet"}</div>
    <div class="pc-stars">${stars}</div>
    <div class="pc-sub">Rated ${rating} out of 100.</div>
    <div class="pc-head">${esc(headline)}</div>
    <ul class="pc-notes">${notes.map((n) => `<li><span class="pc-ic">${n.icon}</span><span>${esc(n.text)}</span></li>`).join("")}</ul>
    ${whyRating(r)}
    <div class="pc-actions">
      <button class="btn primary" data-act="keep">${rating >= 100 ? "Keep building" : "Try for 100"}</button>
    </div>
    <button class="pc-close" data-act="close-pc" title="Hide">×</button>`);
}


// ---------- lenses (explain what is; never suggest moves) ----------

const LENSES: { id: Lens; name: string; tip: string }[] = [
  { id: "none", name: "Plain", tip: "Plain view" },
  { id: "mood", name: "Mood", tip: "Mood lens: how happy each home is" },
  { id: "jobs", name: "Jobs", tip: "Jobs lens: jobs offered and filled" },
  { id: "transit", name: "Transit", tip: "Transit lens: riders on each route and stop" },
];

function lensIcon(id: Lens) {
  if (id === "mood") return ICON.heart();
  if (id === "jobs") return ICON.briefcase();
  if (id === "transit") return ICON.bus("#6FC3E8");
  return `<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="7" fill="none" stroke="#66718F" stroke-width="2"/><circle cx="12" cy="12" r="2.5" fill="#66718F"/></svg>`;
}

function renderLenses() {
  setHTML("lenses", LENSES.map((l) => `<button class="lens ${lens === l.id ? "on" : ""}" data-lens="${l.id}" data-tip="${l.tip}">${lensIcon(l.id)}<span>${l.name}</span></button>`).join("") +
    `<button class="lens recenter" data-act="recenter" data-tip="Recenter: show the whole town"><svg viewBox="0 0 24 24"><path d="M12 3v4M12 17v4M3 12h4M17 12h4" stroke="#66718F" stroke-width="2" stroke-linecap="round"/><circle cx="12" cy="12" r="4.5" fill="none" stroke="#66718F" stroke-width="2"/></svg><span>Center</span></button>`);
}

/** Happiness per person on each home block (from Lean's residents), or null. */
function moodPerPerson(r: EvalReply | null): (number | null)[] {
  const s = shownSolution();
  return s.build.map((_b, i) => {
    const here = (r?.report.residents ?? []).filter((x) => x.block === i);
    const people = here.reduce((a, x) => a + x.people, 0);
    return people ? here.reduce((a, x) => a + x.happinessEach * x.people, 0) / people : null;
  });
}

/** Jobs offered by a block's building (from Lean's options, or Lean's per-block report). */
function jobsOf(i: number, r: EvalReply | null): { jobs: number; workers: number | null } {
  const br = r?.report.blocks?.find((x) => x.block === i);
  if (br) return { jobs: br.jobs, workers: br.workers };
  const b = shownSolution().build[i];
  const opt = st.pr!.options.find((o) => sameB(o.building, b)) ?? st.pr!.fixedOptions.find((o) => sameB(o.building, b));
  // Lean's trips count residents, not job units, so "filled" waits for report.blocks
  return { jobs: opt?.jobs ?? 0, workers: null };
}

const MOOD_COLORS = ["#9AA6C2", "#C9C3E0", "#FFD9C2", "#FFB3A3", "#FF8B7B"]; // gray (glum) to heart-coral (happiest)
function lensTints(): (string | null)[] {
  const r = shownReply();
  const s = shownSolution();
  if (lens === "mood") {
    const mp = moodPerPerson(r);
    const vals = mp.filter((x): x is number => x !== null);
    const hi = Math.max(1, ...vals);
    return mp.map((v) => (v === null ? null : MOOD_COLORS[Math.max(0, Math.min(4, Math.floor((v / hi) * 4.999)))]));
  }
  if (lens === "jobs") return s.build.map((_b, i) => (jobsOf(i, r).jobs > 0 ? "#BFD8F6" : null));
  if (lens === "transit" && s.station !== null) return s.build.map((_b, i) => (i === s.station ? "#C9C8F6" : null));
  return s.build.map(() => null);
}

function updateLens() {
  if (!st.pr) return;
  document.body.dataset.lens = lens;
  renderLenses();
  world.setTint(lensTints());
  world.setBridgeLinks(lens === "mood" || lens === "jobs");
  const r = shownReply();
  const s = shownSolution();
  const widths = st.pr.puzzle.routes.map((_rt, i) => {
    if (lens !== "transit" || !s.routesOn[i]) return 0.085;
    const riders = r?.report.routes[i]?.riders ?? 0;
    return 0.07 + Math.min(0.2, riders / 400);
  });
  world.transit?.setRouteWidths(widths);
  renderBadges();
}

interface Badge { at: () => { x: number; y: number } | null; html: string }
let badges: Badge[] = [];
function renderBadges() {
  const r = shownReply();
  const s = shownSolution();
  const pr = st.pr!;
  badges = [];
  const blockAt = (i: number, h = 1.2) => () => world.project(world.centerOf(i), h);
  if (lens === "mood") {
    moodPerPerson(r).forEach((v, i) => {
      if (v === null) return;
      badges.push({ at: blockAt(i), html: `<span class="bdg mood">${ICON.heart()}${v.toFixed(1)}</span>` });
    });
  } else if (lens === "jobs") {
    s.build.forEach((_b, i) => {
      const { jobs, workers } = jobsOf(i, r);
      if (!jobs) return;
      const f = workers === null ? 0 : Math.min(1, workers / jobs);
      const C2 = 2 * Math.PI * 9;
      badges.push({ at: blockAt(i, 1.4), html: `<span class="bdg jobs"><svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9" fill="#fff" stroke="#E4E0EE" stroke-width="4"/><circle cx="12" cy="12" r="9" fill="none" stroke="#4F7FD0" stroke-width="4" stroke-dasharray="${C2}" stroke-dashoffset="${C2 * (1 - f)}" transform="rotate(-90 12 12)"/></svg>${workers === null ? "" : `${workers}/`}${jobs}</span>` });
    });
  } else if (lens === "transit") {
    pr.puzzle.routes.forEach((_rt, i) => {
      if (!s.routesOn[i]) return;
      const rr = r?.report.routes[i];
      const mid = world.transit?.routeMid(i);
      if (!mid || !rr) return;
      badges.push({ at: () => world.project(mid, 0.3), html: `<span class="bdg route" style="--c:${ROUTE_COLORS[i % ROUTE_COLORS.length]}">${ICON.bus(ROUTE_COLORS[i % ROUTE_COLORS.length])}${rr.riders}</span>` });
    });
    for (const st2 of r?.report.stops ?? []) {
      const max = Math.max(1, ...(r?.report.stops ?? []).map((x) => Math.max(x.boardings, x.alightings)));
      badges.push({ at: blockAt(st2.block, 0.6), html: `<span class="bdg stop" data-tip="Stop on ${esc(pr.puzzle.routes[st2.route]?.name ?? "")}: ${st2.boardings} get on, ${st2.alightings} get off"><i class="on" style="height:${4 + 18 * st2.boardings / max}px"></i><i class="off" style="height:${4 + 18 * st2.alightings / max}px"></i></span>` });
    }
    if (s.station !== null && r) badges.push({ at: blockAt(s.station, 1.0), html: `<span class="bdg route" style="--c:${SUBWAY_COLOR}">${ICON.subway(SUBWAY_COLOR)}${r.report.stationRiders}</span>` });
  }
  setHTML("badges", badges.map((b, k) => `<div class="badge" data-k="${k}">${b.html}</div>`).join(""));
}

function placeBadges() {
  const els = document.querySelectorAll<HTMLElement>("#badges .badge");
  els.forEach((el) => {
    const b = badges[Number(el.dataset.k)];
    const p = b?.at();
    if (!p) { el.style.display = "none"; return; }
    el.style.display = "";
    el.style.transform = `translate(${Math.round(p.x)}px, ${Math.round(p.y)}px) translate(-50%, -50%)`;
  });
}

/** Mood details for a home block: each group, how many, how they feel, and why. */
function moodDetails(i: number, r: EvalReply | null): string {
  const pz = st.pr!.puzzle;
  const here = (r?.report.residents ?? []).filter((x) => x.block === i);
  if (!here.length) return "";
  return `<div class="card-sec">${here.map((x) => {
    const g = pz.groups[x.group];
    const cares = [...new Set([...g.cares, ...(x.type !== undefined ? g.types?.[x.type]?.cares ?? [] : [])])];
    const hates0 = [...new Set([...g.hates, ...(x.type !== undefined ? g.types?.[x.type]?.hates ?? [] : [])])];
    const loves = cares.filter((f) => x.has.includes(f)).map((f) => `<span class="why love">${FACTOR_ICON[f] ?? ""}${FACTOR[f]?.name ?? f}</span>`);
    const hates = hates0.filter((f) => x.has.includes(f)).map((f) => `<span class="why hate">${FACTOR_ICON[f] ?? ""}${FACTOR[f]?.name ?? f}</span>`);
    const lacks = cares.filter((f) => !x.has.includes(f)).map((f) => `<span class="why lack">${FACTOR_ICON[f] ?? ""}${FACTOR[f]?.name ?? f}</span>`);
    const ty = x.type !== undefined ? g.types?.[x.type] : undefined;
    return `<div class="mood-row"><span class="who">${ICON.avatar(groupColor(x.group), AVATAR_FUR[x.group % AVATAR_FUR.length], x.group % 2 ? "scarf" : "tie")}${x.people} ${ty ? `${esc(ty.name)} <small class="of">(${esc(g.name)})</small>` : esc(g.name)}</span>
      <span class="feel ${x.unhappy ? "sad" : ""}">${x.unhappy ? "unhappy" : "happy"}, ${x.happinessEach} each</span>
      ${loves.length ? `<div class="whys"><b>Has, loves:</b>${loves.join("")}</div>` : ""}
      ${hates.length ? `<div class="whys"><b>Has, dislikes:</b>${hates.join("")}</div>` : ""}
      ${lacks.length ? `<div class="whys"><b>Misses:</b>${lacks.join("")}</div>` : ""}</div>`;
  }).join("")}</div>`;
}

/** Job details: offered, filled, and how workers get here (from Lean's trips). */
function jobDetails(i: number, r: EvalReply | null): string {
  const { jobs, workers } = jobsOf(i, r);
  if (!jobs) return "";
  const by = new Map<string, number>();
  for (const t of r?.report.trips ?? []) if (t.toBlock === i) by.set(String(t.mode), (by.get(String(t.mode)) ?? 0) + t.people);
  const MODE: Record<string, string> = { walk: "on foot", bus: "by bus", car: "by car", subway: "by subway" };
  const src = [...by.entries()].map(([k, v]) => `<span class="why">${v} ${MODE[k] ?? k}</span>`).join("");
  return `<div class="card-sec"><div class="whys"><b>Jobs:</b>${workers === null ? `${jobs} offered` : `${workers} filled of ${jobs}`}</div>${src ? `<div class="whys"><b>Commuters arrive:</b>${src}</div>` : ""}</div>`;
}

/** After Build: what this building does to the city (Lean's per-block impact). */
function impactDetails(i: number, r: EvalReply | null): string {
  if (st.mode !== "built") return "";
  const br = r?.report.blocks?.find((x) => x.block === i);
  if (!br) return "";
  const pz = st.pr!.puzzle;
  const parts = br.groupImpact.filter((g) => g.change !== 0).map((g) => `<span class="why ${g.change > 0 ? "love" : "hate"}">${esc(pz.groups[g.group]?.name ?? "")} ${g.change > 0 ? "+" : "−"}${Math.abs(g.change)}</span>`);
  return `<div class="card-sec"><div class="whys"><b>This building:</b>${parts.join("") || `<span class="why">no effect on moods</span>`}</div>
    <div class="whys"><b>Score:</b><span class="why ${br.scoreImpact >= 0 ? "love" : "hate"}">${br.scoreImpact >= 0 ? "+" : "−"}${Math.abs(br.scoreImpact)} compared with an empty lot</span></div></div>`;
}

/** Route or station status, read from Lean: riders, thresholds, and whether Lean flagged it. */
function routeDetails(i: number, r: EvalReply | null): string {
  const pr = st.pr!;
  const rr = r?.report.routes[i];
  if (!rr || !rr.on) return "";
  const name = pr.puzzle.routes[i].name;
  const flagged = (r?.problems ?? []).filter((p) => p.includes(name));
  return `<div class="card-sec"><div class="whys"><b>Riders:</b>${rr.riders} a day (needs ${pr.numbers.minRouteRiders})</div>
    ${rr.newRiders !== undefined ? `<div class="whys"><b>New riders:</b>${rr.newRiders}${pr.numbers.minNewRiders !== undefined ? ` (needs ${pr.numbers.minNewRiders})` : ""}</div>` : ""}
    ${flagged.length ? flagged.map((p) => `<div class="flag bad">${esc(p)}</div>`).join("") : `<div class="flag ok">This route runs fine</div>`}</div>`;
}

function stationDetails(r: EvalReply | null): string {
  if (!r || shownSolution().station === null) return "";
  const flagged = r.problems.filter((p) => /station|subway|metro/i.test(p));
  return `<div class="card-sec"><div class="whys"><b>Riders:</b>${r.report.stationRiders} a day (needs ${st.pr!.numbers.minStationRiders})</div>
    ${flagged.length ? flagged.map((p) => `<div class="flag bad">${esc(p)}</div>`).join("") : `<div class="flag ok">The station runs fine</div>`}</div>`;
}

/** What a building type does, for the tray tooltip. Facts only. */
function buildingInfo(kind: Kind): string {
  const pr = st.pr!;
  const opts = pr.options.filter((o) => o.building.kind === kind).sort((a, b) => a.building.stories - b.building.stories);
  const rows = opts.map((o) => `<div class="ti-row"><span>${hasFloors(kind) ? floorsText(o.building) : KIND_NAME[kind]}</span><span>${money(o.cost)}</span><span>${o.residents ? `${o.residents} residents` : o.jobs ? `${o.jobs} jobs` : "&nbsp;"}</span></div>`).join("");
  const factors: { f: string; note: string }[] = [];
  if (kind === "park") factors.push({ f: "parks", note: "a park on or next to a home" });
  if (kind === "bar") factors.push({ f: "nightlife", note: "a bar on or next to a home" }, { f: "quiet", note: "a bar next door breaks the quiet" });
  if (kind === "shop") factors.push({ f: "shops", note: "a shop on or next to a home; shops count by their customers" });
  if (kind === "food") factors.push({ f: "food", note: "lunch for workers nearby, dinner for residents" });
  if (opts.some((o) => o.jobs > 0)) factors.push({ f: "shortCommute", note: "jobs close to homes mean short trips" }, { f: "walkability", note: "work, shops and a park within walking distance" });
  if (opts.some((o) => o.building.stories >= 3)) factors.push({ f: "quiet", note: "a 3-floor building next door breaks the quiet" });
  const who = (f: string) => {
    const love = pr.puzzle.groups.filter((g) => g.cares.includes(f)).map((g) => `${esc(g.name)} love it`);
    const hate = pr.puzzle.groups.filter((g) => g.hates.includes(f)).map((g) => `${esc(g.name)} dislike it`);
    return [...love, ...hate].join(", ");
  };
  const fx = factors.map(({ f, note }) => `<div class="ti-fx">${FACTOR_ICON[f] ?? ""}<span><b>${FACTOR[f]?.name ?? f}</b>: ${note}${who(f) ? `. ${who(f)}.` : "."}</span></div>`).join("");
  return `<div class="ti-title">${KIND_NAME[kind]}</div>${rows}${fx ? `<div class="ti-sep"></div>${fx}` : ""}`;
}

/** The postcard's "Why this rating": the parts of the score, and the biggest drag in plain words. */
function whyRating(r: EvalReply): string {
  const rep = r.report;
  const pz = st.pr!.puzzle;
  let drag = "";
  if (!r.valid) drag = r.problems[0] ? `A rule isn't met: ${r.problems[0]}` : "A rule isn't met.";
  else {
    const worst = (rep.blocks ?? []).filter((b) => b.scoreImpact < 0).sort((a, b) => a.scoreImpact - b.scoreImpact)[0];
    const unhappy = (rep.residents ?? []).filter((x) => x.unhappy).reduce((a, x) => a + x.people, 0);
    if (worst) drag = `The ${KIND_NAME[shownSolution().build[worst.block].kind].toLowerCase()} on block ${worst.block + 1} lowers the score by ${-worst.scoreImpact}.`;
    else if (rep.crimePenalty > 0) drag = `Crime costs ${rep.crimePenalty} points.`;
    else if (rep.shortage > 0) drag = `${rep.shortage} jobs have no one living nearby to fill them.`;
    else if (unhappy > 0) drag = `${unhappy} residents are unhappy.`;
  }
  void pz;
  const row = (k: string, v: string, neg = false) => `<div class="why-row ${neg ? "neg" : ""}"><span>${k}</span><b>${v}</b></div>`;
  return `<details class="why-rating"><summary>Why this rating</summary>
    ${row("Happiness", rep.happiness.toLocaleString())}
    ${row("Jobs filled", rep.productivity.toLocaleString())}
    ${row("Crime penalty", rep.crimePenalty ? `−${rep.crimePenalty}` : "0", rep.crimePenalty > 0)}
    ${row("Housing shortage", String(rep.shortage), rep.shortage > 0)}
    ${row("Score", `${r.score.toLocaleString()}${r.rating ? ` of ${r.rating.bestScore.toLocaleString()} possible` : ""}`)}
    ${drag ? `<div class="drag">${esc(drag)}</div>` : ""}</details>`;
}

// ---------- hover card ----------

let cardTarget: Target | null = null;
let hideTimer = 0;
let mouse = { x: 0, y: 0 };

function renderCard(t: Target) {
  const pr = st.pr!;
  const nb = pr.numbers;
  const s = shownSolution();
  let html = "";
  if (t.kind === "block") {
    const b = s.build[t.i];
    const fixed = !!pr.puzzle.fixed[t.i];
    const cost = costOf(b);
    if (b.kind === "empty") {
      const tool = st.tool && st.tool !== "subway" && st.tool !== "bridge" && st.tool !== "empty" ? st.tool : null;
      html = `<div class="card-title">Open lot</div>
        <div class="card-sub">${tool ? `Click to build ${KIND_NAME[tool].toLowerCase()} here` : "Pick a building below, then click here"}</div>`;
    } else {
      const hs = heights(b.kind);
      const at = hs.findIndex((h) => sameB(h, b));
      const canUp = canEdit() && !fixed && at >= 0 && at + 1 < hs.length;
      const canDown = canEdit() && !fixed;
      html = `<div class="card-row"><div><div class="card-title">${KIND_NAME[b.kind]}</div>
          <div class="card-sub">${hasFloors(b.kind) ? floorsText(b) : ""}${cost !== undefined ? `${hasFloors(b.kind) ? ", " : ""}${money(cost)}` : ""}</div></div>
          ${fixed ? `<span class="ribbon">Already built</span>` : `<span class="steppers">
            <button class="step" data-act="up" ${canUp ? "" : "disabled"} title="Raise">${ICON.up()}</button>
            <button class="step" data-act="down" ${canDown ? "" : "disabled"} title="Lower">${ICON.down()}</button></span>`}</div>`;
      const r = shownReply();
      const here = (r?.report.residents ?? []).filter((x) => x.block === t.i);
      if (here.length) html += `<div class="card-people">${here.map((x) => `<span class="who">${ICON.avatar(groupColor(x.group), AVATAR_FUR[x.group % AVATAR_FUR.length], x.group % 2 ? "scarf" : "tie")}${x.people}
          <i>${x.unhappy ? ICON.cloud() : ICON.heart()}</i></span>`).join("")}</div>`;
      if (lens === "mood") html += moodDetails(t.i, r);
      if (lens === "jobs" || (lens === "none" && b.kind !== "housing")) html += jobDetails(t.i, r);
      html += impactDetails(t.i, r);
      if (!fixed && canEdit()) html += `<div class="card-hint">Left-click raise, right-click lower</div>`;
    }
  } else if (t.kind === "bridge") {
    const on = drawnBridges()[t.i];
    const [a, b] = world.bridgeBlocks(t.i);
    html = `<div class="card-row"><span class="card-ic">${ICON.bridge()}</span><div>
        <div class="card-title">${on ? "Bridge" : "A bridge could go here"}</div>
        <div class="card-sub">${nb.bridgeCost !== undefined ? money(nb.bridgeCost) : ""}${a !== undefined ? `${nb.bridgeCost !== undefined ? ", " : ""}joins blocks ${a + 1} and ${b + 1}` : ""}</div></div></div>
      <div class="card-hint">Blocks across the river only count as neighbors when a bridge joins them.${canEdit() ? ` Click to ${on ? "remove" : "build"} it.` : ""}</div>`;
  } else if (t.kind === "site") {
    const built = s.station === t.i;
    html = `<div class="card-row"><span class="card-ic">${ICON.subway(SUBWAY_COLOR)}</span><div>
        <div class="card-title">${built ? "Metro station" : "A metro station could go here"}</div>
        <div class="card-sub">${money(nb.stationCost)}, needs ${nb.minStationRiders} riders a day</div></div></div>
      ${stationDetails(shownReply())}
      ${canEdit() ? `<button class="btn small" data-act="${built ? "unstation" : "station"}" data-site="${t.i}">${built ? "Remove station" : "Build station here"}</button>` : ""}`;
  } else {
    const r = pr.puzzle.routes[t.i];
    const on = s.routesOn[t.i];
    html = `<div class="card-row"><span class="card-ic">${ICON.bus(ROUTE_COLORS[t.i % ROUTE_COLORS.length])}</span><div>
        <div class="card-title">${esc(r.name)} bus</div>
        <div class="card-sub">${money(nb.routeCost)}, needs ${nb.minRouteRiders} riders a day</div></div></div>
      ${world.transit?.routeBlocked(t.i) ? `<div class="flag bad">This route crosses the river. It can't run until a bridge is built there.</div>` : ""}
      ${routeDetails(t.i, shownReply())}
      <div class="card-hint">${canEdit() ? `Click the route to turn it ${on ? "off" : "on"}` : on ? "Running" : "Not running"}</div>`;
  }
  setHTML("card", html);
}

function placeCard() {
  if (!cardTarget) return;
  const el = $("card");
  const p = cardTarget.kind === "route" ? { x: mouse.x, y: mouse.y - 18 } : world.screenOf(cardTarget);
  if (!p) return;
  const w = el.offsetWidth, h = el.offsetHeight;
  const W = window.innerWidth, H = window.innerHeight;
  // try above the block, below it, then to either side; the card must not cover the block
  // itself (clicks go there) or the HUD panels. With neighbor arcs showing, below goes first.
  const fit = (x: number, y: number) => ({ x: Math.max(12, Math.min(W - w - 12, x)), y: Math.max(12, Math.min(H - h - 130, y)) });
  const above = fit(p.x - w / 2, p.y - h - 14), under = fit(p.x - w / 2, p.y + 46);
  const right = fit(p.x + 60, p.y - h / 2), left = fit(p.x - w - 60, p.y - h / 2);
  const below = links.length > 0 && cardTarget.kind === "block";
  const farRight = fit(p.x + 200, p.y - h / 2), farLeft = fit(p.x - w - 200, p.y - h / 2), high = fit(p.x - w / 2, p.y - h - 160);
  const order = below ? [under, right, left, above, farRight, farLeft, high] : [above, under, right, left, farRight, farLeft, high];
  const panels = ["town", "meter", "postcard", "lenses"].map((id) => $(id)).filter((e) => !e.classList.contains("hidden") && e.offsetWidth).map((e) => e.getBoundingClientRect());
  // neighbor arc labels must stay visible too
  const labels = links.map((l) => world.linkLabelAt(l.from, l.to, l.tone === "work" ? 0.28 : 0.5)).filter((q): q is { x: number; y: number } => !!q);
  const hits = (c: { x: number; y: number }) =>
    panels.some((r) => c.x < r.right && c.x + w > r.left && c.y < r.bottom && c.y + h > r.top) ||
    labels.some((q) => q.x > c.x - 40 && q.x < c.x + w + 40 && q.y > c.y - 20 && q.y < c.y + h + 20) ||
    (p.x > c.x - 30 && p.x < c.x + w + 30 && p.y + 20 > c.y - 30 && p.y + 20 < c.y + h + 30);
  const { x, y } = order.find((c) => !hits(c)) ?? order[0];
  el.style.transform = `translate(${Math.round(x)}px, ${Math.round(y)}px)`;
}

function showCard(t: Target | null) {
  clearTimeout(hideTimer);
  if (!t) { hideTimer = window.setTimeout(hideCard, 260); return; }
  if (!st.pr) return;
  cardTarget = t;
  renderCard(t);
  $("card").classList.remove("hidden");
  placeCard();
}
function hideCard() { cardTarget = null; $("card").classList.add("hidden"); }

// ---------- neighbors: who affects whom (hover) ----------

/** What a building next door gives a home, in Lean's factor names. */
function gives(b: Building): string[] {
  const f: string[] = [];
  if (b.kind === "park") f.push("parks");
  if (b.kind === "bar") f.push("nightlife");
  if (b.kind === "shop") f.push("shops");
  if (b.kind === "food") f.push("food");
  return f;
}
/** Does a building next door take away a home's quiet (a bar, or 3 floors and up)? */
const breaksQuiet = (b: Building) => b.kind === "bar" || (b.kind !== "empty" && b.kind !== "park" && b.stories >= 3);

interface LinkInfo { from: number; to: number; tone: Link["tone"]; html: string; tip: string }
let links: LinkInfo[] = [];

/**
 * How block `src` affects the cats living on home block `home`. Everything is read from Lean:
 * which factors the residents there have (`has`), what their group and type love or dislike,
 * and how many of them there are. Nothing is scored here.
 */
function effectOn(home: number, src: number): LinkInfo | null {
  const r = shownReply();
  const pz = st.pr!.puzzle;
  const here = (r?.report.residents ?? []).filter((x) => x.block === home);
  if (!here.length) return null;
  const b = st.build[src];
  let love = 0, hate = 0;
  const icons = new Set<string>();
  const tastes = (x: Resident) => {
    const g = pz.groups[x.group], ty = x.type !== undefined ? g.types?.[x.type] : undefined;
    return { cares: ty ? ty.cares : g.cares, hates: ty ? ty.hates : g.hates };
  };
  for (const f of gives(b)) for (const x of here) {
    if (!x.has.includes(f)) continue;
    const t = tastes(x);
    if (t.cares.includes(f)) { love += x.people; icons.add(f); }
    if (t.hates.includes(f)) { hate += x.people; icons.add(f); }
  }
  if (breaksQuiet(b)) for (const x of here) {
    if (x.has.includes("quiet")) continue;
    const t = tastes(x);
    if (t.cares.includes("quiet")) { hate += x.people; icons.add("quiet"); }
    if (t.hates.includes("quiet")) { love += x.people; icons.add("quiet"); }
  }
  if (!love && !hate) return { from: src, to: home, tone: "none", html: `<span class="lk none">no effect</span>`, tip: `The ${KIND_NAME[b.kind].toLowerCase()} next door doesn't change how these cats feel` };
  const tone: Link["tone"] = love && hate ? "mixed" : love ? "good" : "bad";
  const name = KIND_NAME[b.kind].toLowerCase();
  const tip = [love ? `${love} cats here like the ${name} next door` : "", hate ? `${hate} dislike it` : ""].filter(Boolean).join(", ");
  const html = `<span class="lk ${tone}">${[...icons].map((f) => FACTOR_ICON[f] ?? "").join("")}${love ? `<b class="plus">+${love}</b>` : ""}${hate ? `<b class="minus">−${hate}</b>` : ""}</span>`;
  return { from: src, to: home, tone, html, tip };
}

/** Commuters from Lean's trips: home → workplace. */
function commuteLinks(i: number): LinkInfo[] {
  const r = shownReply();
  const by = new Map<string, number>();
  for (const t of r?.report.trips ?? []) {
    if (t.fromBlock === null || t.toBlock === null || t.fromBlock === undefined || t.toBlock === undefined || t.fromBlock === t.toBlock) continue;
    if (t.fromBlock !== i && t.toBlock !== i) continue;
    if (st.build[t.toBlock]?.kind !== "office") continue;
    const k = `${t.fromBlock}>${t.toBlock}`;
    by.set(k, (by.get(k) ?? 0) + t.people);
  }
  return [...by.entries()].map(([k, n]) => {
    const [a, b] = k.split(">").map(Number);
    return { from: a, to: b, tone: "work" as const, html: `<span class="lk work">${ICON.work()}<b>${n}</b></span>`, tip: `${n} cats commute from here to work${b === i ? " here" : ""}` };
  });
}

/**
 * How block `src` changes block `dst`'s value, from Lean: `blocks[src].neighbors` holds, for each
 * neighbor, its value with `src` empty minus its value now, so the effect of `src` is −change.
 */
function pointsEffect(src: number, dst: number): number | null {
  const br = shownReply()?.report.blocks?.find((b) => b.block === src);
  const n = br?.neighbors?.find((x) => x.block === dst);
  return n ? -n.change : null;
}

function showLinks(t: Target | null) {
  links = [];
  if (t?.kind === "block" && st.pr) {
    const i = t.i, b = st.build[i];
    const blocks = shownReply()?.report.blocks;
    if (b && b.kind !== "empty" && blocks?.some((x) => x.neighbors)) {
      // Lean's own numbers: what each built neighbor does to this block's value, in points
      const nb = blocks.find((x) => x.block === i)?.neighbors?.map((x) => x.block) ?? world.linkedNeighbors(i);
      for (const j of nb) {
        if (st.build[j]?.kind === "empty") continue;
        const pts = pointsEffect(j, i);
        if (pts === null) continue;
        const cats = b.kind === "housing" ? effectOn(i, j) : null;
        const tone: Link["tone"] = pts > 0 ? "good" : pts < 0 ? "bad" : "none";
        const name = KIND_NAME[st.build[j].kind].toLowerCase();
        const catNote = cats && cats.tone !== "none" ? ` <small class="lk-cats">${cats.html.replace(/<\/?span[^>]*>/g, "")}</small>` : "";
        const html = pts === 0 ? `<span class="lk none">no effect</span>` : `<span class="lk ${tone}"><b class="${pts > 0 ? "plus" : "minus"}">${pts > 0 ? "+" : "−"}${Math.abs(pts)}</b>${catNote}</span>`;
        const tip = pts === 0 ? `The ${name} next door doesn't change this block's score` : `The ${name} next door ${pts > 0 ? "adds" : "takes away"} ${Math.abs(pts)} points here${cats && cats.tip ? `. ${cats.tip}` : ""}`;
        links.push({ from: j, to: i, tone, html, tip });
      }
      links.push(...commuteLinks(i));
    } else if (b && b.kind !== "empty") {
      const nb = world.linkedNeighbors(i);
      if (b.kind === "housing") for (const j of nb) { if (st.build[j]?.kind === "empty") continue; const l = effectOn(i, j); if (l) links.push(l); }
      else for (const j of nb) if (st.build[j]?.kind === "housing") { const l = effectOn(j, i); if (l) links.push(l); }
      links.push(...commuteLinks(i));
    }
  }
  world.setLinks(links.length ? links.map((l) => ({ from: l.from, to: l.to, tone: l.tone })) : null);
  setHTML("links", links.map((l, k) => `<div class="badge" data-k="${k}" data-tip="${esc(l.tip)}">${l.html}</div>`).join(""));
}

function placeLinks() {
  document.querySelectorAll<HTMLElement>("#links .badge").forEach((el) => {
    const l = links[Number(el.dataset.k)];
    // commute labels sit nearer the home end, so they never sit on top of a neighbor label on the same arc
    const p = l ? world.linkLabelAt(l.from, l.to, l.tone === "work" ? 0.28 : 0.5) : null;
    if (!p) { el.style.display = "none"; return; }
    el.style.display = "";
    el.style.transform = `translate(${Math.round(p.x)}px, ${Math.round(p.y)}px) translate(-50%, -50%)`;
  });
}

// ---------- the day clock (Lean's simulated day) ----------

const PHASE_NAME = ["Morning commute", "Lunch", "Evening out", "Home for the night"];
let clockPhase = -1;
function tickClock() {
  const c = world.transit?.dayClock() ?? null;
  const el = $("dayclock");
  if (!c || document.body.classList.contains("titling")) { if (!el.classList.contains("hidden")) el.classList.add("hidden"); clockPhase = -1; return; }
  el.classList.remove("hidden");
  if (c.phase !== clockPhase) {
    clockPhase = c.phase;
    el.innerHTML = `<span class="dc-ic">${c.phase >= 2 ? ICON.moon() : ICON.sun()}</span><span class="dc-name">${PHASE_NAME[c.phase]}</span>
      <span class="dc-steps">${PHASE_NAME.map((_n, k) => `<i class="${k < c.phase ? "done" : k === c.phase ? "now" : ""}"><s></s></i>`).join("")}</span>`;
    el.dataset.tip = "A day in this town";
  }
  const now = el.querySelector<HTMLElement>(".dc-steps i.now s");
  if (now) now.style.width = `${Math.round(c.u * 100)}%`;
}
void Transit;

// ---------- coach marks, tooltip, toast ----------

function coach() {
  const el = $("coach");
  const done = Number(localStorage.getItem("sb-coach") ?? "0");
  let step = done;
  if (step === 0 && st.tool) step = 1;
  if (step <= 1 && edits > 0) step = 2;
  if (step !== done) localStorage.setItem("sb-coach", String(step));
  const msgs = ["Pick a building", "Click a block to build. Right-click lowers.", "Press Build to see how residents feel"];
  if (step >= 3 || !canEdit() || new URLSearchParams(location.search).has("nocoach")) { el.classList.add("hidden"); return; }
  el.className = `coach step${step}`;
  el.innerHTML = `<span class="coach-n">${step + 1}/3</span>${msgs[step]}`;
}

let tipEl: HTMLDivElement | null = null;
document.addEventListener("mouseover", (e) => {
  const t = (e.target as HTMLElement).closest<HTMLElement>("[data-tip],[data-info]");
  if (!t || !(t.dataset.tip || t.dataset.info) || !st.pr) { tipEl?.remove(); tipEl = null; return; }
  if (!tipEl) { tipEl = document.createElement("div"); document.body.appendChild(tipEl); }
  tipEl.className = t.dataset.info ? "tip rich" : "tip";
  if (t.dataset.info) tipEl.innerHTML = buildingInfo(t.dataset.info as Kind);
  else tipEl.textContent = t.dataset.tip!;
  const r = t.getBoundingClientRect();
  const w = tipEl.offsetWidth;
  const below = r.top < 160;
  tipEl.style.left = `${Math.max(8, Math.min(window.innerWidth - w - 8, r.left + r.width / 2 - w / 2))}px`;
  tipEl.style.top = below ? `${r.bottom + 8}px` : `${r.top - tipEl.offsetHeight - 8}px`;
});

let toastTimer = 0;
function toast(msg: string) {
  const el = $("toast");
  el.textContent = msg;
  el.classList.remove("hidden");
  clearTimeout(toastTimer);
  toastTimer = window.setTimeout(() => el.classList.add("hidden"), 1600);
}

// ---------- events ----------

world.onClick = (t0, button) => {
  if (!st.pr) return;
  if (!t0) return;
  // with a building picked, a click on a faint station entrance builds on its block instead
  const t: Target = t0.kind === "site" && st.tool && st.tool !== "subway" && st.tool !== "bridge" ? { kind: "block", i: t0.i } : t0;
  if (t.kind === "bridge" && button === 0) toggleBridge(t.i);
  if (t.kind === "block" && st.tool === "bridge") return;
  if (t.kind === "block") editBlock(t.i, button === 0, true);
  else if (t.kind === "route" && button === 0) toggleRoute(t.i);
  else if (t.kind === "site" && button === 0) setStation(shownSolution().station === t.i ? null : t.i);
  if (cardTarget) renderCard(cardTarget);
};
world.onHover = (t) => { showCard(t); showLinks(t); };
// double-click focuses a block, unless it's one you're editing (clicks there build/raise)
world.onDouble = (t) => {
  if (t?.kind !== "block") { world.recenter(); return; }
  if (!canEdit() || st.pr!.puzzle.fixed[t.i]) world.focusSmooth(t.i);
};
let lastMeterH = 0;
function layoutRight() {
  const h = $("meter").offsetHeight;
  if (h === lastMeterH) return;
  lastMeterH = h;
  document.documentElement.style.setProperty("--lens-top", `${18 + h + 8}px`);
  document.documentElement.style.setProperty("--pc-top", `${18 + h + 8 + 52 + 8}px`);
}
world.onFrame = () => { layoutRight(); placeCard(); placeBadges(); placeLinks(); tickClock(); };
window.addEventListener("pointermove", (e) => { mouse = { x: e.clientX, y: e.clientY }; });
$("card").addEventListener("pointerenter", () => clearTimeout(hideTimer));
$("card").addEventListener("pointerleave", () => { hideTimer = window.setTimeout(hideCard, 200); });

document.addEventListener("click", (e) => {
  const t = (e.target as HTMLElement).closest<HTMLElement>("[data-tool],[data-route],[data-act],[data-lens],[data-size],[data-pick]");
  if (!t) return;
  if (t.dataset.pick) { void playNew(t.dataset.pick as Size); return; }
  switch (t.dataset.act) {
    case "start": showScreen("size"); return;
    case "rules": showScreen("rules"); return;
    case "home": showScreen("home"); return;
    case "go": hideIntro(); return;
    case "title": location.href = urlWith({ seed: null, size: null }); return;
    case "new": void playNew(pickSize); return;
  }
  if (t.dataset.size) { pickSize = t.dataset.size as Size; lastHTML.delete("town"); renderTown(); return; }
  if (t.dataset.lens) { lens = t.dataset.lens as Lens; updateLens(); if (cardTarget) renderCard(cardTarget); }
  else if (t.dataset.tool) pickTool(t.dataset.tool as Tool);
  else if (t.dataset.route) toggleRoute(Number(t.dataset.route));
  else switch (t.dataset.act) {
    case "keep": keepBuilding(); break;
    case "recenter": world.recenter(); break;
    case "close-pc": st.postcardOpen = false; render(); break;
    case "up": if (cardTarget?.kind === "block") editBlock(cardTarget.i, true, false); break;
    case "down": if (cardTarget?.kind === "block") editBlock(cardTarget.i, false, false); break;
    case "station": setStation(Number(t.dataset.site)); break;
    case "unstation": setStation(null); break;
  }
  if (cardTarget) renderCard(cardTarget);
});
$("build").addEventListener("click", () => (st.mode === "edit" ? void build() : keepBuilding()));
window.addEventListener("keydown", (e) => { if (e.key === "Escape") { st.tool = null; render(); } });

void C;
// Test hook for the screenshot script (?test): block screen positions.
if (new URLSearchParams(location.search).has("test")) {
  (window as unknown as { __sb: unknown }).__sb = {
    info: () => ({ ...world.renderer.info.render, ...world.renderer.info.memory, programs: world.renderer.info.programs?.length }),
    cam: () => ({ t: world.cam.cur.target.toArray().map((x) => +x.toFixed(2)), d: +world.cam.cur.dist.toFixed(2), az: +world.cam.cur.az.toFixed(2), p: +world.cam.cur.polar.toFixed(2) }),
    focus: (i: number) => world.focus(i),
    low: (elev?: number, d?: number) => world.lowAngle(elev, d),
    edge: (i: number, d?: number, e?: number) => world.aimEdge(i, d, e),
    propLook: (kind: "beer" | "cig", d: number, e: number) => { const p = world.transit?.propSpots(kind)[0]; if (p) world.lookAt(p, d, e); return !!p; },
    counts: () => { const tr = world.transit as unknown as Record<string, { count: number }>; return { cigs: tr.cigs.count, beers: tr.beers.count, puffs: tr.puffs.count, dust: tr.dust.count }; },
    cigAt: () => { const tr = world.transit as unknown as Record<string, THREE.InstancedMesh>; const mm = new THREE.Matrix4(); tr.cigs.getMatrixAt(0, mm); const v = new THREE.Vector3().setFromMatrixPosition(mm); const pp = new THREE.Vector3(); tr.puffs.getMatrixAt(0, mm); pp.setFromMatrixPosition(mm); const sc = world.project({ x: v.x, y: -v.z }, v.y); const sp2 = world.project({ x: pp.x, y: -pp.z }, pp.y); return { scr: sc, pscr: sp2, cig: v.toArray(), puff: pp.toArray(), cam: world.camera.position.toArray(), vis: tr.cigs.visible, parent: !!tr.cigs.parent?.parent }; },
    crimeLook: (ci: number, d: number, e: number) => { const c = world.transit?.crimeAt[ci]; if (c) world.lookAt(c.p, d, e); return c ? { u: +c.u.toFixed(1), ko: c.ko } : null; },
    blocked: () => (st.pr?.puzzle.routes ?? []).map((_r, i) => !!world.transit?.routeBlocked(i)),
    lookBridge: (i: number, d: number, e: number) => { const p = world.bridgeMid(i); if (p) world.lookAt(p, d, e); },
    dbgRiver: () => { const tr = world.transit as unknown as { stream: Set<number>; bridged: Set<number>; routeNodes: number[][]; segIndex: Map<string, number> }; return { stream: [...tr.stream], bridged: [...tr.bridged], sites: st.pr!.puzzle.bridgeSites, routes: tr.routeNodes, bridges: st.bridges }; },
    setAllBridges: (on: boolean) => { st.bridges = st.bridges.map(() => on); world.setBridges(st.bridges); render(); void refreshLive(); },
    bridgeSites: () => (st.pr?.puzzle.bridgeSites ?? []).map((_s, i) => ({ i, p: world.screenOf({ kind: "bridge", i }) })),
    lookBlock: (i: number, d: number, e: number) => world.lookAt(world.centerOf(i), d, e),
    far: () => world.titleView(),
    zoom: (k: number) => world.cam.set(world.cam.goal.target, world.cam.goal.dist * k, world.cam.goal.az, world.cam.goal.polar),
    recenter: () => world.recenter(),
    setAll: (kind: Kind, stories: number) => { st.build = st.build.map(() => ({ kind, stories })); world.setBuild(st.build, st.station); void refreshLive(); },
    day: () => world.transit?.dayClock() ?? null,
    bridgeWalk: (i: number) => world.bridgeWalk(i),
    busOnBridge: () => !!world.transit?.busOnBridge(),
    demoWalk: (i: number) => world.transit?.demoWalk([world.edgePath(i)]),
    lens: (l: Lens) => { lens = l; updateLens(); },
    sites: () => (st.pr?.puzzle.stationSites ?? []).map((i) => ({ i, p: world.screenOf({ kind: "site", i }) })),
    blocks: () => st.build.map((_b, i) => ({ i, fixed: !!st.pr?.puzzle.fixed[i], kind: st.build[i].kind, p: world.screenOf({ kind: "block", i }) })),
  };
}
void boot();
