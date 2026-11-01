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
import type { Building, EvalReply, Kind, Personality, PuzzleReply, Resident, Solution } from "./types";
import { World, type Feeling, type Target } from "./world";
import type { CrimeSpot, Cue, IdleMode } from "./transit";
import type { V2 } from "./geom";

const $ = <T extends HTMLElement = HTMLElement>(id: string) => document.getElementById(id) as T;

type Tool = Kind | "subway" | null;

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
const hasFloors = (k: string) => k === "housing" || k === "office" || k === "shop";
const floorsText = (b: Building) => `${b.stories} ${b.stories === 1 ? "floor" : "floors"}`;
const plural = (g: string) => g;

/** Set innerHTML only when it changed, so buttons aren't replaced mid-click. */
const lastHTML = new Map<string, string>();
function setHTML(id: string, html: string) {
  if (lastHTML.get(id) !== html) { $(id).innerHTML = html; lastHTML.set(id, html); }
}

function solution(): Solution {
  const s: Solution = { build: st.build, routesOn: st.routesOn, station: st.station };
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
  pz.bridgeSites = best.slice(0, 2);
  pr.numbers.bridgeCost = 90;
  const T = [
    [{ name: "Gardeners", share: 50, cares: ["parks"], hates: [] }, { name: "Bookworms", share: 30, cares: ["quiet"], hates: ["nightlife"] }, { name: "Shoppers", share: 20, cares: ["shops"], hates: [] }],
    [{ name: "Night owls", share: 60, cares: ["nightlife"], hates: [] }, { name: "Commuters", share: 40, cares: ["transit"], hates: [] }],
  ];
  pz.groups.forEach((g, i) => { g.types = T[i % T.length]; });
}
/** In mock mode, give each resident entry a personality so the mood hover can group by it. */
function mockTypes(r: EvalReply) {
  if (!MOCK) return r;
  for (const x of r.report.residents ?? []) x.type = (x.block + x.group) % (st.pr!.puzzle.groups[x.group].types?.length ?? 1);
  return r;
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

const wantedSeed = (() => {
  const s = new URLSearchParams(location.search).get("seed");
  return s !== null && /^\d+$/.test(s) ? Number(s) : null;
})();

/** Old Harbor (the demo), or a newly generated neighborhood if `?seed=N` asks for it. */
async function loadPuzzle(): Promise<PuzzleReply> {
  if (wantedSeed === null) return engine.demo();
  const current = await engine.puzzle();
  if (current.puzzle.name === `Neighborhood #${wantedSeed}`) return current;
  for (let seed = wantedSeed, tries = 0; tries < 3; seed++, tries++) {
    $("loading-text").textContent = "Planning a brand-new neighborhood…";
    const g = await engine.newPuzzle(seed);
    if (g.generated && g.puzzle) {
      if (seed !== wantedSeed) history.replaceState(null, "", `?seed=${seed}`);
      return g.puzzle;
    }
  }
  throw new Error("Couldn't plan a neighborhood this time");
}

async function start() {
  try {
    const pr = await loadPuzzle();
    if (MOCK) mockPuzzle(pr);
    st.pr = pr;
    const pz = pr.puzzle;
    st.bridges = (pz.bridgeSites ?? []).map(() => false);
    st.build = pz.fixed.map((f) => f ?? emptyB());
    st.routesOn = pz.routes.map(() => false);
    world.load(pr);
    document.body.dataset.setting = world.setting;
    thumbs = renderThumbs(kinds());
    world.setBuild(st.build, st.station, true);
    world.transit?.setRoutes(st.routesOn);
    world.setBridges(st.bridges);
    if (world.transit) world.transit.typeCues = pz.groups.map((g) => (g.types ?? []).map((t) => ({ cue: cueOf(t), share: t.share })));
    renderTown();
    render();
    coach();
    $("loading").classList.add("gone");
    void refreshLive();
  } catch (e) {
    $("loading-text").textContent = `${(e as Error).message}. Retrying…`;
    setTimeout(start, 2500);
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

function showLife(r: EvalReply | null) {
  const s = shownSolution();
  world.setFeelings(feelingsFrom(r));
  world.transit?.setTrips(r?.report.trips ?? null);
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
  const tool = useTool && st.tool && st.tool !== "subway" ? st.tool : null;
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
  world.transit?.setStation(s);
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
    setTimeout(() => { showLife(r); countUp(r.rating?.rating ?? 0); if ((r.rating?.rating ?? 0) >= 100) world.heartBurst(); }, 700);
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
  const open = s.build.map((_b, i) => (canEdit() && st.tool && st.tool !== "subway" && !st.pr!.puzzle.fixed[i] ? i : -1)).filter((i) => i >= 0);
  world.setGlow(open);
  world.transit?.setShowSites(canEdit() && (st.tool === "subway" || st.station === null));
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
  setHTML("town", `<div class="town-head"><h1>${esc(pz.name)}</h1>
      <button class="icon-btn" data-act="new" title="Try a new neighborhood">${ICON.dice()}</button></div>
    <p class="goal">Make your residents happy and keep the town busy, within budget.</p>
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
    <div class="ring-cap">${rated === null ? (st.mode === "built" ? "Lean is rating…" : "Build to see your rating") : rated >= 100 ? "A perfect neighborhood" : "Your rating"}</div>
    <div class="bars">
      <div class="bar-row" data-tip="Total happiness of your residents (from Lean)">${ICON.heart()}<span class="bar-val">${r ? r.report.happiness.toLocaleString() : "0"}</span><span class="bar-label">happiness</span></div>
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
    const price = money(opts[0].cost);
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
  const bus = pr.puzzle.routes.map((r, i) => `<button class="tile small ${routes[i] ? "on" : ""}" data-route="${i}" ${editing ? "" : "disabled"}
      data-tip="${esc(r.name)} bus: ${money(nb.routeCost)}. It needs ${nb.minRouteRiders}+ riders a day, ${nb.minNewRiders}+ of them new. Click to turn it ${routes[i] ? "off" : "on"}.">
      <span class="tile-icon">${ICON.bus(ROUTE_COLORS[i % ROUTE_COLORS.length])}</span><span class="tile-name">${esc(r.name)}</span><span class="led"></span></button>`).join("");
  const sub = pr.puzzle.stationSites.length ? `<button class="tile small ${station !== null ? "on" : ""} ${st.tool === "subway" ? "picked" : ""}" data-tool="subway" ${editing ? "" : "disabled"}
      data-tip="Subway station: ${money(nb.stationCost)}. It needs ${nb.minStationRiders}+ riders a day. Pick it, then click a faint entrance on the map.">
      <span class="tile-icon">${ICON.subway(SUBWAY_COLOR)}</span><span class="tile-name">Subway</span><span class="led"></span></button>` : "";
  setHTML("transit", bus + sub);
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
  if (!show) return;
  if (!r) { setHTML("postcard", `<div class="pc-wait">Lean is rating your neighborhood…</div>`); return; }
  const rating = r.rating?.rating ?? 0;
  const { headline, notes } = notesFrom(r);
  const stars = [50, 80, 100].map((th) => `<span class="star big">${ICON.star(rating >= th)}</span>`).join("");
  setHTML("postcard", `
    <div class="pc-stamp">${rating >= 100 ? "A perfect neighborhood!" : rating >= 80 ? "What a lovely place" : rating >= 50 ? "A cozy start" : rating > 0 ? "Room to grow" : "Not quite working yet"}</div>
    <div class="pc-stars">${stars}</div>
    <div class="pc-sub">Rated ${rating} out of 100. A 100 means no plan can do better, and Lean has proved it.</div>
    <div class="pc-head">${esc(headline)}</div>
    <ul class="pc-notes">${notes.map((n) => `<li><span class="pc-ic">${n.icon}</span><span>${esc(n.text)}</span></li>`).join("")}</ul>
    <div class="pc-facts">
      <span data-tip="Happiness of all residents">${ICON.heart()} ${r.report.happiness.toLocaleString()}</span>
      <span data-tip="Jobs filled, minus crime">${ICON.briefcase()} ${r.report.productivity.toLocaleString()}</span>
    </div>
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
    ${flagged.length ? flagged.map((p) => `<div class="flag bad">${esc(p)}</div>`).join("") : `<div class="flag ok">Lean found no problem with this route</div>`}</div>`;
}

function stationDetails(r: EvalReply | null): string {
  if (!r || shownSolution().station === null) return "";
  const flagged = r.problems.filter((p) => /station|subway/i.test(p));
  return `<div class="card-sec"><div class="whys"><b>Riders:</b>${r.report.stationRiders} a day (needs ${st.pr!.numbers.minStationRiders})</div>
    ${flagged.length ? flagged.map((p) => `<div class="flag bad">${esc(p)}</div>`).join("") : `<div class="flag ok">Lean found no problem with the station</div>`}</div>`;
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
  return `<details class="why-rating" open><summary>Why this rating</summary>
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
      const tool = st.tool && st.tool !== "subway" && st.tool !== "empty" ? st.tool : null;
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
        <div class="card-title">${built ? "Subway station" : "A subway station could go here"}</div>
        <div class="card-sub">${money(nb.stationCost)}, needs ${nb.minStationRiders} riders a day</div></div></div>
      ${stationDetails(shownReply())}
      ${canEdit() ? `<button class="btn small" data-act="${built ? "unstation" : "station"}" data-site="${t.i}">${built ? "Remove station" : "Build station here"}</button>` : ""}`;
  } else {
    const r = pr.puzzle.routes[t.i];
    const on = s.routesOn[t.i];
    html = `<div class="card-row"><span class="card-ic">${ICON.bus(ROUTE_COLORS[t.i % ROUTE_COLORS.length])}</span><div>
        <div class="card-title">${esc(r.name)} bus</div>
        <div class="card-sub">${money(nb.routeCost)}, needs ${nb.minRouteRiders} riders a day</div></div></div>
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
  const x = Math.max(12, Math.min(window.innerWidth - w - 12, p.x - w / 2));
  let y = Math.max(12, Math.min(window.innerHeight - h - 130, p.y - h - 14));
  // never sit on top of the HUD panels
  for (const id of ["town", "meter", "postcard"]) {
    const r = $(id).getBoundingClientRect();
    if (!r.width || $(id).classList.contains("hidden")) continue;
    if (x < r.right && x + w > r.left && y < r.bottom && y + h > r.top) y = r.bottom + 10;
  }
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

world.onClick = (t, button) => {
  if (!st.pr) return;
  if (!t) return;
  if (t.kind === "bridge" && button === 0) toggleBridge(t.i);
  if (t.kind === "block") editBlock(t.i, button === 0, true);
  else if (t.kind === "route" && button === 0) toggleRoute(t.i);
  else if (t.kind === "site" && button === 0) setStation(shownSolution().station === t.i ? null : t.i);
  if (cardTarget) renderCard(cardTarget);
};
world.onHover = (t) => showCard(t);
// double-click focuses a block, unless it's one you're editing (clicks there build/raise)
world.onDouble = (t) => {
  if (t?.kind !== "block") { world.recenter(); return; }
  if (!canEdit() || st.pr!.puzzle.fixed[t.i]) world.focusSmooth(t.i);
};
world.onFrame = () => { placeCard(); placeBadges(); };
window.addEventListener("pointermove", (e) => { mouse = { x: e.clientX, y: e.clientY }; });
$("card").addEventListener("pointerenter", () => clearTimeout(hideTimer));
$("card").addEventListener("pointerleave", () => { hideTimer = window.setTimeout(hideCard, 200); });

document.addEventListener("click", (e) => {
  const t = (e.target as HTMLElement).closest<HTMLElement>("[data-tool],[data-route],[data-act],[data-lens]");
  if (!t) return;
  if (t.dataset.lens) { lens = t.dataset.lens as Lens; updateLens(); if (cardTarget) renderCard(cardTarget); }
  else if (t.dataset.tool) pickTool(t.dataset.tool as Tool);
  else if (t.dataset.route) toggleRoute(Number(t.dataset.route));
  else switch (t.dataset.act) {
    case "new": location.search = `?seed=${Math.floor(Math.random() * 100000)}`; break;
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
    bridgeSites: () => (st.pr?.puzzle.bridgeSites ?? []).map((_s, i) => ({ i, p: world.screenOf({ kind: "bridge", i }) })),
    lookBlock: (i: number, d: number, e: number) => world.lookAt(world.centerOf(i), d, e),
    demoWalk: (i: number) => world.transit?.demoWalk([world.edgePath(i)]),
    lens: (l: Lens) => { lens = l; updateLens(); },
    sites: () => (st.pr?.puzzle.stationSites ?? []).map((i) => ({ i, p: world.screenOf({ kind: "site", i }) })),
    blocks: () => st.build.map((_b, i) => ({ i, fixed: !!st.pr?.puzzle.fixed[i], kind: st.build[i].kind, p: world.screenOf({ kind: "block", i }) })),
  };
}
coach();
void start();
