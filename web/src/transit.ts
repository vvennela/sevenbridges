// Bus routes, buses, subway entrances, and the little residents walking around.
// Which trips happen, by which mode and how many people, comes from Lean's
// report. The street path each resident follows is chosen here for looks only.
import * as THREE from "three";
import { mergeGeometries, mergeVertices } from "three/examples/jsm/utils/BufferGeometryUtils.js";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { TILE_TOP } from "./buildings";
import { add, along, dist, mul, norm, polylineLength, sub, v2, type V2 } from "./geom";
import { C, ROUTE_COLORS, SUBWAY_COLOR, groupColor } from "./palette";
import { Rng } from "./rng";
import type { Route, Segment, Trip } from "./types";

interface Leg { pts: V2[]; L: number; speed: number; visible: boolean }
/** A 1960s office outfit (looks only). */
interface Outfit { suit: THREE.Color; dress: boolean; hat: 0 | 1 | 2; briefcase: boolean; kid: boolean; burglar?: boolean; loot?: boolean; cue?: Cue }
/** A small personality cue on a cat (from what its personality loves). */
export type Cue = "moon" | "leaf" | "book" | "bag" | "ticket" | "star" | null;
const CUE_COLORS: Record<string, string> = { moon: "#FFD54A", leaf: "#5FBF6A", bag: "#FF8B7B", ticket: "#6FC3E8", star: "#F5A93E" };
/** A troubled block where cartoon burglars show up (rate from Lean's data). */
export interface CrimeSpot { ring: V2[]; every: number; forceKO: boolean; group: number }
interface Walker { demo?: boolean; legs: Leg[]; T: number; phase: number; lane: number; car: boolean; color: THREE.Color; coat: Coat; fit: Outfit }
interface Coat { fur: THREE.Color; patch: THREE.Color }
export type IdleMode = "stroll" | "sit" | "wave" | "nap" | "groom" | "fight";
interface Idler { c: V2; r: number; speed: number; phase: number; mode: IdleMode; ang: number; color: THREE.Color; coat: Coat; fit: Outfit; prop: Prop; fightEvery: number }
type Prop = "cig" | "beer" | null;
interface Bus { obj: THREE.Group; route: number; phase: number }

const MAX_PEOPLE = 700, MAX_CARS = 120, MAX_PROPS = 80, MAX_PUFFS = 120, MAX_DUST = 80;
const CAR_COLORS = ["#FF8B7B", "#9CCAF4", "#9FE2C6", "#CDB6F3", "#FFE19A", "#F7A8C8"];

export class Transit {
  private group = new THREE.Group();
  private adj: { to: number; w: number; seg: number }[][];
  private segIndex = new Map<string, number>();
  /** River segments, and the ones with a built bridge. */
  private stream = new Set<number>();
  private bridged = new Set<number>();
  private routeNodes: number[][] = [];
  private routeLane: number[] = [];
  private routeGaps: boolean[][] = [];
  private blockedAt: (V2 | null)[] = [];
  private needSigns: THREE.Sprite[] = [];
  private routeMeshes: THREE.Mesh[] = [];
  private ribbonOf: ((wid: number) => void)[] = [];
  private lastWidth: number[] = [];
  private segEnds: [V2, V2][] = [];
  private widths: number[] = [];
  private routeHits: THREE.Mesh[] = [];
  private routePaths: V2[][] = [];
  private stops: THREE.Group[] = [];
  private buses: Bus[] = [];
  private routesOn: boolean[] = [];
  private hoverRoute: number | null = null;
  private sites = new Map<number, { ghost: THREE.Group; real: THREE.Group; hit: THREE.Mesh }>();
  private hoverSite: number | null = null;
  private walkers: Walker[] = [];
  private idlers: Idler[] = [];
  private bodies: THREE.InstancedMesh;
  private heads: THREE.InstancedMesh;
  private cars: THREE.InstancedMesh;
  private cabins: THREE.InstancedMesh;
  private eyes: THREE.InstancedMesh;
  private cheeks: THREE.InstancedMesh;
  private outline: THREE.InstancedMesh;
  private geoLo!: CatGeos;
  private geoHi!: CatGeos;
  private lod: [THREE.InstancedMesh, GeoKey][] = [];
  private near = false;
  /** Camera orientation, so smoke puffs face the viewer. */
  camQuat = new THREE.Quaternion();
  camPos = new THREE.Vector3();
  /** Swap to the smooth, high-detail cats when the camera is close (with hysteresis, so zooming doesn't flicker). */
  setDetail(dist: number, radius: number) {
    const near = this.near ? dist < radius * 2.15 : dist < radius * 1.75;
    if (near === this.near) return;
    this.near = near;
    const G = near ? this.geoHi : this.geoLo;
    for (const [im, key] of this.lod) im.geometry = G[key];
  }
  private legs!: THREE.InstancedMesh;
  private shoes!: THREE.InstancedMesh;
  /** Ground height under a plan point (set by the world). */
  private baseGround: (p: V2) => number = () => 0.02;
  get groundAt(): (p: V2) => number { return (p) => this.bridgeHeight(p) ?? this.baseGround(p); }
  set groundAt(f: (p: V2) => number) { this.baseGround = f; }
  private cigs!: THREE.InstancedMesh;
  private beers!: THREE.InstancedMesh;
  private puffs!: THREE.InstancedMesh;
  private dust!: THREE.InstancedMesh;
  private stars!: THREE.InstancedMesh;
  private cussSprites: THREE.Sprite[] = [];
  private cussShown: THREE.Vector3[] = [];
  private arms!: THREE.InstancedMesh;
  private wear!: Record<"jacket" | "shirt" | "tie" | "scarf" | "skirt" | "fedora" | "band" | "pillbox" | "briefcase" | "stripes" | "mask" | "cap" | "sack" | "pin" | "book", THREE.InstancedMesh>;
  private ghosts!: THREE.InstancedMesh;
  private halos!: THREE.InstancedMesh;
  private lootSprites: THREE.Sprite[] = [];
  private alarmSprites: THREE.Sprite[] = [];
  private crimes: CrimeSpot[] = [];
  /** Debug: where each crime scene is right now (screenshots aim at it). */
  crimeAt: { p: V2; u: number; ko: boolean }[] = [];
  private ghostN = 0;
  private lootShown: THREE.Vector3[] = [];
  private alarmShown: THREE.Vector3[] = [];
  private station: number | null = null;
  private showSites = true;

  constructor(
    scene: THREE.Scene,
    private pts: V2[],
    segs: Segment[],
    private blockCorners: number[][],
    private blockCenters: V2[],
    private outer: V2[],
    private routes: Route[],
    private stationSpots: Map<number, V2>,
    private seed: number,
  ) {
    scene.add(this.group);
    this.adj = pts.map(() => []);
    segs.forEach((s, si) => {
      const w = dist(pts[s.a], pts[s.b]);
      this.adj[s.a].push({ to: s.b, w, seg: si });
      this.adj[s.b].push({ to: s.a, w, seg: si });
      this.segIndex.set(segKey(s.a, s.b), si);
      this.segEnds[si] = [pts[s.a], pts[s.b]];
      if (s.terrain === "stream") this.stream.add(si);
    });
    routes.forEach((r, i) => this.makeRoute(r, i));
    for (const [b, p] of stationSpots) this.makeSite(b, p);

    // little upright cats (looks only): chibi proportions, a big head, a tail, two legs and two arms.
    // Two detail levels share the same instanced meshes: low-poly far away, smooth up close.
    this.geoLo = catGeometries(5);
    this.geoHi = catGeometries(14);
    const G = this.geoLo;
    const ramp = new THREE.DataTexture(new Uint8Array([168, 168, 168, 255, 222, 222, 222, 255, 255, 255, 255, 255]), 3, 1);
    ramp.minFilter = ramp.magFilter = THREE.NearestFilter;
    ramp.needsUpdate = true;
    const mat = new THREE.MeshToonMaterial({ gradientMap: ramp });
    const solid = (c: string) => new THREE.MeshToonMaterial({ gradientMap: ramp, color: col(c) });
    // hats: smooth shading, no toon banding
    const hatMat = new THREE.MeshStandardMaterial({ roughness: 0.7 });
    const mk = (key: GeoKey, material: THREE.Material, n = MAX_PEOPLE) => { const im = new THREE.InstancedMesh(G[key], material, n); this.lod.push([im, key]); return im; };
    this.bodies = mk("fur", mat);
    this.outline = mk("hull", new THREE.MeshBasicMaterial({ color: col("#3A4466"), side: THREE.BackSide }));
    this.heads = mk("patch", mat);
    this.eyes = mk("face", new THREE.MeshBasicMaterial({ color: col("#2E3A59") }));
    this.cheeks = mk("pink", new THREE.MeshBasicMaterial({ color: col("#FF9FB0") }));
    const carGeo = new THREE.BoxGeometry(0.34, 0.11, 0.18).translate(0, 0.085, 0);
    const cabGeo = new THREE.BoxGeometry(0.18, 0.09, 0.16).translate(-0.02, 0.18, 0);
    this.cars = new THREE.InstancedMesh(carGeo, new THREE.MeshStandardMaterial({ roughness: 0.6 }), MAX_CARS);
    this.cabins = new THREE.InstancedMesh(cabGeo, new THREE.MeshStandardMaterial({ color: col("#F4F8FF"), roughness: 0.5 }), MAX_CARS);
    // limbs: instanced, posed per frame from the hip/shoulder
    this.legs = mk("leg", mat, MAX_PEOPLE * 2);
    this.arms = mk("arm", mat, MAX_PEOPLE * 2);
    this.shoes = mk("shoe", mat, MAX_PEOPLE * 2);
    // 1960s office wear (and the cartoon burglar's)
    this.wear = {
      jacket: mk("jacket", mat), shirt: mk("shirt", solid("#FFFFFF")), tie: mk("tie", mat), scarf: mk("scarf", mat), skirt: mk("skirt", mat),
      fedora: mk("fedora", hatMat), band: mk("band", hatMat), pillbox: mk("pillbox", hatMat), briefcase: mk("briefcase", solid("#8A5A3B")),
      stripes: mk("stripes", solid("#FFFFFF")), mask: mk("mask", solid("#1E2233")), cap: mk("cap", new THREE.MeshStandardMaterial({ color: col("#3A3F4B"), roughness: 0.75 })), sack: mk("sack", solid("#D9C29A")), pin: mk("pin", mat), book: mk("book", solid("#8E5A9B")),
    };
    // ghosts (a cartoon knockout): a pale see-through cat with a halo
    this.ghosts = mk("fur", new THREE.MeshBasicMaterial({ color: col("#FFFFFF"), transparent: true, opacity: 0.55, depthWrite: false }), 8);
    this.halos = new THREE.InstancedMesh(new THREE.TorusGeometry(0.08, 0.014, 6, 18).rotateX(Math.PI / 2).translate(0, 0.66, 0).scale(0.98, 0.98, 0.98), new THREE.MeshBasicMaterial({ color: col("#FFD54A") }), 8);
    for (const m of [this.ghosts, this.halos]) { m.count = 0; m.frustumCulled = false; this.group.add(m); }
    for (let k = 0; k < 6; k++) { const s = textSprite("$", "#3B7D3A"); s.visible = false; this.lootSprites.push(s); this.group.add(s); }
    for (let k = 0; k < 6; k++) { const s = textSprite("!", "#D9604C"); s.visible = false; this.alarmSprites.push(s); this.group.add(s); }
    // props: a cigarette (paper, filter, glowing ember), a glass beer mug with foam, soft smoke puffs
    this.cigs = mk("cig", new THREE.MeshBasicMaterial({ vertexColors: true, toneMapped: false }), MAX_PROPS);
    this.beers = mk("mug", new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.22, metalness: 0.05 }), MAX_PROPS);
    this.puffs = new THREE.InstancedMesh(new THREE.PlaneGeometry(2, 2), new THREE.MeshBasicMaterial({ map: softDot(), color: col("#E3E6EC"), transparent: true, opacity: 0.8, depthWrite: false }), MAX_PUFFS);
    this.puffs.renderOrder = 5;
    this.dust = new THREE.InstancedMesh(new THREE.IcosahedronGeometry(1, 1), new THREE.MeshToonMaterial({ gradientMap: ramp, color: col("#F1E8D6") }), MAX_DUST);
    const starShape = new THREE.Shape();
    for (let k = 0; k < 10; k++) { const a = (k / 10) * Math.PI * 2, r = k % 2 ? 0.45 : 1; k ? starShape.lineTo(Math.sin(a) * r, Math.cos(a) * r) : starShape.moveTo(0, r); }
    this.stars = new THREE.InstancedMesh(new THREE.ExtrudeGeometry(starShape, { depth: 0.3, bevelEnabled: false }).center(), new THREE.MeshBasicMaterial({ color: col("#FFC83D") }), MAX_DUST);
    for (let k = 0; k < 4; k++) { const s = cussSprite(); s.visible = false; this.cussSprites.push(s); this.group.add(s); }
    for (const m of [this.cigs, this.beers, this.puffs, this.dust, this.stars]) { m.count = 0; m.frustumCulled = false; this.group.add(m); }
    for (const m of [...Object.values(this.wear), this.legs, this.arms, this.shoes]) { m.count = 0; m.frustumCulled = false; m.castShadow = true; this.group.add(m); }
    for (const m of [this.bodies, this.heads, this.cars, this.cabins, this.eyes, this.cheeks, this.outline]) {
      m.count = 0; m.frustumCulled = false; m.castShadow = true;
      this.group.add(m);
    }
  }

  // ---------- routes ----------

  private makeRoute(r: Route, i: number) {
    const n = this.routes.length;
    const lane = (i - (n - 1) / 2) * 0.2;
    const path0 = offsetPolyline(r.path.map((k) => this.pts[k]), lane);
    this.routePaths.push(path0);
    this.routeNodes.push(r.path);
    this.routeLane.push(lane);
    const sign = textSprite("!", "#2A7BC0");
    sign.scale.set(0.34, 0.34, 1);
    sign.visible = false;
    this.needSigns.push(sign);
    this.group.add(sign);
    const color = ROUTE_COLORS[i % ROUTE_COLORS.length];
    const ribbon = (wid: number, y: number) => {
      const m = new GB();
      const c = col("#ffffff");
      const path = this.routePaths[i], gaps = this.routeGaps[i] ?? [];
      for (let k = 1; k < path.length; k++) {
        if (gaps[k]) continue; // a gap where the route meets unbridged water
        const a = path[k - 1], b = path[k];
        const d = norm(sub(b, a)), nn = v2(-d.y * wid, d.x * wid);
        m.quad(w3(add(a, nn), y), w3(add(b, nn), y), w3(sub(b, nn), y), w3(sub(a, nn), y), c, [0, 1, 0]);
      }
      for (const [pk, p] of path.entries()) {
        if (gaps[pk] && gaps[pk + 1]) continue;
        const ring: ReturnType<typeof w3>[] = [];
        for (let k = 0; k < 12; k++) { const t = (k / 12) * Math.PI * 2; ring.push(w3(add(p, v2(Math.cos(t) * wid, Math.sin(t) * wid)), y)); }
        m.poly(ring, c, [0, 1, 0]);
      }
      return m.build();
    };
    const mat = new THREE.MeshBasicMaterial({ color: col(color), transparent: true, opacity: 0.3, depthWrite: false });
    const mesh = new THREE.Mesh(ribbon(0.085, 0.06 + i * 0.002), mat);
    this.ribbonOf.push((wid: number) => { mesh.geometry.dispose(); mesh.geometry = ribbon(wid, 0.06 + i * 0.002); });
    mesh.renderOrder = 2;
    this.routeMeshes.push(mesh);
    this.group.add(mesh);
    const hit = new THREE.Mesh(ribbon(0.24, 0.07), new THREE.MeshBasicMaterial({ visible: false }));
    hit.userData.route = i;
    this.routeHits.push(hit);
    this.group.add(hit);

    // bus stops: a post with a round sign in the route color, at every other corner
    const stops = new THREE.Group();
    const sm = new GB();
    const path = path0;
    const wet = (k: number) => [k - 1, k + 1].some((j) => { const si = this.segIndex.get(segKey(r.path[k], r.path[j] ?? -1)); return si !== undefined && this.stream.has(si); });
    path.forEach((p, k) => {
      if ((k % 2 !== 0 && k !== path.length - 1) || wet(k)) return; // no bus stop standing in the river
      const d = norm(sub(path[Math.min(path.length - 1, k + 1)], path[Math.max(0, k - 1)]));
      const q = add(p, mul(v2(-d.y, d.x), 0.3 * (i % 2 ? -1 : 1)));
      sm.geom(SHAPES.cyl, trs(q.x, 0.3, -q.y, 0.018, 0.6, 0.018), col("#F4F4F8"));
      sm.geom(SHAPES.cyl, trs(q.x, 0.62, -q.y, 0.09, 0.03, 0.09), col(color));
    });
    const stopMesh = new THREE.Mesh(sm.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.6 }));
    stopMesh.castShadow = true;
    stops.add(stopMesh);
    stops.visible = false;
    this.stops.push(stops);
    this.group.add(stops);

    for (let k = 0; k < 2; k++) {
      const bus = busMesh(color);
      bus.visible = false;
      this.group.add(bus);
      this.buses.push({ obj: bus, route: i, phase: k * 0.5 + i * 0.17 });
    }
  }

  setRoutes(on: boolean[]) {
    this.routesOn = on;
    this.refreshRoutes();
  }

  /** Ribbon width per route (the transit lens thickens busy routes). */
  setRouteWidths(w: number[]) {
    this.lastWidth = [...w];
    w.forEach((x, i) => { if (this.widths[i] !== x) { this.widths[i] = x; this.ribbonOf[i]?.(x); } });
  }

  /** Middle point of a route's path (for labels). */
  routeMid(i: number): V2 | null { const p = this.routePaths[i]; return p ? along(p, polylineLength(p) / 2).at : null; }

  setHoverRoute(i: number | null) { this.hoverRoute = i; this.refreshRoutes(); }

  private refreshRoutes() {
    this.routeMeshes.forEach((m, i) => {
      const mat = m.material as THREE.MeshBasicMaterial;
      mat.opacity = this.routesOn[i] ? 0.95 : i === this.hoverRoute ? 0.7 : 0.28;
    });
    this.stops.forEach((s, i) => { s.visible = !!this.routesOn[i] || i === this.hoverRoute; });
    for (const b of this.buses) b.obj.visible = !!this.routesOn[b.route] && !this.blockedAt[b.route];
    this.needSigns.forEach((s, i) => {
      const at = this.blockedAt[i];
      s.visible = !!at && (!!this.routesOn[i] || i === this.hoverRoute);
      if (at) s.position.set(at.x, 0.55, -at.y);
    });
  }

  /** Is a street segment usable (not river, or river with a built bridge)? */
  private passable(seg: number) { return !this.stream.has(seg) || this.bridged.has(seg); }
  /** Can this route run? (Lean also reports it as a problem when it can't.) */
  routeBlocked(i: number): boolean { return !!this.blockedAt[i]; }

  /** Which river segments have a built bridge. Routes over unbridged water stop, and get a gap and a sign. */
  setBridged(segs: number[]) {
    this.bridged = new Set(segs);
    this.routeNodes.forEach((nodes, i) => {
      let at: V2 | null = null;
      const pts: V2[] = [], gaps: boolean[] = [];
      nodes.forEach((k, j) => {
        if (j > 0) {
          const si = this.segIndex.get(segKey(nodes[j - 1], k));
          if (si !== undefined && this.stream.has(si)) {
            if (this.bridged.has(si)) { pts.pop(); gaps.pop(); for (const q of detour(this.pts[nodes[j - 1]], this.pts[k])) { pts.push(q); gaps.push(false); } return; }
            else { if (!at) at = mid2(this.pts[nodes[j - 1]], this.pts[k]); pts.push(this.pts[k]); gaps.push(true); return; }
          }
        }
        pts.push(this.pts[k]); gaps.push(false);
      });
      this.routePaths[i] = offsetPolyline(pts, this.routeLane[i]);
      this.routeGaps[i] = gaps;
      this.blockedAt[i] = at;
      this.widths[i] = -1; // force the ribbon to rebuild with (or without) its gap
    });
    this.setRouteWidths(this.routeNodes.map((_n, i) => this.lastWidth[i] ?? 0.085));
    this.refreshRoutes();
  }

  /** Deck height when standing on a built bridge (it arches along the segment), or null. */
  bridgeHeight(p: V2): number | null {
    for (const si of this.bridged) {
      const sg = this.segEnds[si];
      if (!sg) continue;
      const { mid, d, n } = crossing(sg[0], sg[1]);
      const across = (p.x - mid.x) * n.x + (p.y - mid.y) * n.y, along2 = (p.x - mid.x) * d.x + (p.y - mid.y) * d.y;
      if (Math.abs(across) > BRIDGE_SPAN / 2 || Math.abs(along2) > BRIDGE_W / 2) continue;
      return bridgeY(across / BRIDGE_SPAN + 0.5);
    }
    return null;
  }

  /** Street nodes to points; a leg along a bridged river segment detours bank-to-bank over the bridge. */
  private nodePoints(nodes: number[]): V2[] {
    const out: V2[] = [];
    nodes.forEach((k, j) => {
      if (j > 0) {
        const si = this.segIndex.get(segKey(nodes[j - 1], k));
        if (si !== undefined && this.stream.has(si) && this.bridged.has(si)) { out.pop(); out.push(...detour(this.pts[nodes[j - 1]], this.pts[k])); return; }
      }
      out.push(this.pts[k]);
    });
    return out;
  }

  /** Objects to raycast for route clicks. */
  get routeTargets(): THREE.Object3D[] { return this.routeHits; }

  // ---------- subway ----------

  private makeSite(block: number, p: V2) {
    const real = kioskMesh(false);
    const ghost = kioskMesh(true);
    for (const k of [real, ghost]) { k.position.set(p.x, TILE_TOP, -p.y); this.group.add(k); }
    real.visible = false;
    const hit = new THREE.Mesh(new THREE.CylinderGeometry(0.42, 0.42, 0.9, 12), new THREE.MeshBasicMaterial({ visible: false }));
    hit.position.set(p.x, TILE_TOP + 0.45, -p.y);
    hit.userData.site = block;
    this.group.add(hit);
    this.sites.set(block, { ghost, real, hit });
  }

  /** Only markers you can see are clickable (the built station, or sites while the Subway tool is picked). */
  get siteTargets(): THREE.Object3D[] { return [...this.sites.values()].filter((s) => s.ghost.visible || s.real.visible).map((s) => s.hit); }

  setStation(block: number | null) { this.station = block; this.refreshSites(); }
  setShowSites(show: boolean) { this.showSites = show; this.refreshSites(); }
  setHoverSite(b: number | null) { this.hoverSite = b; this.refreshSites(); }

  private refreshSites() {
    for (const [b, s] of this.sites) {
      s.real.visible = b === this.station;
      s.ghost.visible = b !== this.station && this.showSites;
      s.ghost.traverse((o) => {
        if (o instanceof THREE.Mesh && o.userData.fade !== false) (o.material as THREE.MeshStandardMaterial).opacity = b === this.hoverSite ? 0.9 : 0.5;
      });
    }
  }

  // ---------- residents ----------

  /** Personality cues per group, with shares (from puzzle.groups[g].types). */
  typeCues: { cue: Cue; share: number }[][] = [];
  private pickCue(g: number, rng: Rng): Cue {
    const ts = this.typeCues[g];
    if (!ts?.length) return null;
    let r = rng.next() * ts.reduce((s, x) => s + x.share, 0);
    for (const x of ts) { if (r < x.share) return x.cue; r -= x.share; }
    return ts[ts.length - 1].cue;
  }

  /** Groups whose kittens tag along (any group whose name suggests families). */
  kidGroups = new Set<number>();

  /** Debug: where idlers with a prop stand. */
  propSpots(kind: "beer" | "cig"): V2[] {
    const im = kind === "cig" ? this.cigs : this.beers;
    if (!im.count) return [];
    const mm = new THREE.Matrix4(); im.getMatrixAt(0, mm);
    const v = new THREE.Vector3().setFromMatrixPosition(mm);
    return [v2(v.x, -v.z)];
  }

  /** Debug: cats walking back and forth over a bridge (screenshots). */
  bridgeWalk(seg: number) {
    const sg = this.segEnds[seg];
    if (!sg) return;
    this.demoWalk([detour(sg[0], sg[1]).slice(1, -1)]);
  }
  /** Debug: is any bus on a bridge deck right now? */
  busOnBridge(): boolean { return this.buses.some((b) => b.obj.visible && b.obj.position.y > 0.2); }

  /** Debug (screenshots only): cats pacing back and forth from the road up onto a sidewalk. */
  demoWalk(paths: V2[][]) {
    const rng = new Rng(5);
    for (const pts of paths) for (let k = 0; k < 3; k++) {
      const L = polylineLength(pts);
      const legs: Leg[] = [{ pts, L, speed: 0.35, visible: true }, { pts: [...pts].reverse(), L, speed: 0.35, visible: true }];
      this.walkers.push({ demo: true, legs, T: (2 * L) / 0.35, car: false, phase: k * 1.6, lane: (k - 1) * 0.12, color: col(groupColor(k)), coat: COATS[k * 2], fit: k === 2 ? kidOutfit(rng) : outfit(rng, 0.5) });
    }
  }

  /** Residents walking Lean's trips (null clears them). */
  setTrips(trips: Trip[] | null) {
    this.walkers = [];
    if (!trips) return;
    const rng = new Rng(this.seed ^ 0x7a1);
    trips.forEach((t, ti) => {
      const car = String(t.mode) === "car";
      const n = Math.max(1, Math.min(car ? 3 : 8, Math.round(t.people / (car ? 12 : 4))));
      const offset = rng.range(0, 40) + ti * 1.7;
      const accent = col(groupColor(t.group));
      for (let k = 0; k < n; k++) {
        // each cat leaves from its own spot on the sidewalk, and they leave one after another
        const legs = this.tripLegs(t, rng);
        if (!legs.length) continue;
        const T = legs.reduce((s, l) => s + l.L / l.speed, 0);
        const phase = offset + (k * (T + 3)) / n + rng.range(0, 0.6);
        const lane = car ? 0.1 * (rng.chance(0.5) ? 1 : -1) : rng.range(-0.2, 0.14);
        const coat = rng.pick(COATS);
        this.walkers.push({ legs, T, car, phase, lane, color: car ? col(rng.pick(CAR_COLORS)) : accent, coat, fit: { ...outfit(rng, !car && String(t.mode) !== "walk" ? 0.35 : 0.15), cue: this.pickCue(t.group, rng) } });
        // a kitten walking next to its grown-up
        if (!car && this.kidGroups.has(t.group) && rng.chance(0.5)) {
          this.walkers.push({ legs, T, car, phase, lane: lane + 0.13, color: accent, coat: rng.chance(0.6) ? coat : rng.pick(COATS), fit: kidOutfit(rng) });
        }
      }
    });
  }

  /** Residents idling on their block: strolling the lawn, sitting on benches, napping; kittens play. */
  setIdlers(items: { p: V2; mode: IdleMode; ang: number; group: number; kid?: boolean; beer?: boolean; cig?: boolean; fightEvery?: number; cue?: Cue }[]) {
    const rng = new Rng(this.seed ^ 0x1d1e);
    const expanded: typeof items = [];
    for (const it of items) {
      if (it.mode === "groom" || it.mode === "fight") {
        // a chatting pair, facing each other
        const d = v2(Math.cos(it.ang) * 0.13, Math.sin(it.ang) * 0.13);
        const a1 = Math.atan2(-d.x, d.y), a2 = Math.atan2(d.x, -d.y);
        expanded.push({ ...it, p: add(it.p, d), ang: a1 }, { ...it, p: sub(it.p, d), ang: a2 });
      } else expanded.push(it);
    }
    items = expanded;
    this.idlers = items.slice(0, 180).map((it) => ({
      c: it.p, r: it.mode === "stroll" || it.kid ? rng.range(0.08, 0.18) : 0, speed: (it.kid ? rng.range(0.8, 1.3) : rng.range(0.25, 0.5)) * (rng.chance(0.5) ? 1 : -1),
      phase: rng.range(0, 7), mode: it.kid ? "wave" : it.mode, ang: it.ang, color: col(groupColor(it.group)), coat: rng.pick(COATS),
      fit: it.kid ? kidOutfit(rng) : { ...outfit(rng, 0), cue: it.cue ?? this.pickCue(it.group, rng) },
      // grown-ups only: a beer at the bar, or now and then a cigarette
      prop: (it.kid ? null : it.beer ? "beer" : it.cig ? "cig" : it.mode !== "sit" && it.mode !== "fight" && it.mode !== "wave" && rng.chance(0.13) ? "cig" : null) as Prop,
      fightEvery: it.fightEvery ?? 0,
    }));
  }

  /** Troubled blocks (from Lean's crime, unhappiness and shortage) where burglars show up. */
  setCrime(spots: CrimeSpot[]) { this.crimes = spots; }

  /**
   * Cartoon crime on troubled blocks, along the block's sidewalk ring: a burglar skulks up,
   * snatches a briefcase ("!"), runs, and the victim gives chase. Most end with the burglar
   * getting away or dropping the loot; about 2% end in a cartoon knockout (dust cloud, then a
   * little ghost with a halo floats up and fades). Looks only; how often comes from Lean's data.
   */
  private crimeScenes(t: number, person: (pos: V2, y: number, heading: number, k: number, sway: number, accent: THREE.Color, coat: Coat, fit: Outfit, pose: { swing: number; right?: [number, number]; hidden?: boolean }) => void,
    puff: (x: number, y: number, z: number, s: number, star?: boolean) => void) {
    this.crimes.forEach((c, ci) => {
      const L = polylineLength(c.ring);
      if (L < 2 || c.every <= 0) return;
      const P = c.every;
      const cyc = Math.floor((t + ci * 7.3) / P), u = (t + ci * 7.3) - cyc * P;
      if (u > 14) return; // between incidents: nobody around
      const h = ((cyc * 2654435761 + ci * 97) >>> 0) % 100;
      const ko = c.forceKO ? cyc % 2 === 0 : h < 2;
      const dropped = !ko && h % 3 === 0;
      const s0 = ((cyc * 1.7 + ci) % 1) * L;
      const at = (s: number) => { const a = along(c.ring, ((s % L) + L) % L); return a; };
      const head = (dir: V2) => Math.atan2(dir.x, -dir.y);
      const victimFit: Outfit = { kid: false, dress: cyc % 2 === 1, suit: col(cyc % 2 ? "#8DA2B5" : "#2F3B57"), hat: 1, briefcase: true };
      const burglarFit: Outfit = { kid: false, dress: false, suit: col("#1E2233"), hat: 0, briefcase: false, burglar: true, loot: false };
      const victimCoat = COATS[(cyc + 2) % COATS.length], burglarCoat = COATS[3];
      const accent = col(groupColor(c.group));
      const g = (p: V2) => this.groundAt(p);
      const v3 = (p: V2, y: number) => new THREE.Vector3(p.x, y, -p.y);
      // victim strolls along the ring; burglar skulks up from behind
      const vs = u < 4 ? s0 + u * 0.18 : s0 + 4 * 0.18;
      const va = at(vs);
      this.crimeAt[ci] = { p: ko ? at(vs - 0.1).at : at(vs + Math.max(0, u - 5) * 0.4).at, u, ko };
      if (u < 4) {
        const bs = vs - 1.4 + u * 0.32;
        const ba = at(bs);
        person(va.at, g(va.at), head(va.dir), 1, 0, accent, victimCoat, victimFit, { swing: Math.sin(t * 7) * 0.45 });
        person(ba.at, g(ba.at) - 0.03, head(ba.dir), 1, 0.12, accent, burglarCoat, burglarFit, { swing: Math.sin(t * 5) * 0.3, right: [-0.4, 0.3] });
        return;
      }
      if (u < 5) {
        // the snatch
        person(va.at, g(va.at), head(va.dir) + Math.PI, 1, 0, accent, victimCoat, { ...victimFit, briefcase: false }, { swing: 0, right: [-2.4, 0.4] });
        const ba = at(vs - 0.22);
        person(ba.at, g(ba.at), head(ba.dir), 1, 0, accent, burglarCoat, { ...burglarFit, loot: true }, { swing: 0.2, right: [-0.6, 0.3] });
        this.alarmShown.push(v3(va.at, g(va.at) + 0.85));
        return;
      }
      if (ko && u < 8) {
        // a cartoon tussle: one dust cloud, stars, and then...
        const mid = at(vs - 0.1).at;
        person(va.at, g(va.at), 0, 1, 0, accent, victimCoat, victimFit, { swing: 0, hidden: true });
        for (let j = 0; j < 7; j++) { const a = j * 0.9 + t * 7; puff(mid.x + Math.cos(a) * 0.18, g(mid) + 0.25 + Math.sin(a * 1.3) * 0.08, -mid.y + Math.sin(a) * 0.18, 0.12); }
        for (let j = 0; j < 3; j++) { const a = j * 2.1 + t * 4; puff(mid.x + Math.cos(a) * 0.3, g(mid) + 0.45, -mid.y + Math.sin(a) * 0.3, 0.05, true); }
        if (this.cussShown.length < this.cussSprites.length) this.cussShown.push(v3(mid, g(mid) + 0.75));
        return;
      }
      if (ko) {
        // the burglar runs off with the loot; the victim floats up as a little ghost with a halo
        const w = u - 8;
        const ba = at(vs + w * 0.9);
        if (w < 3) person(ba.at, g(ba.at), head(ba.dir), 1, 0, accent, burglarCoat, { ...burglarFit, loot: true }, { swing: Math.sin(t * 13) * 0.7 });
        if (w < 5 && this.ghostN < 8) {
          const gp = at(vs - 0.1).at;
          const m = new THREE.Matrix4().compose(new THREE.Vector3(gp.x + Math.sin(t * 2) * 0.05, g(gp) + 0.1 + w * 0.35, -gp.y), new THREE.Quaternion().setFromEuler(new THREE.Euler(0, Math.sin(t) * 0.4, Math.sin(t * 2) * 0.1)), new THREE.Vector3(1, 1, 1).multiplyScalar(1 - w / 6));
          this.ghosts.setMatrixAt(this.ghostN, m); this.halos.setMatrixAt(this.ghostN, m); this.ghostN++;
        }
        return;
      }
      // the chase: burglar runs with the sack, victim runs after (or the loot gets dropped)
      const w = u - 5;
      const ba = at(vs + w * 0.85), ca = at(vs + w * 0.7 - 0.25);
      const bLoot = !(dropped && w > 3);
      if (w < 7) person(ba.at, g(ba.at), head(ba.dir), 1, 0, accent, burglarCoat, { ...burglarFit, loot: bLoot }, { swing: Math.sin(t * 13) * 0.75 });
      if (dropped && w > 3) {
        const dp = at(vs + 3 * 0.85).at;
        this.lootShown.push(v3(dp, g(dp) + 0.15));
        const back = Math.min(w - 3, 2.5);
        const vp = at(vs + 3 * 0.7 - 0.25 + (w - 3 < 1.5 ? (w - 3) * 0.7 : 1.05)).at;
        person(vp, g(vp), head(ca.dir), 1, 0, accent, victimCoat, { ...victimFit, briefcase: back > 1.4 }, { swing: back > 1.4 ? 0 : Math.sin(t * 12) * 0.7 });
      } else {
        person(ca.at, g(ca.at), head(ca.dir), 1, 0, accent, victimCoat, { ...victimFit, briefcase: false }, { swing: Math.sin(t * 12) * 0.75, right: [-2.6, 0.3] });
        if (w < 2.5) this.alarmShown.push(v3(ca.at, g(ca.at) + 0.85));
      }
      if (bLoot && w < 7) this.lootShown.push(v3(ba.at, g(ba.at) + 0.72));
    });
  }

  /**
   * A cartoon scuffle between two grown-ups (looks only). How often it happens comes from
   * Lean's data (crime and unhappy neighbors), set by the caller as `fightEvery` seconds.
   * Square up, then a dust cloud with stars and a "#@!", then they storm apart.
   */
  private fight(d: Idler, t: number, y0: number,
    person: (pos: V2, y: number, heading: number, k: number, sway: number, accent: THREE.Color, coat: Coat, fit: Outfit, pose: { swing: number; right?: [number, number]; left?: [number, number]; hidden?: boolean }) => void,
    puff: (x: number, y: number, z: number, s: number, star?: boolean) => void) {
    const period = d.fightEvery > 0 ? d.fightEvery : 1e9;
    const u = ((t + d.phase * 13) % period + period) % period;
    // the pair's middle point: this cat stands at mid + f*0.13, facing -f
    const f = v2(Math.sin(d.ang + Math.PI), -Math.cos(d.ang + Math.PI));
    const midP = add(d.c, mul(f, -0.13));
    if (u < 1.6) {
      // squaring up: lean in, fists raised, little hops
      const hop = Math.abs(Math.sin(t * 9 + d.phase)) * 0.03;
      person(add(d.c, mul(f, -0.03)), y0 + hop, d.ang, 1, Math.sin(t * 6) * 0.08, d.color, d.coat, d.fit, { swing: 0.2, right: [-1.6, 0.3], left: [-1.6, -0.3] });
    } else if (u < 4.2) {
      // the scuffle: both cats vanish into a dust cloud
      person(d.c, y0, d.ang, 1, 0, d.color, d.coat, d.fit, { swing: 0, hidden: true });
      const c3 = new THREE.Vector3(midP.x, y0 + 0.25, -midP.y);
      for (let j = 0; j < 7; j++) {
        const a = j * 0.9 + t * 7;
        puff(c3.x + Math.cos(a) * 0.17, c3.y + Math.sin(a * 1.3) * 0.08, c3.z + Math.sin(a) * 0.17, 0.11 + 0.03 * Math.sin(t * 13 + j));
      }
      for (let j = 0; j < 3; j++) {
        const a = j * 2.1 + t * 4;
        puff(c3.x + Math.cos(a) * 0.3, c3.y + 0.2 + Math.sin(t * 9 + j) * 0.05, c3.z + Math.sin(a) * 0.3, 0.05, true);
      }
      if (d.ang < Math.PI && this.cussShown.length < this.cussSprites.length) this.cussShown.push(c3.clone().setY(c3.y + 0.45));
    } else if (u < 6.5) {
      // storming off in opposite directions
      const w = (u - 4.2) * 0.35;
      person(add(d.c, mul(f, w)), y0, d.ang + Math.PI, 1, 0, d.color, d.coat, d.fit, { swing: Math.sin(t * 12) * 0.6 });
    } else if (u < 7.5) {
      person(add(d.c, mul(f, 0.8)), y0, d.ang + Math.PI, 1, 0, d.color, d.coat, d.fit, { swing: 0, hidden: true });
    } else {
      // back to a calm chat
      person(d.c, y0, d.ang, 1, Math.sin(t * 3 + d.phase) * 0.04, d.color, d.coat, d.fit, { swing: 0.04 * Math.sin(t * 2) });
    }
  }

  private validBlock(b: number | null | undefined): b is number {
    return typeof b === "number" && b >= 0 && b < this.blockCenters.length;
  }

  private tripLegs(t: Trip, rng: Rng): Leg[] {
    const to = this.validBlock(t.toBlock) ? t.toBlock : null;
    if (to === null) return [];
    const mode = String(t.mode);
    const walk = mode === "car" ? 1.5 : 0.5;
    const endAt = this.sidewalkSpot(to, rng);
    const end = endAt.p;
    let start: V2, startNodes: number[];
    if (mode === "subway" && this.station !== null && this.stationSpots.has(this.station)) {
      start = this.stationSpots.get(this.station)!;
      startNodes = this.blockCorners[this.station];
    } else if (this.validBlock(t.fromBlock)) {
      const s = this.sidewalkSpot(t.fromBlock, rng);
      start = s.p;
      startNodes = s.nodes;
    } else {
      start = rng.pick(this.outer);
      startNodes = [this.nearestNode(start)];
    }
    const legs: Leg[] = [];
    const leg = (pts: V2[], speed: number, visible: boolean) => {
      if (pts.length < 2) return;
      const L = polylineLength(pts);
      if (L > 0.01) legs.push({ pts, L, speed, visible });
    };
    let cur = startNodes;
    let at = start;
    if (mode === "bus") {
      for (const r of t.routes) {
        const route = this.routes[r];
        if (!route) continue;
        const board = this.nearestOnRoute(route.path, cur);
        const alight = this.nearestOnRoute(route.path, this.blockCorners[to]);
        const w = [at, ...this.nodePoints(this.streetPath(cur, [route.path[board]]))];
        leg(w, walk, true);
        const ride = this.nodePoints(board <= alight ? route.path.slice(board, alight + 1) : route.path.slice(alight, board + 1).reverse());
        leg(ride, 1.3, false);
        at = this.pts[route.path[alight]];
        cur = [route.path[alight]];
      }
    }
    leg([at, ...this.nodePoints(this.streetPath(cur, endAt.nodes)), end], walk, true);
    return legs;
  }

  /** A random spot on a block's sidewalk, and the two corners of that side. */
  private sidewalkSpot(b: number, rng: Rng): { p: V2; nodes: number[] } {
    const cs = this.blockCorners[b];
    const k = rng.int(0, cs.length - 1);
    const a = this.pts[cs[k]], c = this.pts[cs[(k + 1) % cs.length]];
    const onRoad = add(a, mul(sub(c, a), rng.range(0.2, 0.8)));
    const inward = norm(sub(this.blockCenters[b], onRoad));
    return { p: add(onRoad, mul(inward, 0.5)), nodes: [cs[k], cs[(k + 1) % cs.length]] };
  }

  private nearestNode(p: V2): number {
    let best = 0;
    this.pts.forEach((q, i) => { if (dist(p, q) < dist(p, this.pts[best])) best = i; });
    return best;
  }

  private nearestOnRoute(path: number[], nodes: number[]): number {
    const d = this.dijkstra(nodes).dist;
    let best = 0;
    path.forEach((k, i) => { if (d[k] < d[path[best]]) best = i; });
    return best;
  }

  private dijkstra(src: number[]) {
    const n = this.pts.length;
    const d = new Array<number>(n).fill(Infinity), prev = new Array<number>(n).fill(-1), done = new Array<boolean>(n).fill(false);
    for (const s of src) d[s] = 0;
    for (;;) {
      let u = -1;
      for (let i = 0; i < n; i++) if (!done[i] && d[i] < Infinity && (u < 0 || d[i] < d[u])) u = i;
      if (u < 0) break;
      done[u] = true;
      for (const e of this.adj[u]) if (this.passable(e.seg) && d[u] + e.w < d[e.to]) { d[e.to] = d[u] + e.w; prev[e.to] = u; }
    }
    return { dist: d, prev };
  }

  private streetPath(from: number[], to: number[]): number[] {
    const { dist: d, prev } = this.dijkstra(from);
    let best = to[0];
    for (const k of to) if (d[k] < d[best]) best = k;
    const p: number[] = [];
    for (let v = best; v >= 0; v = prev[v]) p.unshift(v);
    return p;
  }

  // ---------- per frame ----------

  update(t: number) {
    for (const b of this.buses) {
      if (!b.obj.visible) continue;
      const path = this.routePaths[b.route];
      const L = polylineLength(path);
      const v = 1.3, pause = 1.5, run = L / v;
      const P = 2 * run + 2 * pause;
      const u = (((t + b.phase * P) % P) + P) % P;
      let s = 0, back = false;
      if (u < run) s = u * v;
      else if (u < run + pause) s = L;
      else if (u < 2 * run + pause) { s = L - (u - run - pause) * v; back = true; }
      const a = along(path, s);
      const dir = back ? mul(a.dir, -1) : a.dir;
      b.obj.position.set(a.at.x, this.bridgeHeight(a.at) ?? 0.05, -a.at.y);
      b.obj.rotation.y = Math.atan2(dir.y, dir.x);
    }

    const m = new THREE.Matrix4(), q = new THREE.Quaternion(), e = new THREE.Euler(), sc = new THREE.Vector3(), p = new THREE.Vector3();
    const base = new THREE.Matrix4(), lm = new THREE.Matrix4(), tmp = new THREE.Matrix4();
    let np = 0, nc = 0, nl = 0, na = 0, np2 = 0, ncig = 0, nbeer = 0, npuff = 0, ndust = 0, nstar = 0;
    const W = this.wear;
    const n = { jacket: 0, shirt: 0, tie: 0, scarf: 0, skirt: 0, fedora: 0, band: 0, pillbox: 0, briefcase: 0, stripes: 0, mask: 0, cap: 0, sack: 0, pin: 0, book: 0 };
    const put = (key: keyof typeof n, c?: THREE.Color, mat = base) => { const im = W[key]; im.setMatrixAt(n[key], mat); if (c) im.setColorAt(n[key], c); n[key]++; };
    const S = 0.98;
    /** A limb matrix: from the body, at a joint (x, y), swung forward by `rx` and outward by `rz`. */
    const limb = (x: number, y: number, rx: number, rz: number) => {
      tmp.makeRotationFromEuler(e.set(rx, 0, rz, "XYZ"));
      lm.makeTranslation(x * S, y * S, 0).multiply(tmp);
      return lm.premultiply(base);
    };
    type Pose = { swing: number; sit?: boolean; wave?: number; bob?: number; right?: [number, number]; left?: [number, number]; prop?: Prop; hidden?: boolean };
    type Draw = { pos: V2; y: number; heading: number; k: number; sway: number; accent: THREE.Color; coat: Coat; fit: Outfit; pose: Pose; fixed: boolean };
    const queue: Draw[] = [];
    /** Queue a cat; all cats are drawn after a separation pass so they never overlap. */
    const person = (pos: V2, y: number, heading: number, k: number, sway: number, accent: THREE.Color, coat: Coat, fit: Outfit, pose: Pose) => {
      queue.push({ pos: { x: pos.x, y: pos.y }, y, heading, k, sway, accent, coat, fit, pose, fixed: !!pose.sit || !!pose.hidden });
    };
    const drawCat = (pos: V2, y: number, heading: number, k: number, sway: number, accent: THREE.Color, coat: Coat, fit: Outfit, pose: Pose) => {
      if (np >= MAX_PEOPLE || pose.hidden) return;
      if (fit.kid) k *= 0.62;
      e.set(0, heading, sway, "YXZ"); q.setFromEuler(e);
      // feet on the ground: the planted leg's lowest point sits exactly at y
      const swA = Math.min(Math.abs(pose.swing), 1.2);
      const by = pose.sit || OLD_GROUND ? y : y + (0.135 * Math.cos(swA) - 0.12) * S * k;
      base.compose(p.set(pos.x, by, -pos.y), q, sc.set(k, k, k));
      this.bodies.setMatrixAt(np, base); this.bodies.setColorAt(np, coat.fur);
      this.heads.setMatrixAt(np, base); this.heads.setColorAt(np, coat.patch);
      this.eyes.setMatrixAt(np, base); this.cheeks.setMatrixAt(np, base); this.outline.setMatrixAt(np, base);
      np++;
      const sw = pose.swing;
      const trouser = fit.dress ? coat.fur : fit.suit;
      const legA = pose.sit ? -1.45 : sw, legB = pose.sit ? -1.45 : -sw;
      const shoe = fit.kid ? SHOE_KID : fit.dress ? SHOE_F : SHOE_M;
      for (const [x, a] of [[-0.04, legA], [0.04, legB]] as const) {
        const lm2 = limb(x, 0.12, a, 0);
        this.legs.setMatrixAt(nl, lm2); this.legs.setColorAt(nl, fit.kid && !fit.dress ? KID_SHORTS : trouser);
        this.shoes.setMatrixAt(nl, lm2); this.shoes.setColorAt(nl, shoe);
        nl++;
      }
      const armL = pose.sit ? -0.5 : -sw * 0.8, armR = pose.sit ? -0.5 : sw * 0.8;
      const rArm = pose.right ?? [pose.wave !== undefined ? 0 : armR, pose.wave !== undefined ? 2.6 + Math.sin(pose.wave) * 0.35 : 0.18];
      const lArm = pose.left ?? [armL, -0.18];
      const lmL = limb(-0.085, 0.29, lArm[0], lArm[1]).clone();
      this.arms.setMatrixAt(na, lmL); this.arms.setColorAt(na, fit.suit); na++;
      if (fit.cue === "book") put("book", undefined, lmL);
      else if (fit.cue && !fit.kid && !fit.burglar) put("pin", col(CUE_COLORS[fit.cue] ?? "#FFD54A"));
      const rm = limb(0.085, 0.29, rArm[0], rArm[1]).clone();
      this.arms.setMatrixAt(na, rm); this.arms.setColorAt(na, fit.suit); na++;
      if (fit.briefcase && pose.wave === undefined && !pose.sit && !pose.right) put("briefcase", undefined, rm);
      if (pose.prop && np2 < MAX_PROPS) {
        const im = pose.prop === "cig" ? this.cigs : this.beers;
        const k2 = pose.prop === "cig" ? ncig++ : nbeer++;
        im.setMatrixAt(k2, rm);
        if (pose.prop === "cig" && npuff < MAX_PUFFS - 3) {
          // a tiny wisp of smoke rising from the tip
          const tip = new THREE.Vector3(0, -0.26 * S, 0.012 * S).applyMatrix4(rm);
          for (let j = 0; j < 3; j++) {
            const u = ((t * 0.45 + j / 3 + pos.x) % 1 + 1) % 1;
            const s2 = (0.02 + u * 0.05) * (1 - Math.max(0, u - 0.7) / 0.3); // grows, then fades away
            m.compose(p.set(tip.x + Math.sin(u * 6 + j) * 0.05, tip.y + 0.02 + u * 0.4, tip.z + Math.cos(u * 5) * 0.03), this.camQuat, sc.set(s2, s2, s2));
            this.puffs.setMatrixAt(npuff++, m);
          }
        }
        np2++;
      }
      put("jacket", fit.suit);
      if (fit.burglar) { put("stripes"); put("mask"); put("cap"); if (fit.loot) put("sack", undefined, rm); return; }
      if (fit.kid) { if (fit.dress) put("skirt", accent); return; }
      if (fit.dress) { put("skirt", fit.suit); put("scarf", accent); }
      else { put("shirt"); put("tie", accent); }
      if (fit.hat === 1) { put("fedora", fit.suit); put("band", accent); }
      else if (fit.hat === 2) put("pillbox", accent);
    };
    const walkPose = (ph: number, amp = 0.55): Pose => ({ swing: Math.sin(ph) * amp });
    for (const w of this.walkers) {
      const cycle = w.T + 3;
      let u = (t + w.phase) % cycle;
      if (u > w.T) continue;
      let leg: Leg | null = null;
      for (const l of w.legs) { const d = l.L / l.speed; if (u <= d) { leg = l; break; } u -= d; }
      if (!leg || !leg.visible) continue;
      const s = u * leg.speed;
      const at = along(leg.pts, s);
      const side = v2(-at.dir.y, at.dir.x);
      const pos = add(at.at, mul(side, w.lane));
      const k = w.demo ? 1 : Math.min(1, s / 0.25, (leg.L - s) / 0.25);
      const heading = Math.atan2(at.dir.x, -at.dir.y);
      if (w.car) {
        if (nc >= MAX_CARS) continue;
        e.set(0, Math.atan2(at.dir.y, at.dir.x), 0); q.setFromEuler(e);
        m.compose(p.set(pos.x, 0.05, -pos.y), q, sc.set(k, k, k));
        this.cars.setMatrixAt(nc, m); this.cars.setColorAt(nc, w.color);
        this.cabins.setMatrixAt(nc, m);
        nc++;
      } else {
        person(pos, OLD_GROUND ? 0.05 : this.groundAt(pos), heading, k, 0, w.color, w.coat, w.fit, walkPose((t + w.phase) * (w.fit.kid ? 14 : 10)));
      }
    }
    /** Hold the prop at chest height; every few seconds raise it to the mouth (sip / puff). */
    const propPose = (d: Idler, tt: number): Partial<Pose> => {
      if (!d.prop) return {};
      const cyc = (tt * 0.35 + d.phase) % 1;
      const up = cyc > 0.8 ? Math.sin(((cyc - 0.8) / 0.2) * Math.PI) : 0;
      return { right: [-0.9 - up * 1.3, 0.15 + up * 0.25], prop: d.prop };
    };
    const puff = (x: number, y: number, z: number, s: number, star = false) => {
      m.compose(p.set(x, y, z), q.identity(), sc.set(s, s, s));
      if (star) { if (nstar < MAX_DUST) this.stars.setMatrixAt(nstar++, m); }
      else if (ndust < MAX_DUST) this.dust.setMatrixAt(ndust++, m);
    };
    /** Turn an idle cat up to 60° toward the camera, so faces show. */
    const faceCam = (p: V2, ang: number) => {
      const toCam = Math.atan2(this.camPos.x - p.x, -(-this.camPos.z - p.y));
      const diff = Math.atan2(Math.sin(toCam - ang), Math.cos(toCam - ang));
      return ang + Math.max(-1.05, Math.min(1.05, diff));
    };
    for (const d0 of this.idlers) {
      const d = d0.mode === "groom" || d0.mode === "wave" || d0.mode === "nap" ? { ...d0, ang: faceCam(d0.c, d0.ang) } : d0;
      const y0 = this.groundAt(d.c);
      if (d.mode === "stroll" || (d.mode === "wave" && d.r > 0)) {
        // strolling the lawn (kittens chase each other faster)
        const a = d.phase + t * d.speed;
        const pos = add(d.c, v2(Math.cos(a) * d.r, Math.sin(a) * d.r * 0.8));
        const tx = -Math.sin(a) * Math.sign(d.speed), ty = Math.cos(a) * Math.sign(d.speed);
        person(pos, this.groundAt(pos), Math.atan2(tx, -ty), 1, 0, d.color, d.coat, d.fit, { ...walkPose((t + d.phase) * (d.fit.kid ? 15 : 7), d.fit.kid ? 0.7 : 0.45), ...(d.prop ? { right: [-0.9, 0.15] as [number, number], prop: d.prop } : {}) });
      } else if (d.mode === "sit") {
        // sitting upright on the bench seat, facing away from the backrest, legs swinging
        const f = v2(-Math.sin(d.ang), -Math.cos(d.ang));
        const seat = TILE_TOP + 0.155;
        person(add(d.c, mul(f, 0.03)), seat - 0.12 * S * (d.fit.kid ? 0.62 : 1), -d.ang, 1, 0, d.color, d.coat, d.fit, { swing: 0, sit: true });
      } else if (d.mode === "fight") {
        this.fight(d, t, y0, person, puff);
      } else if (d.mode === "groom") {
        // two cats chatting, facing each other, with small nods (and a sip or a puff now and then)
        const nod = Math.sin(t * 3 + d.phase) * 0.04;
        person(d.c, y0, d.ang, 1, nod, d.color, d.coat, d.fit, { swing: 0.05 * Math.sin(t * 2 + d.phase), ...propPose(d, t) });
      } else if (d.mode === "wave") {
        person(d.c, y0, d.ang, 1, 0, d.color, d.coat, d.fit, { swing: 0, wave: t * 8 + d.phase });
      } else {
        // standing and looking around
        person(d.c, y0, d.ang + (d.prop ? 0 : Math.sin(t * 0.7 + d.phase) * 0.8), 1, 0, d.color, d.coat, d.fit, { swing: 0, ...propPose(d, t) });
      }
    }
    this.crimeScenes(t, person, puff);
    // separation: each cat has a small body radius; push overlapping cats apart (spatial hash grid)
    const R0 = 0.11, cell = 0.3;
    const grid = new Map<string, number[]>();
    const key = (x: number, y: number) => `${Math.floor(x / cell)},${Math.floor(y / cell)}`;
    queue.forEach((d, i) => { if (d.pose.hidden) return; const kk = key(d.pos.x, d.pos.y); (grid.get(kk) ?? grid.set(kk, []).get(kk)!).push(i); });
    for (let it = 0; it < 2; it++) {
      for (let i = 0; i < queue.length; i++) {
        const a = queue[i];
        if (a.pose.hidden) continue;
        const ra = R0 * a.k * (a.fit.kid ? 0.62 : 1);
        const cx = Math.floor(a.pos.x / cell), cy = Math.floor(a.pos.y / cell);
        for (let gx = cx - 1; gx <= cx + 1; gx++) for (let gy = cy - 1; gy <= cy + 1; gy++) for (const j of grid.get(`${gx},${gy}`) ?? []) {
          if (j <= i) continue;
          const b = queue[j];
          const rb = R0 * b.k * (b.fit.kid ? 0.62 : 1);
          const dx = b.pos.x - a.pos.x, dy = b.pos.y - a.pos.y, dd = Math.hypot(dx, dy), need = ra + rb;
          if (dd >= need) continue;
          const nx = dd > 1e-4 ? dx / dd : 1, ny = dd > 1e-4 ? dy / dd : 0, push = need - dd;
          const wa = a.fixed ? 0 : b.fixed ? 1 : 0.5, wb = 1 - wa;
          if (a.fixed && b.fixed) continue;
          a.pos.x -= nx * push * wa; a.pos.y -= ny * push * wa;
          b.pos.x += nx * push * wb; b.pos.y += ny * push * wb;
        }
      }
    }
    for (const d of queue) {
      const y = d.fixed ? d.y : d.y + (this.groundAt(d.pos) - d.y) * (Math.abs(d.y - this.groundAt(d.pos)) < 0.1 ? 1 : 0);
      drawCat(d.pos, y, d.heading, d.k, d.sway, d.accent, d.coat, d.fit, d.pose);
    }
    this.legs.count = nl; this.arms.count = na; this.shoes.count = nl;
    this.cigs.count = ncig; this.beers.count = nbeer; this.puffs.count = npuff; this.dust.count = ndust; this.stars.count = nstar;
    for (const im of [this.cigs, this.beers, this.puffs, this.dust, this.stars]) im.instanceMatrix.needsUpdate = true;
    this.ghosts.count = this.ghostN; this.halos.count = this.ghostN; this.ghostN = 0;
    for (const im of [this.ghosts, this.halos]) im.instanceMatrix.needsUpdate = true;
    this.lootSprites.forEach((s, k) => { s.visible = k < this.lootShown.length; if (s.visible) s.position.copy(this.lootShown[k]); });
    this.alarmSprites.forEach((s, k) => { s.visible = k < this.alarmShown.length; if (s.visible) s.position.copy(this.alarmShown[k]); });
    this.lootShown = []; this.alarmShown = [];
    for (const [k, s] of this.cussSprites.entries()) s.visible = k < this.cussShown.length;
    this.cussShown.forEach((v, k) => { const s = this.cussSprites[k]; if (s) { s.position.copy(v); } });
    this.cussShown = [];
    for (const im of [this.legs, this.arms, this.shoes]) { im.instanceMatrix.needsUpdate = true; if (im.instanceColor) im.instanceColor.needsUpdate = true; }
    for (const key of Object.keys(n) as (keyof typeof n)[]) {
      const im = W[key];
      im.count = n[key];
      im.instanceMatrix.needsUpdate = true;
      if (im.instanceColor) im.instanceColor.needsUpdate = true;
    }
    this.bodies.count = np; this.heads.count = np; this.eyes.count = np; this.cheeks.count = np; this.outline.count = np;
    this.cars.count = nc; this.cabins.count = nc;
    for (const im of [this.bodies, this.heads, this.cars, this.cabins, this.eyes, this.cheeks, this.outline]) {
      im.instanceMatrix.needsUpdate = true;
      if (im.instanceColor) im.instanceColor.needsUpdate = true;
    }
  }
}

function offsetPolyline(p: V2[], d: number): V2[] {
  if (d === 0) return p;
  return p.map((q, i) => {
    const a = p[Math.max(0, i - 1)], b = p[Math.min(p.length - 1, i + 1)];
    const dir = norm(sub(b, a));
    return add(q, mul(v2(-dir.y, dir.x), d));
  });
}

function circle(c: V2, r: number, n: number): V2[] {
  const out: V2[] = [];
  for (let k = 0; k < n; k++) { const t = (k / n) * Math.PI * 2; out.push(v2(c.x + Math.cos(t) * r, c.y + Math.sin(t) * r)); }
  return out;
}

/** A chubby little bus in the route's color. */
function busMesh(color: string): THREE.Group {
  const m = new GB();
  const body = col(color), white = col(C.white), glass = col("#4E6A93");
  const box = (x0: number, x1: number, y0: number, y1: number, z: number, c: THREE.Color) =>
    m.prism([v2(x0, -z), v2(x1, -z), v2(x1, z), v2(x0, z)], y0, y1, c);
  box(-0.3, 0.3, 0.06, 0.26, 0.13, body);
  box(-0.31, 0.31, 0.26, 0.3, 0.135, white);
  box(-0.27, 0.27, 0.15, 0.24, 0.134, glass);
  box(0.29, 0.305, 0.1, 0.24, 0.1, glass);
  for (const x of [-0.18, 0.18]) for (const z of [-0.13, 0.13]) m.prism(circle(v2(x, z), 0.055, 10), 0, 0.07, col("#3B4560"));
  const grp = new THREE.Group();
  const mesh = new THREE.Mesh(m.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.55 }));
  mesh.castShadow = true;
  grp.add(mesh);
  return grp;
}

/** A subway entrance: tiled booth, canopy and a round sign. `ghost`: a faint "could go here" version. */
function kioskMesh(ghost: boolean): THREE.Group {
  const m = new GB();
  const main = col(SUBWAY_COLOR), white = col(C.white), dark = col("#36406A");
  const rect = (w: number, d: number) => [v2(-w, -d), v2(w, -d), v2(w, d), v2(-w, d)];
  m.prism(rect(0.34, 0.26), 0, 0.05, white);
  m.prism(rect(0.25, 0.18), 0.05, 0.4, main, null);
  m.prism(rect(0.17, 0.182), 0.05, 0.3, dark, null);
  m.prism(rect(0.34, 0.26), 0.4, 0.45, white);
  m.prism(rect(0.3, 0.22), 0.45, 0.48, main);
  m.prism(circle(v2(0.42, 0.24), 0.02, 6), 0, 0.78, col("#8A93B8"));
  const mat = new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.6, transparent: ghost, opacity: ghost ? 0.45 : 1, depthWrite: !ghost });
  const grpExtra: THREE.Object3D[] = [];
  if (ghost) {
    const ring = new THREE.Mesh(new THREE.RingGeometry(0.42, 0.5, 32), new THREE.MeshBasicMaterial({ color: col(SUBWAY_COLOR), transparent: true, opacity: 0.6, depthWrite: false }));
    ring.rotation.x = -Math.PI / 2; ring.position.y = 0.012;
    grpExtra.push(ring);
  }
  const mesh = new THREE.Mesh(m.build(), mat);
  mesh.castShadow = !ghost;
  const signMat = new THREE.MeshStandardMaterial({ color: col(SUBWAY_COLOR), roughness: 0.4, transparent: ghost, opacity: ghost ? 0.9 : 1, emissive: col(SUBWAY_COLOR), emissiveIntensity: ghost ? 0 : 0.25 });
  const sign = new THREE.Mesh(new THREE.CylinderGeometry(0.12, 0.12, 0.035, 20), signMat);
  sign.rotation.x = Math.PI / 2;
  sign.position.set(0.42, 0.84, -0.24);
  const ring = new THREE.Mesh(new THREE.TorusGeometry(0.12, 0.022, 6, 20), new THREE.MeshStandardMaterial({ color: 0xffffff, transparent: ghost, opacity: ghost ? 0.45 : 1 }));
  ring.position.copy(sign.position);
  const grp = new THREE.Group();
  grp.add(mesh, sign, ring, ...grpExtra);
  return grp;
}

const SUITS = ["#3A3F4B", "#2F3B57", "#5A4636", "#6B6E75", "#44506A"];
const DRESSES = ["#B88A8F", "#8DA2B5", "#A89A7C", "#9C8BB0", "#C9B48E", "#7E9A8A"];
/** A random 1960s office outfit: mostly suits, some skirt suits, hats and briefcases here and there. */
function outfit(rng: Rng, briefcaseChance: number): Outfit {
  const dress = rng.chance(0.5);
  return {
    kid: false,
    dress,
    suit: col(dress ? rng.pick(DRESSES) : rng.pick(SUITS)),
    hat: dress ? (rng.chance(0.5) ? 2 : 0) : rng.chance(0.4) ? 1 : 0,
    briefcase: rng.chance(briefcaseChance),
  };
}

const c2 = (fur: string, patch: string): Coat => ({ fur: col(fur), patch: col(patch) });
/** Natural cat coats: ginger tabby, gray tabby, tuxedo, calico-ish, cream, brown. */
const COATS: Coat[] = [
  c2("#E8914A", "#FFF4E4"), c2("#E8914A", "#FFF4E4"), c2("#98A0AA", "#EEF0F2"), c2("#33343B", "#FFFFFF"),
  c2("#DDA36E", "#FFFFFF"), c2("#F2DDB3", "#FFFCF4"), c2("#8A6046", "#F2E2CE"),
];
const SWEATERS = ["#F4C95D", "#7FB7D9", "#E58B76", "#9CCB86", "#C7A6E0", "#F0EAD8"];
/** A kitten's outfit: a little sweater, sometimes a dress, sometimes a school satchel. */
function kidOutfit(rng: Rng): Outfit {
  return { kid: true, dress: rng.chance(0.45), suit: col(rng.pick(SWEATERS)), hat: 0, briefcase: rng.chance(0.3) };
}

/** A small comic "#@!" bubble for scuffles. */
function cussSprite(): THREE.Sprite {
  const cv = document.createElement("canvas");
  cv.width = 128; cv.height = 64;
  const g = cv.getContext("2d")!;
  g.fillStyle = "#fff"; g.strokeStyle = "#2E3A59"; g.lineWidth = 5;
  g.beginPath(); g.ellipse(64, 30, 56, 24, 0, 0, Math.PI * 2); g.fill(); g.stroke();
  g.fillStyle = "#D9604C"; g.font = "bold 34px Fredoka, sans-serif"; g.textAlign = "center"; g.textBaseline = "middle";
  g.fillText("#@!", 64, 32);
  const tx = new THREE.CanvasTexture(cv);
  tx.colorSpace = THREE.SRGBColorSpace;
  const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: tx, transparent: true, depthTest: false }));
  s.scale.set(0.5, 0.25, 1);
  s.renderOrder = 15;
  return s;
}

const SHOE_M = col("#3B2F2A"), SHOE_F = col("#8E3B46"), SHOE_KID = col("#D9604C"), KID_SHORTS = col("#4E5A78");
/** `?oldground`: the previous (un-grounded) placement, kept only for before/after screenshots. */
const OLD_GROUND = new URLSearchParams(location.search).has("oldground");

/** A small round badge sprite with one bold symbol ("$", "!"). */
function textSprite(txt: string, color: string): THREE.Sprite {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 64;
  const g = cv.getContext("2d")!;
  g.fillStyle = "#fff"; g.strokeStyle = "#2E3A59"; g.lineWidth = 4;
  g.beginPath(); g.arc(32, 32, 26, 0, Math.PI * 2); g.fill(); g.stroke();
  g.fillStyle = color; g.font = "bold 38px Fredoka, sans-serif"; g.textAlign = "center"; g.textBaseline = "middle";
  g.fillText(txt, 32, 34);
  const tx = new THREE.CanvasTexture(cv);
  tx.colorSpace = THREE.SRGBColorSpace;
  const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: tx, transparent: true, depthTest: false }));
  s.scale.set(0.22, 0.22, 1);
  s.renderOrder = 16;
  return s;
}

type GeoKey = "fur" | "hull" | "patch" | "face" | "pink" | "leg" | "arm" | "shoe" | "jacket" | "shirt" | "tie" | "scarf" | "skirt"
  | "fedora" | "band" | "pillbox" | "briefcase" | "stripes" | "mask" | "cap" | "sack" | "cig" | "mug" | "pin" | "book";
type CatGeos = Record<GeoKey, THREE.BufferGeometry>;

/** Paint a whole geometry one color (for vertex-colored props). */
function paint(geo: THREE.BufferGeometry, hex: string): THREE.BufferGeometry {
  const c = new THREE.Color(hex), n = geo.getAttribute("position").count;
  const a = new Float32Array(n * 3);
  for (let i = 0; i < n; i++) { a[i * 3] = c.r; a[i * 3 + 1] = c.g; a[i * 3 + 2] = c.b; }
  geo.setAttribute("color", new THREE.BufferAttribute(a, 3));
  return geo;
}

/** An outline shell: the same shape pushed out along smoothed normals (no spikes at seams). */
function outlineShell(src: THREE.BufferGeometry, width: number): THREE.BufferGeometry {
  let g = src.clone();
  g.deleteAttribute("uv");
  g.deleteAttribute("normal");
  g = mergeVertices(g, 1e-4);
  g.computeVertexNormals();
  const pos = g.getAttribute("position"), nor = g.getAttribute("normal");
  for (let i = 0; i < pos.count; i++) pos.setXYZ(i, pos.getX(i) + nor.getX(i) * width, pos.getY(i) + nor.getY(i) * width, pos.getZ(i) + nor.getZ(i) * width);
  return g;
}

/** All cat and prop geometries at one detail level (`seg` ~ sphere segments). */
function catGeometries(seg: number): CatGeos {
  const S = 0.98;
  const hi = seg > 8;
  const sp = (r: number, x: number, y: number, z: number, sx = 1, sy = 1, sz = 1, k = 1) =>
    new THREE.SphereGeometry(r, Math.max(6, Math.round(seg * 1.6 * k)), Math.max(4, Math.round(seg * k))).scale(sx, sy, sz).translate(x, y, z);
  const box = (w: number, h: number, d: number, x: number, y: number, z: number) => new THREE.BoxGeometry(w, h, d).translate(x, y, z);
  const cyl = (r0: number, r1: number, h: number, x: number, y: number, z: number, s = 8) => new THREE.CylinderGeometry(r0, r1, h, hi ? Math.max(s, 16) : s).translate(x, y, z);
  const g = (geo: THREE.BufferGeometry) => geo.scale(S, S, S);
  const ear = (x: number, r = 0.056, h = 0.12, z = -0.005) => new THREE.ConeGeometry(r, h, hi ? 12 : 6).rotateZ(x > 0 ? -0.32 : 0.32).translate(x, 0.535, z);
  const tailCurve = new THREE.CubicBezierCurve3(new THREE.Vector3(0, 0.15, -0.05), new THREE.Vector3(0, 0.08, -0.2), new THREE.Vector3(0, 0.3, -0.26), new THREE.Vector3(0.02, 0.37, -0.17));
  const fur = g(mergeGeometries([
    sp(0.135, 0, 0.42, 0, 1.06, 0.96, 1), ear(-0.078), ear(0.078),
    sp(0.075, 0, 0.21, 0, 1, 1.35, 0.85, 0.8), sp(0.04, -0.062, 0.27, 0, 1, 1, 1, 0.6), sp(0.04, 0.062, 0.27, 0, 1, 1, 1, 0.6),
    new THREE.TubeGeometry(tailCurve, hi ? 16 : 7, 0.017, hi ? 8 : 4), sp(0.02, 0.02, 0.37, -0.17, 1, 1, 1, 0.5),
  ])!);
  // a smile under the nose ("w"), eyes with depth, and highlights in the patch layer
  const mouth = (x: number) => new THREE.TorusGeometry(0.0145, hi ? 0.0042 : 0.006, 5, hi ? 14 : 8, Math.PI).rotateZ(Math.PI).translate(x, 0.381, 0.14);
  return {
    fur,
    hull: outlineShell(fur, hi ? 0.007 : 0.011),
    patch: g(mergeGeometries([
      sp(0.034, -0.026, 0.383, 0.11, 1, 0.85, 0.8, 0.6), sp(0.034, 0.026, 0.383, 0.11, 1, 0.85, 0.8, 0.6),
      // big white eye highlights, up and to the side of each pupil
      sp(0.014, -0.043, 0.452, 0.143, 1, 1, 0.6, 0.6), sp(0.014, 0.061, 0.452, 0.143, 1, 1, 0.6, 0.6),
      sp(0.007, -0.06, 0.428, 0.144, 1, 1, 0.6, 0.4), sp(0.007, 0.044, 0.428, 0.144, 1, 1, 0.6, 0.4),
    ])!),
    // big round black eyes on the face front, and a small "ω" mouth
    face: g(mergeGeometries([
      sp(0.044, -0.052, 0.437, 0.112, 1, 1.12, 0.62, 0.9), sp(0.044, 0.052, 0.437, 0.112, 1, 1.12, 0.62, 0.9),
      mouth(-0.0135), mouth(0.0135),
    ])!),
    pink: g(mergeGeometries([sp(0.017, 0, 0.402, 0.143, 1.25, 0.8, 0.9, 0.5), sp(0.03, -0.094, 0.392, 0.104, 1, 0.6, 0.45, 0.6), sp(0.03, 0.094, 0.392, 0.104, 1, 0.6, 0.45, 0.6), ear(-0.076, 0.03, 0.07, 0.016), ear(0.076, 0.03, 0.07, 0.016)])!),
    leg: g(cyl(0.026, 0.023, 0.11, 0, -0.055, 0, 6)),
    arm: g(mergeGeometries([cyl(0.022, 0.02, 0.11, 0, -0.055, 0, 6), sp(0.028, 0, -0.115, 0, 1, 1, 1, 0.5)])!),
    shoe: g(sp(0.036, 0, -0.112, 0.018, 1, 0.65, 1.4, 0.6)),
    jacket: g(sp(0.083, 0, 0.215, 0, 1.05, 1.32, 0.95, 0.9)),
    shirt: g(new THREE.ConeGeometry(0.045, 0.09, 3).rotateX(Math.PI).rotateY(Math.PI / 6).scale(1, 1, 0.3).translate(0, 0.27, 0.074)),
    tie: g(mergeGeometries([box(0.022, 0.09, 0.01, 0, 0.235, 0.08), box(0.028, 0.02, 0.012, 0, 0.29, 0.077)])!),
    scarf: g(new THREE.TorusGeometry(0.055, 0.018, hi ? 8 : 4, hi ? 18 : 8).rotateX(Math.PI / 2).translate(0, 0.305, 0.005)),
    skirt: g(cyl(0.075, 0.115, 0.1, 0, 0.13, 0, 8)),
    fedora: g(mergeGeometries([cyl(0.12, 0.12, 0.012, 0, 0.535, 0, 8), cyl(0.07, 0.08, 0.07, 0, 0.57, 0, 7)])!),
    band: g(cyl(0.082, 0.082, 0.018, 0, 0.55, 0, 7)),
    pillbox: g(cyl(0.06, 0.06, 0.045, 0, 0.56, 0.01, 7)),
    briefcase: g(mergeGeometries([box(0.025, 0.075, 0.11, 0, -0.16, 0), box(0.012, 0.02, 0.04, 0, -0.115, 0)])!),
    stripes: g(mergeGeometries([0.16, 0.21, 0.26].map((y) => new THREE.TorusGeometry(0.083, 0.012, hi ? 6 : 4, hi ? 20 : 10).rotateX(Math.PI / 2).scale(1.05, 1, 0.95).translate(0, y, 0)))!),
    mask: g(new THREE.BoxGeometry(0.2, 0.04, 0.04).translate(0, 0.435, 0.11)),
    cap: g(mergeGeometries([cyl(0.105, 0.11, 0.05, 0, 0.53, -0.005, 8), box(0.12, 0.012, 0.08, 0, 0.51, 0.1)])!),
    pin: g(sp(0.018, 0.045, 0.255, 0.07, 1, 1, 0.5, 0.6)),
    book: g(mergeGeometries([box(0.02, 0.09, 0.075, 0, -0.12, 0.02), box(0.022, 0.08, 0.065, 0.002, -0.12, 0.02)])!),
    sack: g(mergeGeometries([sp(0.075, 0, -0.2, 0.02, 1, 1.1, 1, 0.7), cyl(0.02, 0.03, 0.04, 0, -0.12, 0.02, 6)])!),
    // held in the paw, pointing along the arm: white paper, a tan filter, an orange ember
    cig: g(mergeGeometries([
      paint(cyl(0.011, 0.011, 0.03, 0, -0.14, 0.012, 8), "#D9A066"),
      paint(cyl(0.011, 0.011, 0.085, 0, -0.197, 0.012, 8), "#FAFAF7"),
      paint(cyl(0.0115, 0.011, 0.012, 0, -0.245, 0.012, 8), "#FF6A1A"),
      paint(sp(0.007, 0, -0.252, 0.012, 1, 0.6, 1, 0.4), "#FFD34D"),
    ])!),
    // a glass beer mug: amber beer, white foam, a handle
    mug: g(mergeGeometries([
      paint(cyl(0.05, 0.047, 0.11, 0, -0.14, 0.06, 12), "#E9A33A"),
      paint(cyl(0.053, 0.05, 0.03, 0, -0.072, 0.06, 12), "#FFF8EC"),
      paint(sp(0.05, 0, -0.058, 0.06, 1, 0.35, 1, 0.6), "#FFFFFF"),
      paint(new THREE.TorusGeometry(0.03, 0.009, 6, 12).rotateY(Math.PI / 2).translate(0.052, -0.14, 0.06), "#F3D9A8"),
    ])!),
  };
}

/** A soft round puff (radial gradient) for smoke. */
function softDot(): THREE.CanvasTexture {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 64;
  const g = cv.getContext("2d")!;
  const gr = g.createRadialGradient(32, 32, 0, 32, 32, 32);
  gr.addColorStop(0, "rgba(255,255,255,0.95)");
  gr.addColorStop(0.5, "rgba(255,255,255,0.55)");
  gr.addColorStop(1, "rgba(255,255,255,0)");
  g.fillStyle = gr; g.fillRect(0, 0, 64, 64);
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

const segKey = (a: number, b: number) => (a < b ? `${a},${b}` : `${b},${a}`);
const mid2 = (a: V2, b: V2): V2 => v2((a.x + b.x) / 2, (a.y + b.y) / 2);
/** Bridge geometry shared with river.ts: the deck spans the river, perpendicular to segment a→b. */
export const BRIDGE_SPAN = 2.7, BRIDGE_W = 0.95;
export const bridgeY = (t: number) => 0.17 + Math.sin(Math.max(0, Math.min(1, t)) * Math.PI) * 0.3;
export function crossing(a: V2, b: V2) {
  const d = norm(sub(b, a)), n = v2(-d.y, d.x);
  return { mid: mid2(a, b), d, n };
}
/** The way over: from one end of the river segment to the bank, across the bridge, and on. */
/** Distance from the river's centre line to the bank lane. */
export const BANK_LANE = 1.0;
/** The way over, replacing the river leg a→b: along the near bank lane, over the deck, along the far bank lane. */
function detour(a: V2, b: V2): V2[] {
  const { mid, n } = crossing(a, b);
  const e0 = add(mid, mul(n, -BANK_LANE)), e1 = add(mid, mul(n, BANK_LANE));
  const steps = [0.2, 0.35, 0.5, 0.65, 0.8].map((u) => add(e0, mul(sub(e1, e0), u)));
  return [add(a, mul(n, -BANK_LANE)), e0, ...steps, e1, add(b, mul(n, BANK_LANE))];
}
