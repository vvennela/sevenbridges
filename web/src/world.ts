// The three.js diorama: meadow, roads, plots, buildings, surroundings, feelings, camera.
// Everything here is for looks. The layout drawn is exactly what the game
// state holds; outcomes (cost, score, trips, feelings) only come from Lean replies.
import * as THREE from "three";
import { OrbitControls } from "three/examples/jsm/controls/OrbitControls.js";
import { MapCamera } from "./camera";
import { GB, col, w3 } from "./builder";
import { TILE_TOP, buildingHeight, fixedMarker, makeBuilding, tree, type LifeSpots, type Piece } from "./buildings";
import { MAP_SCALE, segDist, add, ccw, centroid, dist, inset, insetEdges, mid, mul, norm, pointInPolygon, smoothClosed, sub, v2, type V2 } from "./geom";
import { C } from "./palette";
import { Rng, hashStr } from "./rng";
import { Transit } from "./transit";
import { RIVER_HALF, bridgeMesh, buildRiver, type BridgeView } from "./river";
import type { Building, PuzzleReply } from "./types";
import { Metro } from "./metro";
import { U, alive, lightAt } from "./ambient";
import { Birds, Farm, Lamps, MAT_OUTER, Smoke, buildOutskirts } from "./outskirts";
import { Air, linkArcs, trafficWash, arcTop, type Link } from "./overlays";

const ROAD_W = 0.62;

export type Setting = "inland" | "river" | "coast";
export type Target = { kind: "block"; i: number } | { kind: "route"; i: number } | { kind: "site"; i: number } | { kind: "bridge"; i: number };
export type Feeling = "happy" | "unhappy" | null;

interface BlockView {
  tilePoly: V2[];
  center: V2;
  root: THREE.Group;
  top: THREE.Mesh;
  glow: THREE.Mesh;
  tint: THREE.Mesh;
  inner: V2[];
  innerPark: V2[];
  ring: THREE.Mesh;
  pieces: Piece[];
  spots: LifeSpots;
  shown: string;
  fixed: boolean;
  building: Building | null;
  feeling: Feeling;
  badge: THREE.Sprite | null;
  nextHeart: number;
}

interface Anim { obj: THREE.Object3D; start: number; dur: number; step: (o: THREE.Object3D, u: number) => void; done?: () => void }

export class World {
  readonly renderer: THREE.WebGLRenderer;
  readonly scene = new THREE.Scene();
  readonly camera: THREE.PerspectiveCamera;
  readonly controls: OrbitControls;
  readonly cam: MapCamera;
  private clock = new THREE.Clock();
  private blocks: BlockView[] = [];
  private anims: Anim[] = [];
  private ray = new THREE.Raycaster();
  private sun!: THREE.DirectionalLight;
  private radius = 12;
  private seed = 1;
  private hovered: Target | null = null;
  private glowOn: Set<number> = new Set();
  private heartTex = heartTexture();
  private cloudTex = cloudTexture();
  transit: Transit | null = null;
  setting: Setting = "inland";

  /** `button`: 0 = left, 2 = right. */
  onClick: (t: Target | null, button: number, ev: PointerEvent) => void = () => {};
  onHover: (t: Target | null) => void = () => {};
  onFrame: () => void = () => {};
  onDouble: (t: Target | null) => void = () => {};

  constructor(private host: HTMLElement) {
    this.renderer = new THREE.WebGLRenderer({ antialias: true, preserveDrawingBuffer: true });
    this.renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.toneMapping = THREE.ACESFilmicToneMapping;
    this.renderer.toneMappingExposure = 1.12;
    host.appendChild(this.renderer.domElement);

    this.scene.background = skyTexture();
    this.scene.fog = new THREE.Fog(col(C.skyHaze), 80, 215);

    this.camera = new THREE.PerspectiveCamera(24, 1, 1, 600);
    this.controls = new OrbitControls(this.camera, this.renderer.domElement);
    this.controls.enablePan = false;
    this.controls.enableDamping = true;
    this.controls.dampingFactor = 0.08;
    this.controls.minPolarAngle = THREE.MathUtils.degToRad(28);
    this.controls.maxPolarAngle = THREE.MathUtils.degToRad(66);
    this.controls.rotateSpeed = 0.6;
    // OrbitControls only holds the target here; input goes through MapCamera (trackpad-first)
    this.controls.enabled = false;
    this.cam = new MapCamera(this.camera, this.renderer.domElement);

    this.hemi = new THREE.HemisphereLight(0xd6ecff, 0xbfe0a0, 1.25);
    this.scene.add(this.hemi);
    const sun = new THREE.DirectionalLight(0xffe4bd, 2.6);
    sun.castShadow = true;
    sun.shadow.mapSize.set(2048, 2048);
    sun.shadow.bias = -0.0005;
    sun.shadow.normalBias = 0.025;
    sun.shadow.radius = 4;
    this.scene.add(sun, sun.target);
    this.sun = sun;

    this.picking();
    window.addEventListener("resize", () => this.resize());
    this.resize();
    this.renderer.setAnimationLoop(() => this.frame());
  }

  private resize() {
    const w = this.host.clientWidth, h = this.host.clientHeight;
    this.renderer.setSize(w, h);
    this.camera.aspect = w / h;
    this.camera.updateProjectionMatrix();
  }

  private picking() {
    const el = this.renderer.domElement;
    let down: { x: number; y: number } | null = null;
    el.addEventListener("contextmenu", (e) => e.preventDefault());
    el.addEventListener("pointerdown", (e) => { down = { x: e.clientX, y: e.clientY }; });
    el.addEventListener("pointerup", (e) => {
      if (down && !this.cam.dragged && Math.hypot(e.clientX - down.x, e.clientY - down.y) < 6 && (e.button === 0 || e.button === 2)) this.onClick(this.pick(e), e.button, e);
      down = null;
    });
    el.addEventListener("pointermove", (e) => {
      if (e.buttons) return;
      const t = this.pick(e);
      if (!sameTarget(t, this.hovered)) { this.hovered = t; this.refreshHover(); this.onHover(t); }
      el.style.cursor = t ? "pointer" : "grab";
      if (e.buttons) el.style.cursor = "grabbing";
    });
    el.addEventListener("dblclick", (e) => { const t = this.pick(e as unknown as PointerEvent); this.onDouble(t); });
    el.addEventListener("pointerleave", () => { this.hovered = null; this.refreshHover(); this.onHover(null); });
  }

  private pick(e: PointerEvent): Target | null {
    const r = this.renderer.domElement.getBoundingClientRect();
    const p = new THREE.Vector2(((e.clientX - r.left) / r.width) * 2 - 1, -((e.clientY - r.top) / r.height) * 2 + 1);
    this.ray.setFromCamera(p, this.camera);
    if (this.transit) {
      const s = this.ray.intersectObjects(this.transit.siteTargets, false)[0];
      const b = this.ray.intersectObjects(this.blocks.map((v) => v.root), true).find((h) => !(h.object instanceof THREE.Sprite));
      const rt = this.ray.intersectObjects(this.transit.routeTargets, false)[0];
      const br = this.ray.intersectObjects(this.bridges.map((x) => x.hit), false)[0];
      // nearest wins, but a site beats its own block
      const cands: { d: number; t: Target }[] = [];
      if (s) cands.push({ d: s.distance - 0.6, t: { kind: "site", i: s.object.userData.site } });
      if (br) cands.push({ d: br.distance - 0.8, t: { kind: "bridge", i: br.object.userData.bridge } });
      if (rt) cands.push({ d: rt.distance - 0.05, t: { kind: "route", i: rt.object.userData.route } });
      if (b) {
        let o: THREE.Object3D | null = b.object;
        while (o && o.userData.block === undefined) o = o.parent;
        if (o) cands.push({ d: b.distance, t: { kind: "block", i: o.userData.block } });
      }
      cands.sort((x, y) => x.d - y.d);
      return cands[0]?.t ?? null;
    }
    return null;
  }

  // ---------- loading ----------

  /** Everything that belongs to the current town (cleared when a new town loads). */
  private level = new THREE.Group();

  /** Remove the current town (a new level is about to load). */
  private clear() {
    this.scene.remove(this.level);
    this.level.traverse((o) => { if (o instanceof THREE.Mesh || o instanceof THREE.InstancedMesh) o.geometry.dispose(); });
    this.level = new THREE.Group();
    this.scene.add(this.level);
    this.blocks = []; this.anims = []; this.bridges = []; this.bridgeOn = []; this.spots = new Map(); this.segOwners = new Map();
    this.links = null; this.transit = null; this.hovered = null; this.glowOn = new Set();
    this.outskirts = null; this.farmAt = null; this.farm = null; this.smoke = null; this.birds = null; this.lamps = null; this.border = null; this.riverLines = [];
    this.metro = null; this.air = null; this.wash = null; this.linkGroup = null;
  }

  load(pr: PuzzleReply) {
    this.clear();
    const pz = pr.puzzle;
    this.seed = hashStr(pz.name + ":" + pz.map.points.map((p) => `${p.x},${p.y}`).join(";"));
    const forced = new URLSearchParams(location.search).get("setting");
    this.setting = forced === "inland" || forced === "river" || forced === "coast" ? forced
      : (["inland", "inland", "river", "coast"] as const)[this.seed % 4];

    const pts = pz.map.points.map((p) => v2(p.x * MAP_SCALE, p.y * MAP_SCALE));
    const outer = ccw(outerLoop(pz.map.blocks.map((b) => b.corners)).map((i) => pts[i]));
    const c = centroid(outer);
    this.mapCenter = c;
    this.radius = Math.max(...pts.map((p) => dist(p, c)));

    // the metro to downtown: from Lean's entry point when given, else behind the town as first seen
    const me = pz.metroEntry && (pz.metroEntry.x !== 0 || pz.metroEntry.y !== 0) ? pz.metroEntry : undefined;
    const mf = me ?? pz.metro?.from;
    const jitter = ((this.seed >>> 8) % 1000) / 1000 - 0.5;
    const mdir = mf ? norm(sub(v2(mf.x * MAP_SCALE, mf.y * MAP_SCALE), c)) : v2(-Math.sin(0.49 + jitter * 0.9), Math.cos(0.49 + jitter * 0.9));
    this.metroDir = mdir;
    this.ground(c);
    const wet = this.water(c);
    this.verge(outer, c);
    const riverSegs = pz.map.segments.map((s, i) => (s.terrain === "stream" ? i : -1)).filter((i) => i >= 0);
    this.riverSegs = new Set(riverSegs);
    this.segPts = pz.map.segments.map((s) => [pts[s.a], pts[s.b]] as [V2, V2]);
    this.roads(pts, pz.map.segments.filter((s) => s.terrain !== "stream"));
    this.riverLines = riverSegs.length ? buildRiver(this.level as unknown as THREE.Scene, pts, pz.map.segments, riverSegs, new Set(outerLoop(pz.map.blocks.map((b) => b.corners))), c, this.seed) : [];
    this.bridges = (pz.bridgeSites ?? []).map((seg, site) => {
      const s = pz.map.segments[seg];
      const a = pts[s.a], b = pts[s.b];
      const ghost = bridgeMesh(a, b, true), real = bridgeMesh(a, b, false);
      real.visible = false;
      const hit = new THREE.Mesh(new THREE.SphereGeometry(0.9, 8, 6), new THREE.MeshBasicMaterial({ visible: false }));
      hit.position.set((a.x + b.x) / 2, 0.15, -(a.y + b.y) / 2);
      hit.scale.set(1, 1, 1);
      hit.userData.bridge = site;
      this.level.add(ghost, real, hit);
      return { site, seg, a, b, ghost, real, hit };
    });
    this.metro = new Metro(this.level, c, this.radius, mdir, outer, this.seed);
    this.air = new Air(this.level);
    this.surroundings(c, outer, (p) => wet(p) || !!this.metro?.near(p, 1.4) || this.downtownArea(p, c));

    const edgeKey = (a: number, b: number) => (a < b ? `${a},${b}` : `${b},${a}`);
    const owners = new Map<string, number[]>();
    pz.map.blocks.forEach((b, i) => b.corners.forEach((c0, k) => { const kk = edgeKey(c0, b.corners[(k + 1) % b.corners.length]); owners.set(kk, [...(owners.get(kk) ?? []), i]); }));
    this.adj = pz.map.blocks.map(() => []);
    for (const os of owners.values()) if (os.length === 2) { this.adj[os[0]].push(os[1]); this.adj[os[1]].push(os[0]); }
    pz.map.segments.forEach((s, i) => this.segOwners.set(i, owners.get(edgeKey(s.a, s.b)) ?? []));
    const riverMids = pz.map.segments.filter((s) => s.terrain === "stream").map((s) => mid(pts[s.a], pts[s.b]));
    this.blocks = pz.map.blocks.map((b, i) => this.makeBlock(i, ccw(b.corners.map((k) => pts[k])), pz.fixed[i] !== null, riverMids));

    const spots = new Map<number, V2>();
    for (const s of pz.stationSites) {
      const b = this.blocks[s];
      if (b) spots.set(s, this.stationSpot(b));
    }
    this.transit = new Transit(this.level as unknown as THREE.Scene, pts, pz.map.segments, pz.map.blocks.map((b) => b.corners),
      this.blocks.map((b) => b.center), outer, pz.routes, spots, this.seed);
    this.transit.groundAt = (p) => this.groundAt(p);
    this.spots = spots;
    // life around town: cars on the outer streets and the lanes, cats idling in outer yards,
    // lamp posts, birds now and then
    const ok = this.outskirts;
    if (ok) {
      this.transit.setAmbientCars([...ok.streets.map(([a, b]) => ({ pts: [a, b], loop: true })), ...this.lanes.map((l) => ({ pts: l, loop: false }))]);
      this.transit.ambientIdle = ok.idle;
      this.transit.setIdlers([]);
    }
    const lampSpots = [...(ok?.lamps ?? [])];
    for (const b of this.blocks) {
      // two lamps per playable block, at its sharpest corners, on the sidewalk
      const P = b.tilePoly;
      const corners = P.map((v, k) => { const a = P[(k - 1 + P.length) % P.length], d = P[(k + 1) % P.length]; const u = norm(sub(a, v)), w = norm(sub(d, v)); return { v, k, c: u.x * w.x + u.y * w.y }; }).sort((x, y) => y.c - x.c);
      for (const q of corners.slice(0, 2)) lampSpots.push(add(q.v, mul(norm(sub(b.center, q.v)), 0.14)));
    }
    this.lamps = new Lamps(this.level, lampSpots);
    this.birds = new Birds(this.level, c, this.radius, this.seed);
    // a soft line around the playable district, on the inner edge of the ring road
    const bm = new GB();
    const ring = outer.map((q) => add(q, mul(norm(sub(q, c)), -0.36)));
    for (let k = 0; k < ring.length; k++) {
      const a = ring[k], b = ring[(k + 1) % ring.length], d = norm(sub(b, a)), nn = v2(-d.y * 0.05, d.x * 0.05);
      bm.quad(w3(add(a, nn), 0.03), w3(add(b, nn), 0.03), w3(sub(b, nn), 0.03), w3(sub(a, nn), 0.03), col("#FFC83D"), [0, 1, 0]);
    }
    this.border = new THREE.Mesh(bm.build(), new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: 0.35, depthWrite: false }));
    this.border.renderOrder = 2;
    this.level.add(this.border);

    const t = new THREE.Vector3(c.x, 0, -c.y);
    this.controls.target.copy(t);
    const d = this.radius * 4.3;
    // the camera looks toward downtown, so the skyline sits behind the town
    const el = THREE.MathUtils.degToRad(42), az = Math.atan2(-mdir.x, mdir.y) + 0.12;
    this.camera.position.set(t.x + d * Math.cos(el) * Math.sin(az), d * Math.sin(el), t.z + d * Math.cos(el) * Math.cos(az));
    this.cam.minDist = this.radius * 0.55;
    this.cam.maxDist = this.radius * 6.5;
    this.cam.center.copy(t);
    this.cam.bound = this.radius * 0.95;
    this.home = { target: t.clone(), dist: d, az, polar: Math.PI / 2 - el };
    this.cam.set(t, d, az, Math.PI / 2 - el, true);
    const s = this.radius + 3;
    Object.assign(this.sun.shadow.camera, { left: -s, right: s, top: s, bottom: -s, near: 1, far: 90 });
    this.sun.position.set(t.x - 16, 20, t.z + 12);
    this.sun.target.position.copy(t);
    this.sun.shadow.camera.updateProjectionMatrix();
  }

  private metroDir: V2 = v2(0, 1);
  private riverLines: [V2, V2][] = [];
  private lanes: V2[][] = [];
  private outskirts: ReturnType<typeof buildOutskirts> | null = null;
  private farmAt: V2 | null = null;
  private farm: Farm | null = null;
  private smoke: Smoke | null = null;
  private birds: Birds | null = null;
  private lamps: Lamps | null = null;
  private hemi!: THREE.HemisphereLight;
  private border: THREE.Mesh | null = null;
  metro: Metro | null = null;
  private air: Air | null = null;
  private wash: THREE.Mesh | null = null;
  private linkGroup: THREE.Group | null = null;
  /** Slow turntable spin (title screen), radians per second; 0 = off. */
  orbit = 0;

  /** The open country around downtown (no trees or cottages there). */
  private downtownArea(p: V2, c: V2): boolean {
    void c;
    return !!this.metro && dist(p, this.metro.downtown) < 35;
  }

  /** Pollution haze (0..1 per block) and fresh air over the given blocks. */
  setAir(level: (number | null)[] | null, fresh: number[]) {
    this.air?.set(this.blocks.map((b) => b.center), level ?? [], level ? fresh : [], (i) => {
      const b = this.blocks[i];
      return b ? Math.min(...b.tilePoly.map((q) => dist(q, b.center))) : 1;
    });
  }

  /** Busy streets: 0..1 per map segment (null clears). */
  setTraffic(level: number[] | null) {
    if (this.wash) { this.level.remove(this.wash); this.wash.geometry.dispose(); this.wash = null; }
    if (!level || !this.segPts.length) return;
    this.wash = trafficWash(this.segPts, level, ROAD_W * 0.8);
    if (this.wash) this.level.add(this.wash);
  }
  private segPts: [V2, V2][] = [];
  private heat: THREE.Mesh | null = null;
  /** Air lens: a bold heat line on streets with cars (0..1 per segment; null clears). */
  setHeat(level: number[] | null) {
    if (this.heat) { this.level.remove(this.heat); this.heat.geometry.dispose(); this.heat = null; }
    if (!level || !this.segPts.length) return;
    this.heat = trafficWash(this.segPts, level, ROAD_W * 0.42, 0.95, 0.045);
    if (this.heat) this.level.add(this.heat);
  }

  /** Arcs from a hovered block to the blocks that affect it (null clears). */
  setLinks(links: { from: number; to: number; tone: Link["tone"] }[] | null) {
    if (this.linkGroup) { this.level.remove(this.linkGroup); this.linkGroup.traverse((o) => { if (o instanceof THREE.Mesh) o.geometry.dispose(); }); this.linkGroup = null; }
    if (!links?.length) return;
    this.linkGroup = linkArcs(links.map((l) => ({ from: this.centerOf(l.from), to: this.centerOf(l.to), tone: l.tone })));
    this.level.add(this.linkGroup);
  }
  /** Screen spot for a link's label (the top of its arc). */
  linkLabelAt(from: number, to: number, along = 0.5): { x: number; y: number } | null {
    const t = arcTop(this.centerOf(from), this.centerOf(to), along);
    return this.project(t.p, t.h);
  }

  /** Neighbors as Lean counts them: blocks sharing a street, across the river only over a built bridge. */
  linkedNeighbors(i: number): number[] {
    const out = new Set<number>();
    for (const [seg, os] of this.segOwners) {
      if (os.length !== 2 || !os.includes(i)) continue;
      const j = os[0] === i ? os[1] : os[0];
      const site = this.bridges.find((b) => b.seg === seg);
      if (this.riverSegs.has(seg) && !(site && this.bridgeOn[site.site])) continue;
      out.add(j);
    }
    return [...out];
  }
  private riverSegs = new Set<number>();

  private spots = new Map<number, V2>();
  private bridges: BridgeView[] = [];
  private bridgeOn: boolean[] = [];
  private segOwners = new Map<number, number[]>();
  private links: THREE.Group | null = null;
  private home = { target: new THREE.Vector3(), dist: 30, az: 0.5, polar: 0.9 };
  private mapCenter: V2 = v2(0, 0);
  /** Blocks that share a street edge. */
  private adj: number[][] = [];

  /** The subway entrance spot: a free corner of the block. */
  private stationSpot(b: BlockView): V2 {
    const P = b.tilePoly;
    let best = P[0], bestA = -Infinity;
    P.forEach((v, k) => {
      const a = P[(k - 1 + P.length) % P.length], c = P[(k + 1) % P.length];
      const d1 = norm(sub(a, v)), d2 = norm(sub(c, v));
      const ang = Math.acos(Math.max(-1, Math.min(1, d1.x * d2.x + d1.y * d2.y)));
      const room = Math.min(dist(a, v), dist(c, v));
      const score = ang + room * 0.3;
      if (score > bestA) { bestA = score; best = v; }
    });
    const q = add(best, mul(norm(sub(b.center, best)), 0.75));
    return pointInPolygon(q, P) ? q : b.center;
  }

  private makeBlock(i: number, poly: V2[], fixed: boolean, riverMids: V2[] = []): BlockView {
    // edges along the river give way to the wide waterway (render only)
    const ds = poly.map((p, k) => { const q = mid(p, poly[(k + 1) % poly.length]); return riverMids.some((r) => dist(r, q) < 0.05) ? RIVER_HALF + 0.05 : ROAD_W / 2 + 0.06; });
    const tilePoly = insetEdges(poly, ds);
    const center = centroid(tilePoly);
    const root = new THREE.Group();
    root.userData.block = i;
    this.level.add(root);

    // soft raised plot: a curb, then the plot top
    const curb = extrude(tilePoly, 0, TILE_TOP - 0.02, 0.05, col(C.curb));
    const top = extrude(inset(tilePoly, 0.1), TILE_TOP - 0.03, TILE_TOP, 0.02, col(fixed ? C.plotFixed : C.lot));
    root.add(curb, top);

    // placement glow (open blocks, while a building type is picked)
    const gGeo = new THREE.ShapeGeometry(new THREE.Shape(inset(tilePoly, 0.1).map((p) => new THREE.Vector2(p.x, p.y))));
    gGeo.rotateX(-Math.PI / 2);
    gGeo.translate(0, TILE_TOP + 0.006, 0);
    const glow = new THREE.Mesh(gGeo, new THREE.MeshBasicMaterial({ color: col(C.glow), transparent: true, opacity: 0, depthWrite: false }));
    glow.visible = false;
    root.add(glow);
    const tint = new THREE.Mesh(gGeo.clone().translate(0, 0.05, 0), new THREE.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.6, depthWrite: false }));
    tint.visible = false;
    tint.renderOrder = 3;
    root.add(tint);

    // the hover ring: the plot outline with the inner part cut out (vertex counts may differ)
    const ringShape = new THREE.Shape(tilePoly.map((p) => new THREE.Vector2(p.x, p.y)));
    ringShape.holes.push(new THREE.Path(inset(tilePoly, 0.16).map((p) => new THREE.Vector2(p.x, p.y))));
    const ringGeo = new THREE.ShapeGeometry(ringShape);
    ringGeo.rotateX(-Math.PI / 2);
    ringGeo.translate(0, TILE_TOP + 0.01, 0);
    const ring = new THREE.Mesh(ringGeo, new THREE.MeshBasicMaterial({ color: 0xffffff, transparent: true, opacity: 0.9, depthWrite: false, side: THREE.DoubleSide }));
    ring.visible = false;
    root.add(ring);

    if (fixed) root.add(fixedMarker(tilePoly, center));
    return { tilePoly, center, root, top, glow, tint, inner: inset(tilePoly, 0.3), innerPark: inset(tilePoly, 0.16), ring, pieces: [], spots: { benches: [], strolls: [] }, shown: "", fixed, building: null, feeling: null, badge: null, nextHeart: 0 };
  }

  private ground(c: V2) {
    const g = new THREE.Mesh(new THREE.CircleGeometry(400, 64), alive(new THREE.MeshStandardMaterial({ color: col(C.meadow), roughness: 1 }), { clouds: true }));
    g.rotateX(-Math.PI / 2);
    g.position.set(c.x, -0.02, -c.y);
    g.receiveShadow = true;
    this.level.add(g);
  }

  /** A slightly deeper green verge hugging the ring road. */
  private verge(outer: V2[], c: V2) {
    const rng = new Rng(this.seed ^ 0x51ab);
    const ph = [rng.range(0, 6), rng.range(0, 6)];
    const v = smoothClosed(outer.map((p) => {
      const d = norm(sub(p, c));
      const a = Math.atan2(d.y, d.x);
      return add(p, mul(d, 1.1 + 0.3 * (Math.sin(a * 3 + ph[0]) * 0.6 + Math.sin(a * 5 + ph[1]) * 0.4)));
    }), 5);
    const g = new THREE.ShapeGeometry(new THREE.Shape(v.map((q) => new THREE.Vector2(q.x, q.y))));
    g.rotateX(-Math.PI / 2);
    g.translate(0, -0.01, 0);
    const m = new THREE.Mesh(g, alive(new THREE.MeshStandardMaterial({ color: col(C.meadowDeep), roughness: 1 }), { clouds: true }));
    m.receiveShadow = true;
    this.level.add(m);
  }

  /** Cosmetic water on one side: a river or a coast (or nothing). Returns a "wet" test. */
  private water(c: V2): (p: V2) => boolean {
    if (this.setting === "inland") return () => false;
    const rng = new Rng(this.seed ^ 0x5e7);
    // water lies on the side away from downtown
    const a = Math.atan2(-this.metroDir.y, -this.metroDir.x) + rng.range(-0.6, 0.6);
    const u = v2(Math.cos(a), Math.sin(a)), w = v2(-u.y, u.x);
    const ph = rng.range(0, 6);
    const near = (t: number) => this.radius + 3.2 + 0.9 * Math.sin(t * 0.09 + ph) + 0.4 * Math.sin(t * 0.23 + ph * 2);
    const width = (t: number) => (this.setting === "river" ? 4.2 + 0.6 * Math.sin(t * 0.13 + ph) : 500);
    const at = (t: number, d: number) => add(c, add(mul(w, t), mul(u, d)));
    const ts: number[] = [];
    for (let t = -320; t <= 320; t += Math.abs(t) < 80 ? 1 : 20) ts.push(t);
    const band = (grow: number, y: number, color: string) => {
      const pts = [...ts.map((t) => at(t, near(t) - grow)), ...[...ts].reverse().map((t) => at(t, near(t) + width(t) + grow))];
      const g = new THREE.ShapeGeometry(new THREE.Shape(pts.map((p) => new THREE.Vector2(p.x, p.y))));
      g.rotateX(-Math.PI / 2);
      g.translate(0, y, 0);
      const m = new THREE.Mesh(g, alive(new THREE.MeshStandardMaterial({ color: col(color), roughness: 0.35, metalness: 0.0 }), { clouds: true, water: color === C.water }));
      m.receiveShadow = true;
      this.level.add(m);
    };
    band(0.8, -0.012, C.sand);
    band(0.15, -0.008, C.shallows);
    band(-0.35, -0.004, C.water);
    return (p: V2) => {
      const q = sub(p, c);
      const t = q.x * w.x + q.y * w.y, d = q.x * u.x + q.y * u.y;
      return d > near(t) - 1.4 && d < near(t) + width(t) + 1.4;
    };
  }

  private roads(pts: V2[], segs: { a: number; b: number }[]) {
    const m = new GB();
    const road = col(C.road);
    const y = 0.02;
    for (const s of segs) {
      const a = pts[s.a], b = pts[s.b];
      const d = norm(sub(b, a)), n = v2(-d.y * ROAD_W / 2, d.x * ROAD_W / 2);
      m.quad(w3(add(a, n), y), w3(add(b, n), y), w3(sub(b, n), y), w3(sub(a, n), y), road, [0, 1, 0]);
    }
    for (const p of pts) {
      const ring: ReturnType<typeof w3>[] = [];
      for (let k = 0; k < 16; k++) { const t = (k / 16) * Math.PI * 2; ring.push(w3(add(p, v2(Math.cos(t) * ROAD_W / 2, Math.sin(t) * ROAD_W / 2)), y)); }
      m.poly(ring, road, [0, 1, 0]);
    }
    const mesh = new THREE.Mesh(m.build(), alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.95 }), { clouds: true }));
    mesh.receiveShadow = true;
    this.level.add(mesh);
  }

  /** The edge of town. `?bg=meadow` (default): rolling meadow with soft tree lines and a lane
   * leading out; `?bg=suburb`: quieter streets of little houses fading into haze. Context only. */
  private surroundings(c: V2, outer: V2[], wet: (p: V2) => boolean) {
    const rng = new Rng(this.seed ^ 0xc17);
    const style = new URLSearchParams(location.search).get("bg") === "suburb" ? "suburb" : "meadow";
    const near = new GB(), far = new GB();
    const town = outer.map((q) => add(q, mul(norm(sub(q, c)), 2.0)));
    const clear = (p: V2, pad = 0) => !pointInPolygon(p, town) && !wet(p) && dist(p, c) > this.radius + 1.8 + pad && !(this.outskirts?.covers(p) ?? false) && !(this.farmAt && dist(p, this.farmAt) < 7.5);
    const R = this.radius;
    const pick = (r: number) => (r < R + 14 ? near : far);
    const blob = (p: V2, rx: number, ry: number, rot: number, color: string, y: number, m: GB) => {
      const pts: V2[] = [];
      for (let k = 0; k < 24; k++) {
        const t = (k / 24) * Math.PI * 2, wob = 1 + 0.12 * Math.sin(t * 3 + rot * 5);
        const q = v2(Math.cos(t) * rx * wob, Math.sin(t) * ry * wob);
        pts.push(add(p, v2(q.x * Math.cos(rot) - q.y * Math.sin(rot), q.x * Math.sin(rot) + q.y * Math.cos(rot))));
      }
      m.poly(pts.map((q) => w3(q, y)), col(color), [0, 1, 0]);
    };
    const smokeAt: { p: V2; h: number }[] = [];
    const house = (m: GB, p: V2, n: V2, w: number, d: number, h: number, wall: string, roof: string) => {
      if (smokeAt.length < 7 && rng.chance(0.6)) smokeAt.push({ p, h: h + d * 0.42 + 0.1 });
      const ax = v2(n.y, -n.x);
      const F = [add(add(p, mul(ax, -w / 2)), mul(n, -d / 2)), add(add(p, mul(ax, w / 2)), mul(n, -d / 2)), add(add(p, mul(ax, w / 2)), mul(n, d / 2)), add(add(p, mul(ax, -w / 2)), mul(n, d / 2))];
      m.prism(F, 0, h, col(wall), null);
      const r1 = mid(F[0], F[3]), r2 = mid(F[1], F[2]), H = h + d * 0.42;
      m.quad(w3(F[0], h), w3(F[1], h), w3(r2, H), w3(r1, H), col(roof), [-n.x, 1, n.y]);
      m.quad(w3(F[2], h), w3(F[3], h), w3(r1, H), w3(r2, H), col(roof), [n.x, 1, -n.y]);
      m.tri(w3(F[3], h), w3(F[0], h), w3(r1, H), col(wall), [-ax.x, 0, ax.y]);
      m.tri(w3(F[1], h), w3(F[2], h), w3(r2, H), col(wall), [ax.x, 0, -ax.y]);
    };
    // two lanes leading out of town, gently curving
    const lanes: V2[][] = [];
    const exits = [rng.range(0, Math.PI * 2)];
    exits.push(exits[0] + Math.PI * rng.range(0.7, 1.3));
    for (const a0 of exits) {
      const start = outer.reduce((best, q) => (Math.abs(Math.atan2(q.y - c.y, q.x - c.x) - a0) < Math.abs(Math.atan2(best.y - c.y, best.x - c.x) - a0) ? q : best), outer[0]);
      const lane: V2[] = [start];
      let ang = Math.atan2(start.y - c.y, start.x - c.x), p = start;
      for (let s = 0; s < 60; s++) {
        ang += Math.sin(s * 0.35 + a0) * 0.06;
        p = add(p, v2(Math.cos(ang) * 1.0, Math.sin(ang) * 1.0));
        if (wet(p)) break;
        lane.push(p);
      }
      lanes.push(lane);
      const m = new GB();
      for (let k = 1; k < lane.length; k++) {
        const a = lane[k - 1], b = lane[k], dn = norm(sub(b, a)), nn = v2(-dn.y * 0.28, dn.x * 0.28);
        m.quad(w3(add(a, nn), 0.006), w3(add(b, nn), 0.006), w3(sub(b, nn), 0.006), w3(sub(a, nn), 0.006), col(C.road), [0, 1, 0]);
        m.poly(Array.from({ length: 10 }, (_, j) => w3(add(b, v2(Math.cos(j / 10 * 6.283) * 0.28, Math.sin(j / 10 * 6.283) * 0.28)), 0.006)), col(C.road), [0, 1, 0]);
      }
      const mesh = new THREE.Mesh(m.build(), alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 1 }), { clouds: true }));
      mesh.receiveShadow = true;
      this.level.add(mesh);
    }
    // the city around the neighborhood (not playable), thinning out into the countryside
    const riverNear = (p: V2, d: number) => this.riverLines.some(([a, b]) => segDist(p, a, b) < d);
    const laneNear = (p: V2, d: number) => lanes.some((l) => l.some((q) => dist(q, p) < d));
    const ok = buildOutskirts(this.level, outer, c, this.seed, (p) => wet(p) || riverNear(p, 1.7) || laneNear(p, 0.9) || pointInPolygon(p, outer));
    this.outskirts = ok;
    const cottages: { p: V2; h: number }[] = [];
    // a windmill and a little farm out in the meadow
    for (let k = 0; k < 24; k++) {
      const a = rng.range(0, Math.PI * 2), r = R + rng.range(15, 22);
      const p = add(c, v2(Math.cos(a) * r, Math.sin(a) * r));
      const face = norm(sub(c, p)), side = v2(-face.y, face.x);
      const probe = [p, add(p, mul(side, -6)), add(p, mul(side, 6)), add(add(p, mul(side, -4)), mul(face, 3.5))];
      if (probe.some((q) => !clear(q, 1) || laneNear(q, 1.5) || riverNear(q, 2) || this.downtownArea(q, c))) continue;
      this.farm = new Farm(this.level, p, face, rng);
      this.farmAt = p;
      break;
    }

    this.lanes = lanes;
    const nearLane = (p: V2, d: number) => lanes.some((l) => l.some((q) => dist(q, p) < d));

    if (style === "meadow") {
      // soft, low-contrast swells in the grass
      for (let k = 0; k < 40; k++) {
        const a = rng.range(0, Math.PI * 2), r = R + 4 + rng.next() * 40;
        const p = add(c, v2(Math.cos(a) * r, Math.sin(a) * r));
        if (!clear(p, 2)) continue;
        blob(p, rng.range(3, 7), rng.range(2, 4.5), rng.range(0, 3), rng.pick(["#B0D891", "#BFE2A2", "#ACD58B", "#C4E3A6"]), 0.002, far);
      }
      // tree lines that follow gentle curves
      for (let k = 0; k < 11; k++) {
        const a0 = rng.range(0, Math.PI * 2), r0 = R + 4 + rng.range(0, 24);
        let ang = a0;
        for (let s = 0; s < rng.int(6, 14); s++) {
          ang += 0.045 + Math.sin(s * 0.7 + k) * 0.02;
          const r = r0 + Math.sin(s * 0.5 + k) * 0.8;
          const p = add(c, v2(Math.cos(ang) * r, Math.sin(ang) * r));
          if (!clear(p) || nearLane(p, 1.2)) continue;
          tree(pick(r), p, rng.range(0.9, 1.35), rng, 0, rng.pick([C.leaf, "#6FCB72", "#57B567"]));
        }
      }
      // a few round copses and lone trees
      for (let k = 0; k < 70; k++) {
        const a = rng.range(0, Math.PI * 2), r = R + 2.6 + rng.next() ** 1.3 * 36;
        const p = add(c, v2(Math.cos(a) * r, Math.sin(a) * r));
        if (!clear(p) || nearLane(p, 1)) continue;
        const nT = rng.chance(0.3) ? rng.int(3, 5) : 1;
        for (let j = 0; j < nT; j++) tree(pick(r), add(p, v2(rng.range(-0.7, 0.7), rng.range(-0.7, 0.7))), rng.range(0.85, 1.4), rng, 0, rng.pick([C.leaf, "#6FCB72", "#57B567"]));
      }
      // cottages along the lanes
      for (const lane of lanes) for (let s = 4; s < lane.length; s += rng.int(4, 7)) {
        const a = lane[s - 1], b = lane[s], dn = norm(sub(b, a)), side = rng.chance(0.5) ? 1 : -1;
        const p = add(b, mul(v2(-dn.y, dn.x), side * 1.1));
        if (!clear(p, 0.5)) continue;
        const n = mul(v2(-dn.y, dn.x), -side);
        house(pick(dist(p, c)), p, n, rng.range(0.9, 1.2), 0.85, rng.range(0.55, 0.75), rng.pick([C.butter, "#FFD6A5", "#FFF1CF", C.white]), rng.pick([C.coral, "#F47C6E", "#E0707E"]));
        tree(pick(dist(p, c)), add(p, mul(dn, 0.9)), 1, rng, 0);
      }
    } else {
      // quieter residential streets: rows of little houses on soft rings, fading out
      for (let ring = 0; ring < 9; ring++) {
        const r = R + 3.4 + ring * 2.3;
        const count = Math.floor((2 * Math.PI * r) / 1.45);
        for (let k = 0; k < count; k++) {
          const a = (k / count) * Math.PI * 2 + ring * 0.13;
          const p = add(c, v2(Math.cos(a) * r, Math.sin(a) * r));
          if (!clear(p) || nearLane(p, 0.9) || rng.chance(0.15)) continue;
          const n = norm(sub(c, p));
          if (rng.chance(0.25)) { tree(pick(r), p, rng.range(0.9, 1.3), rng, 0); continue; }
          house(pick(r), p, n, rng.range(0.9, 1.2), 0.85, rng.range(0.5, 0.8), rng.pick([C.butter, "#FFD6A5", C.mint, C.sky, "#FFF1CF"]), rng.pick([C.coral, "#F47C6E", "#9F86D6", "#6FA8DC"]));
        }
      }
    }
    void cottages;
    this.smoke = new Smoke(this.level, smokeAt);
    for (const [m, shadow] of [[near, true], [far, false]] as const) {
      const mesh = new THREE.Mesh(m.build(), alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.9 }), { wind: true, clouds: true, windows: true }));
      mesh.castShadow = shadow; mesh.receiveShadow = true;
      this.level.add(mesh);
    }
  }

  // ---------- drawing the layout ----------

  /** Draw a building per block. Changed blocks regrow; `regrowAll` replays the whole town growing in. */
  setBuild(build: Building[], station: number | null, regrowAll = false) {
    const now = this.clock.getElapsedTime();
    build.forEach((b, i) => {
      const v = this.blocks[i];
      if (!v) return;
      const key = `${b.kind}:${b.stories}`;
      if (key === v.shown && !regrowAll) return;
      const sameKind = v.shown.split(":")[0] === b.kind;
      if (key !== v.shown) {
        for (const p of v.pieces) { v.root.remove(p.obj); disposeTree(p.obj); }
        v.spots = { benches: [], strolls: [] };
        v.pieces = makeBuilding(b, { poly: v.tilePoly, center: v.center, rng: new Rng(this.seed ^ hashStr(`b${i}:${b.kind}`)), keepClear: this.spots.get(i), fixed: v.fixed, spots: v.spots, index: i, townSalt: this.seed % 7 });
        for (const p of v.pieces) { p.obj.userData.block = i; v.root.add(p.obj); }
        v.shown = key;
        v.building = b;
        (v.top.material as THREE.MeshStandardMaterial).color.copy(col(b.kind === "empty" ? C.lot : v.fixed ? C.plotFixed : C.plot));
      }
      const stagger = regrowAll ? i * 0.14 : 0;
      for (const p of v.pieces) {
        const from = sameKind && !regrowAll ? 0.7 : 0.001;
        p.obj.scale.set(1, from, 1);
        this.anim(p.obj, now + stagger + p.delay, 0.6, (o, u) => {
          const s = easeOutBack(u);
          o.scale.set(0.9 + 0.1 * Math.min(1, u * 1.5), Math.max(0.001, from + (1 - from) * s), 0.9 + 0.1 * Math.min(1, u * 1.5));
        });
      }
      if (v.badge) v.badge.position.y = buildingHeight(b) + 0.5;
    });
    this.transit?.setStation(station);
    this.metro?.setStation(station !== null ? this.spots.get(station) ?? this.blocks[station]?.center ?? null : null);
  }

  /** Hearts over happy homes, small gray clouds over unhappy ones (from Lean's residents). */
  setFeelings(f: Feeling[]) {
    const now = this.clock.getElapsedTime();
    this.blocks.forEach((v, i) => {
      const next = f[i] ?? null;
      if (next === v.feeling) return;
      v.feeling = next;
      if (v.badge) { const old = v.badge; this.anim(old, now, 0.2, (o, u) => o.scale.setScalar(0.5 * (1 - u)), () => { v.root.remove(old); }); v.badge = null; }
      if (!next) return;
      const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: next === "happy" ? this.heartTex : this.cloudTex, depthTest: false, transparent: true }));
      s.renderOrder = 20;
      s.position.set(v.center.x, buildingHeight(v.building ?? { kind: "empty", stories: 0 }) + 0.75, -v.center.y);
      s.userData.base = s.position.y;
      v.root.add(s);
      v.badge = s;
      v.nextHeart = now + 1 + Math.random() * 2;
      this.anim(s, now + i * 0.04, 0.45, (o, u) => o.scale.setScalar(0.8 * easeOutBack(u)));
    });
  }

  /** A burst of hearts over every happy home (a perfect score). */
  heartBurst() {
    const now = this.clock.getElapsedTime();
    for (const v of this.blocks) if (v.building && v.building.kind !== "empty") for (let k = 0; k < 6; k++) this.floatHeart(v, now + k * 0.12, 1.4);
  }

  private floatHeart(v: BlockView, start: number, size = 1) {
    const s = new THREE.Sprite(new THREE.SpriteMaterial({ map: this.heartTex, depthTest: false, transparent: true }));
    s.renderOrder = 19;
    const base = buildingHeight(v.building ?? { kind: "empty", stories: 0 }) + 0.3;
    const dx = (Math.random() - 0.5) * 0.8, dz = (Math.random() - 0.5) * 0.8;
    s.position.set(v.center.x + dx, base, -v.center.y + dz);
    s.scale.setScalar(0.001);
    this.level.add(s);
    this.anim(s, start, 1.6, (o, u) => {
      const sp = o as THREE.Sprite;
      sp.position.y = base + u * 1.3;
      sp.scale.setScalar(0.42 * size * Math.min(1, u * 4));
      sp.material.opacity = 1 - u * u;
    }, () => { this.level.remove(s); s.material.dispose(); });
  }

  /** Debug: a path from the road up onto a block's outer sidewalk and along it (for clip checks). */
  edgePath(i: number): V2[] {
    const b = this.blocks[i];
    let k0 = 0, bd = -1;
    b.tilePoly.forEach((p, k) => { const q = mid(p, b.tilePoly[(k + 1) % b.tilePoly.length]); const dd = dist(q, this.mapCenter); if (dd > bd) { bd = dd; k0 = k; } });
    const a = b.tilePoly[k0], c = b.tilePoly[(k0 + 1) % b.tilePoly.length];
    const m0 = mid(a, c), out = norm(sub(m0, this.mapCenter)), along = norm(sub(c, a));
    return [add(m0, mul(out, 0.3)), add(m0, mul(out, -0.15)), add(add(m0, mul(out, -0.15)), mul(along, 0.9))];
  }

  /** Point the camera at a plan point from a given distance and elevation (screenshots). */
  lookAt(p: V2, d: number, elev: number) {
    this.controls.minDistance = 0.5;
    const off = this.camera.position.clone().sub(this.controls.target);
    const flat = new THREE.Vector3(off.x, 0, off.z).normalize();
    this.controls.target.set(p.x, 0.3, -p.y);
    this.camera.position.copy(this.controls.target).add(flat.multiplyScalar(d * Math.cos(elev))).add(new THREE.Vector3(0, d * Math.sin(elev), 0));
    this.cam.syncFromCamera(this.controls.target, true); this.cam.loose = true;
  }

  /** Aim a low camera from outside the town at the outer sidewalk of a block (screenshots). */
  aimEdge(i: number, d = 3.2, elev = 0.2) {
    const b = this.blocks[i];
    if (!b) return;
    let best = b.tilePoly[0], bd = -1;
    b.tilePoly.forEach((p, k) => { const q = mid(p, b.tilePoly[(k + 1) % b.tilePoly.length]); const dd = dist(q, this.mapCenter); if (dd > bd) { bd = dd; best = q; } });
    const out = norm(sub(best, this.mapCenter));
    this.controls.minDistance = 0.5;
    this.controls.minPolarAngle = 0;
    this.controls.maxPolarAngle = Math.PI / 2 - 0.05;
    this.controls.target.set(best.x, 0.15, -best.y);
    const side = v2(-out.y, out.x);
    const dir = norm(add(out, mul(side, 0.6)));
    this.camera.position.set(best.x + dir.x * d * Math.cos(elev), 0.15 + d * Math.sin(elev), -(best.y + dir.y * d * Math.cos(elev)));
    this.cam.syncFromCamera(this.controls.target, true); this.cam.loose = true;
  }

  /** Drop the camera to a low angle (screenshots: check feet on the ground). */
  lowAngle(elev = 0.38, dist = 0.7) {
    this.controls.minDistance = this.radius * 0.4;
    const off = this.camera.position.clone().sub(this.controls.target);
    const len = this.radius * dist;
    const flat = new THREE.Vector3(off.x, 0, off.z).normalize();
    this.camera.position.copy(this.controls.target).add(flat.multiplyScalar(len * Math.cos(elev))).add(new THREE.Vector3(0, len * Math.sin(elev), 0));
    this.cam.syncFromCamera(this.controls.target, true); this.cam.loose = true;
  }

  /** Ease the camera to a block (double-click). */
  focusSmooth(i: number) {
    const v = this.blocks[i];
    if (!v) return;
    this.cam.loose = false;
    this.cam.set(new THREE.Vector3(v.center.x, 0, -v.center.y), this.radius * 1.5, this.cam.goal.az, this.cam.goal.polar);
  }

  /** Where downtown is, from the town's center (the metro comes from there). */
  get downtown(): V2 { return this.metroDir; }

  /** Title screen: a lower, wider view, so the skyline shows behind the town. */
  titleView() {
    this.cam.loose = true;
    this.cam.set(this.home.target, this.radius * 3.4, this.home.az, THREE.MathUtils.degToRad(75), true);
  }

  /** Back to the starting view of the whole town. */
  recenter() {
    this.cam.loose = false;
    this.cam.set(this.home.target, this.home.dist, this.home.az, this.home.polar);
  }

  /** Move the camera close to a block (used by the screenshot script). */
  focus(i: number) {
    const v = this.blocks[i];
    if (!v) return;
    const off = this.camera.position.clone().sub(this.controls.target).setLength(this.radius * 1.45);
    this.controls.target.set(v.center.x, 0, -v.center.y);
    this.camera.position.copy(this.controls.target).add(off);
    this.cam.syncFromCamera(this.controls.target, true); this.cam.loose = true;
  }

  /** Lens tint per block (null = none). */
  setTint(colors: (string | null)[]) {
    this.blocks.forEach((b, i) => {
      const c = colors[i] ?? null;
      b.tint.visible = !!c;
      if (c) (b.tint.material as THREE.MeshBasicMaterial).color.copy(col(c));
    });
  }

  /** Screen position (CSS px) of a plan point at a height, or null if behind the camera. */
  project(p: V2, h: number): { x: number; y: number } | null {
    const v = new THREE.Vector3(p.x, h, -p.y).project(this.camera);
    if (v.z > 1) return null;
    const r = this.renderer.domElement.getBoundingClientRect();
    return { x: r.left + ((v.x + 1) / 2) * r.width, y: r.top + ((1 - v.y) / 2) * r.height };
  }

  /** Height of the surface at a plan point: lawn or plaza inside a block, the paved
   * sidewalk ring, or the road. Used to keep the cats' feet on the ground. */
  groundAt(p: V2): number {
    if (new URLSearchParams(location.search).has("oldground")) return this.blocks.some((b) => pointInPolygon(p, b.tilePoly)) ? TILE_TOP + 0.04 : 0.05;
    for (const b of this.blocks) {
      if (!pointInPolygon(p, b.tilePoly)) continue;
      const k = b.building?.kind ?? "empty";
      if (k === "empty") return TILE_TOP;
      const inner = k === "park" ? b.innerPark : b.inner;
      return pointInPolygon(p, inner) ? TILE_TOP + 0.045 : TILE_TOP;
    }
    if (this.outskirts?.onTile(p)) return TILE_TOP + 0.045;
    return 0.02;
  }

  /** The sidewalk ring around a block, as a closed polyline (crime scenes walk along it). */
  sidewalkRing(i: number): V2[] { const b = this.blocks[i]; if (!b) return []; const r = inset(b.tilePoly, 0.15); return [...r, r[0]]; }
  neighbors(i: number): number[] { return this.adj[i] ?? []; }
  /** Show which bridges are built; a newly built one grows in. */
  setBridges(on: boolean[]) {
    const now = this.clock.getElapsedTime();
    this.bridges.forEach((b, k) => {
      const v = !!on[k];
      if (v && !this.bridgeOn[k]) { b.real.scale.set(1, 0.001, 1); this.anim(b.real, now, 0.6, (o, u) => o.scale.set(1, Math.max(0.001, easeOutBack(u)), 1)); }
      b.real.visible = v;
      b.ghost.visible = !v;
    });
    this.bridgeOn = on.map(Boolean);
    this.transit?.setBridged(this.bridges.filter((_b, k) => on[k]).map((b) => b.seg));
  }

  private bridgeTool = false;
  private hoverBridge: number | null = null;
  /** Unbuilt bridge sites: faint normally, clearer with the Bridge tool, strongest on hover. */
  setBridgeTool(on: boolean) { this.bridgeTool = on; this.refreshBridgeGhosts(); }
  private refreshBridgeGhosts() {
    this.bridges.forEach((b, k) => {
      const op = k === this.hoverBridge ? 0.7 : this.bridgeTool ? 0.5 : 0.16;
      b.ghost.traverse((o) => { if (o instanceof THREE.Mesh) (o.material as THREE.MeshBasicMaterial).opacity = op; });
    });
  }

  /** Lens links: a dotted arc between the two blocks joined by each built bridge. */
  setBridgeLinks(show: boolean) {
    if (this.links) { this.level.remove(this.links); this.links = null; }
    if (!show) return;
    const g = new THREE.Group();
    const m = new GB();
    this.bridges.forEach((b, k) => {
      if (!this.bridgeOn[k]) return;
      const [i, j] = this.segOwners.get(b.seg) ?? [];
      if (i === undefined || j === undefined) return;
      const A = this.blocks[i].center, B = this.blocks[j].center;
      for (let s = 0; s < 14; s += 2) {
        const t0 = s / 14, t1 = (s + 1) / 14;
        const p0 = v2(A.x + (B.x - A.x) * t0, A.y + (B.y - A.y) * t0), p1 = v2(A.x + (B.x - A.x) * t1, A.y + (B.y - A.y) * t1);
        const h0 = 0.6 + Math.sin(t0 * Math.PI) * 0.8, h1 = 0.6 + Math.sin(t1 * Math.PI) * 0.8;
        const d = norm(sub(p1, p0)), n = v2(-d.y * 0.05, d.x * 0.05);
        m.quad(w3(add(p0, n), h0), w3(add(p1, n), h1), w3(sub(p1, n), h1), w3(sub(p0, n), h0), col(C.coral), [0, 1, 0]);
      }
    });
    if (m.empty) return;
    const mesh = new THREE.Mesh(m.build(), new THREE.MeshBasicMaterial({ vertexColors: true, side: THREE.DoubleSide, depthTest: false, transparent: true }));
    mesh.renderOrder = 12;
    g.add(mesh);
    this.level.add(g);
    this.links = g;
  }

  bridgeWalk(site: number) { const b = this.bridges[site]; if (b) this.transit?.bridgeWalk(b.seg); }
  bridgeMid(site: number): V2 | null { const b = this.bridges[site]; return b ? v2((b.a.x + b.b.x) / 2, (b.a.y + b.b.y) / 2) : null; }

  /** The two blocks a bridge would join. */
  bridgeBlocks(site: number): number[] { return this.segOwners.get(this.bridges[site]?.seg ?? -1) ?? []; }

  centerOf(i: number): V2 { return this.blocks[i]?.center ?? v2(0, 0); }
  /** Benches and lawn spots on a block, for idle residents. */
  spotsOf(i: number): LifeSpots { return this.blocks[i]?.spots ?? { benches: [], strolls: [] }; }

  /** Glow on these blocks (open plots you can build on). */
  setGlow(blocks: number[]) {
    this.glowOn = new Set(blocks);
    // while building, the city outside the neighborhood steps back and the district edge shows
    MAT_OUTER.color.setScalar(blocks.length ? 0.68 : 1);
    if (this.border) (this.border.material as THREE.MeshBasicMaterial).opacity = blocks.length ? 0.85 : 0.35;
    this.blocks.forEach((b, i) => { b.glow.visible = this.glowOn.has(i); });
    this.refreshHover();
  }

  setHover(t: Target | null) { this.hovered = t; this.refreshHover(); }

  private refreshHover() {
    const h = this.hovered;
    this.blocks.forEach((b, i) => {
      const hov = h?.kind === "block" && h.i === i;
      b.ring.visible = hov || this.glowOn.has(i);
      (b.ring.material as THREE.MeshBasicMaterial).opacity = hov ? 1 : 0.6;
    });
    this.transit?.setHoverRoute(h?.kind === "route" ? h.i : null);
    this.transit?.setHoverSite(h?.kind === "site" ? h.i : null);
    this.hoverBridge = h?.kind === "bridge" ? h.i : null;
    this.refreshBridgeGhosts();
  }

  /** A small shake: the click did nothing. */
  shake(i: number) {
    const v = this.blocks[i];
    if (!v) return;
    const x0 = v.root.position.x;
    this.anim(v.root, this.clock.getElapsedTime(), 0.32, (o, u) => { o.position.x = x0 + Math.sin(u * Math.PI * 6) * 0.07 * (1 - u); }, () => { v.root.position.x = x0; });
  }

  /** Screen position (CSS px) of a point above a block, a route's middle, or a site. */
  screenOf(t: Target): { x: number; y: number } | null {
    let p: THREE.Vector3;
    if (t.kind === "block") {
      const v = this.blocks[t.i];
      if (!v) return null;
      p = new THREE.Vector3(v.center.x, buildingHeight(v.building ?? { kind: "empty", stories: 0 }) * 0.6 + 0.4, -v.center.y);
    } else if (t.kind === "bridge") {
      const b = this.bridges[t.i];
      if (!b) return null;
      p = new THREE.Vector3((b.a.x + b.b.x) / 2, 0.6, -(b.a.y + b.b.y) / 2);
    } else if (t.kind === "site") {
      const s = this.spots.get(t.i);
      if (!s) return null;
      p = new THREE.Vector3(s.x, 1.1, -s.y);
    } else return null;
    p.project(this.camera);
    const r = this.renderer.domElement.getBoundingClientRect();
    return { x: r.left + ((p.x + 1) / 2) * r.width, y: r.top + ((1 - p.y) / 2) * r.height };
  }

  private anim(obj: THREE.Object3D, start: number, dur: number, step: Anim["step"], done?: () => void) {
    this.anims = this.anims.filter((a) => !(a.obj === obj && a.step.length === step.length && !a.done && !done));
    this.anims.push({ obj, start, dur, step, done });
  }

  /** Wind, clouds, the light of the time of day, and the little lives around town. */
  private living(t: number) {
    U.uTime.value = t;
    const clock = this.transit?.dayClock() ?? null;
    const d = new URLSearchParams(location.search).get("tod");
    const L = lightAt(d !== null ? Number(d) : clock ? clock.phase + clock.u : 1.7);
    this.sun.color.copy(L.sun); this.sun.intensity = L.sunI;
    this.hemi.color.copy(L.hemiSky); this.hemi.groundColor.copy(L.hemiGround); this.hemi.intensity = L.hemiI;
    this.renderer.toneMappingExposure = L.exposure;
    (this.scene.fog as THREE.Fog).color.copy(L.fog);
    U.uNight.value = L.night; U.uCloud.value = 1 - L.night * 0.7; U.uSun.value = 1 - L.night;
    const tg = this.sun.target.position, base = Math.atan2(12, -16) + L.az, R = 25;
    this.sun.position.set(tg.x + Math.cos(base) * R * Math.cos(L.elev), R * Math.sin(L.elev) + 4, tg.z + Math.sin(base) * R * Math.cos(L.elev));
    this.lamps?.update(L.night);
    this.smoke?.update(t, this.camera.quaternion);
    this.farm?.update(t);
    this.birds?.update(t);
  }

  private frameDt = 0.016;
  private lastT = 0;
  private frame() {
    const t = this.clock.getElapsedTime();
    this.frameDt = Math.min(0.05, t - this.lastT); this.lastT = t;
    this.anims = this.anims.filter((a) => {
      const u = (t - a.start) / a.dur;
      if (u < 0) return true;
      a.step(a.obj, Math.min(1, u));
      if (u >= 1) { a.done?.(); return false; }
      return true;
    });
    // glow pulse, feelings bob, little hearts rising from happy homes
    const pulse = 0.22 + 0.12 * Math.sin(t * 3.2);
    for (const v of this.blocks) {
      if (v.glow.visible) (v.glow.material as THREE.MeshBasicMaterial).opacity = pulse;
      if (v.badge) {
        v.badge.position.y = (v.badge.userData.base as number) + Math.sin(t * 2 + v.center.x) * 0.06;
        if (v.feeling === "happy" && t > v.nextHeart) { this.floatHeart(v, t); v.nextHeart = t + 2.5 + Math.random() * 2.5; }
      }
    }
    if (this.transit) {
      this.transit.camQuat.copy(this.camera.quaternion);
      this.transit.camPos.copy(this.camera.position);
      this.transit.setDetail(this.camera.position.distanceTo(this.controls.target), this.radius);
    }
    this.transit?.update(t);
    this.metro?.update(t);
    this.air?.update(t, this.camera.position);
    this.living(t);
    if (this.orbit) { this.cam.goal.az += this.orbit * this.frameDt; this.cam.cur.az += this.orbit * this.frameDt; }
    this.cam.update(this.frameDt);
    this.controls.target.copy(this.cam.cur.target);
    this.onFrame();
    this.renderer.render(this.scene, this.camera);
  }
}

function extrude(poly: V2[], y0: number, y1: number, bevel: number, color: THREE.Color): THREE.Mesh {
  const shape = new THREE.Shape(inset(poly, bevel).map((p) => new THREE.Vector2(p.x, p.y)));
  const depth = Math.max(0.001, y1 - y0 - bevel * 2);
  const g = new THREE.ExtrudeGeometry(shape, { depth, bevelEnabled: bevel > 0, bevelThickness: bevel, bevelSize: bevel, bevelSegments: 3, curveSegments: 4 });
  g.rotateX(-Math.PI / 2);
  g.translate(0, y0 + bevel, 0);
  const m = new THREE.Mesh(g, new THREE.MeshStandardMaterial({ color, roughness: 0.9 }));
  m.receiveShadow = true;
  return m;
}

function sameTarget(a: Target | null, b: Target | null) {
  return a === b || (!!a && !!b && a.kind === b.kind && a.i === b.i);
}

function easeOutBack(x: number): number {
  const c1 = 1.70158, c3 = c1 + 1;
  return 1 + c3 * Math.pow(x - 1, 3) + c1 * Math.pow(x - 1, 2);
}

function heartTexture(): THREE.CanvasTexture {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 128;
  const g = cv.getContext("2d")!;
  const heart = (s: number, color: string) => {
    g.save(); g.translate(64, 68); g.scale(s, s);
    g.beginPath(); g.moveTo(0, 30);
    g.bezierCurveTo(-46, 0, -34, -42, 0, -18);
    g.bezierCurveTo(34, -42, 46, 0, 0, 30);
    g.fillStyle = color; g.fill(); g.restore();
  };
  heart(1.18, "#FFFFFF");
  heart(1, C.coral);
  g.fillStyle = "rgba(255,255,255,0.7)"; g.beginPath(); g.ellipse(48, 52, 9, 6, -0.6, 0, Math.PI * 2); g.fill();
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

function cloudTexture(): THREE.CanvasTexture {
  const cv = document.createElement("canvas");
  cv.width = cv.height = 128;
  const g = cv.getContext("2d")!;
  const blob = (color: string, grow: number) => {
    g.fillStyle = color;
    for (const [x, y, r] of [[44, 70, 22], [66, 58, 28], [88, 72, 20], [64, 80, 22]]) { g.beginPath(); g.arc(x, y, r + grow, 0, Math.PI * 2); g.fill(); }
  };
  blob("#FFFFFF", 5);
  blob("#A9B2C6", 0);
  // a little frown of rain drops
  g.fillStyle = "#7FA8D8";
  for (const x of [52, 68, 84]) { g.beginPath(); g.ellipse(x, 106, 3.5, 6, 0, 0, Math.PI * 2); g.fill(); }
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}

/** The ring of outer segments (used by one block only), as point indices in loop order. */
export function outerLoop(blocks: number[][]): number[] {
  const count = new Map<string, number>();
  const key = (a: number, b: number) => (a < b ? `${a},${b}` : `${b},${a}`);
  for (const loop of blocks) for (let i = 0; i < loop.length; i++) {
    const k = key(loop[i], loop[(i + 1) % loop.length]);
    count.set(k, (count.get(k) ?? 0) + 1);
  }
  const adj = new Map<number, number[]>();
  for (const [k, n] of count) if (n === 1) {
    const [a, b] = k.split(",").map(Number);
    adj.set(a, [...(adj.get(a) ?? []), b]);
    adj.set(b, [...(adj.get(b) ?? []), a]);
  }
  const start = adj.keys().next().value;
  if (start === undefined) return [];
  const loop = [start];
  let prev = -1, cur = start;
  for (;;) {
    const next = (adj.get(cur) ?? []).find((x) => x !== prev);
    if (next === undefined || next === start) break;
    loop.push(next); prev = cur; cur = next;
    if (loop.length > adj.size) break;
  }
  return loop;
}

function disposeTree(o: THREE.Object3D) {
  o.traverse((x) => { if (x instanceof THREE.Mesh) x.geometry.dispose(); });
}


/** A soft vertical sky gradient (screen-space background). */
function skyTexture(): THREE.CanvasTexture {
  const cv = document.createElement("canvas");
  cv.width = 4; cv.height = 256;
  const g = cv.getContext("2d")!;
  const gr = g.createLinearGradient(0, 0, 0, 256);
  gr.addColorStop(0, "#BFE0F7");
  gr.addColorStop(0.55, C.skyHaze);
  gr.addColorStop(1, C.skyHaze);
  g.fillStyle = gr; g.fillRect(0, 0, 4, 256);
  const t = new THREE.CanvasTexture(cv);
  t.colorSpace = THREE.SRGBColorSpace;
  return t;
}
