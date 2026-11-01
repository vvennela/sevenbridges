// The city around the playable neighborhood, and life in the countryside beyond it.
// None of this is part of the puzzle: the outer blocks can't be built on or clicked,
// and nothing here affects a score. It is all drawn into a few merged/instanced meshes.
import * as THREE from "three";
import { mergeGeometries } from "three/examples/jsm/utils/BufferGeometryUtils.js";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { MAT_GLOW, MAT_MAIN, TILE_TOP, makeBuilding, type LifeSpots } from "./buildings";
import { add, ccw, centroid, dist, inset, mul, norm, pointInPolygon, segDist, sub, v2, type V2 } from "./geom";
import { C } from "./palette";
import { Rng } from "./rng";
import { U, alive } from "./ambient";
import type { Building, Kind } from "./types";

/** Outer blocks share one material, so they can dim together when a building tool is picked. */
export const MAT_OUTER = alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.85 }), { wind: true, clouds: true, windows: true });

const ROAD = 0.56;

export interface Outskirts {
  group: THREE.Group;
  /** Streets cars can loop on (land only). */
  streets: [V2, V2][];
  /** Spots for lamp posts. */
  lamps: V2[];
  /** Places for a few idle cats. */
  idle: V2[];
  /** Is this point covered by an outer block or street (keep trees out)? */
  covers: (p: V2) => boolean;
  /** Is this point on a raised outer tile (cats stand at tile height there)? */
  onTile: (p: V2) => boolean;
}

/**
 * Two rings of city blocks around the town: a dense one, then a thinner one that fades into fields.
 * `avoid(p)` keeps blocks off the river, the metro line and the lanes out of town.
 */
export function buildOutskirts(parent: THREE.Object3D, outer: V2[], c: V2, seed: number, avoid: (p: V2) => boolean): Outskirts {
  const rng = new Rng(seed ^ 0x0c17);
  const group = new THREE.Group();
  parent.add(group);
  // resample the ring road with outward normals
  const loop: { p: V2; n: V2 }[] = [];
  for (let i = 0; i < outer.length; i++) {
    const a = outer[i], b = outer[(i + 1) % outer.length];
    const L = dist(a, b), k = Math.max(1, Math.round(L / 0.5));
    for (let j = 0; j < k; j++) loop.push({ p: add(a, mul(sub(b, a), j / k)), n: v2(0, 0) });
  }
  loop.forEach((q, i) => {
    const a = loop[(i - 2 + loop.length) % loop.length].p, b = loop[(i + 2) % loop.length].p;
    const d = norm(sub(b, a));
    let n = v2(d.y, -d.x); // CCW loop → right-hand normal points out
    if ((q.p.x - c.x) * n.x + (q.p.y - c.y) * n.y < 0) n = mul(n, -1);
    q.n = n;
  });
  const arc: number[] = [0];
  for (let i = 1; i < loop.length; i++) arc.push(arc[i - 1] + dist(loop[i - 1].p, loop[i].p));
  const total = arc[arc.length - 1] + dist(loop[loop.length - 1].p, loop[0].p);
  const at = (s: number, d: number): V2 => {
    s = ((s % total) + total) % total;
    let i = 0;
    while (i < arc.length - 1 && arc[i + 1] <= s) i++;
    const q = loop[i];
    return add(q.p, mul(q.n, d));
  };

  const all = new GB(), glow = new GB();
  const pieces: THREE.BufferGeometry[] = [], glows: THREE.BufferGeometry[] = [];
  const streets: [V2, V2][] = [], lamps: V2[] = [], idle: V2[] = [];
  const polys: V2[][] = [], tiles: V2[][] = [];
  const roadStrips: [V2, V2][] = [];
  const road = (a: V2, b: V2, w = ROAD) => {
    const d = norm(sub(b, a)), n = v2(-d.y * w / 2, d.x * w / 2);
    all.quad(w3(add(a, n), 0.02), w3(add(b, n), 0.02), w3(sub(b, n), 0.02), w3(sub(a, n), 0.02), col(C.road), [0, 1, 0]);
    roadStrips.push([a, b]);
  };
  const rings = [{ d0: 0.62, d1: 4.3, built: 0.9, step: 3.4 }, { d0: 4.9, d1: 8.4, built: 0.55, step: 3.8 }];
  const kinds: [Kind, number, number][] = [["housing", 0.48, 3], ["shop", 0.14, 2], ["office", 0.1, 3], ["park", 0.12, 1], ["food", 0.08, 1], ["bar", 0.04, 1]];
  rings.forEach((ring, ri) => {
    const n = Math.max(6, Math.round(total / ring.step));
    const len = total / n;
    for (let k = 0; k < n; k++) {
      const s0 = k * len + 0.3, s1 = (k + 1) * len - 0.3;
      const poly = ccw([at(s0, ring.d0), at(s1, ring.d0), at(s1, ring.d1), at(s0, ring.d1)]);
      const mid = centroid(poly);
      const bad = [...poly, mid].some(avoid);
      // the road along the outer edge of this ring, and the cross street before this block
      const ra = at(k * len, ring.d1 + 0.3), rb = at((k + 1) * len, ring.d1 + 0.3);
      if (!avoid(ra) && !avoid(rb) && !avoid(add(mul(ra, 0.5), mul(rb, 0.5)))) { road(ra, rb); streets.push([ra, rb]); if (k % 2 === 0) lamps.push(at(k * len, ring.d1 - 0.05)); }
      const ca = at(k * len, ring.d0 - 0.3), cb = at(k * len, ring.d1 + 0.3);
      if (!avoid(ca) && !avoid(cb)) { road(ca, cb, 0.46); if (ri === 0 && k % 3 === 0) streets.push([ca, cb]); }
      if (bad || !rng.chance(ring.built)) {
        // gardens and fields where the city thins out
        if (!bad) { all.prism(inset(poly, 0.1), 0, 0.03, col("#A9D68C"), col("#A6D486")); polys.push(poly); for (let j = 0; j < 3; j++) treeAt(all, add(mid, v2(rng.range(-1, 1), rng.range(-1, 1))), rng); }
        continue;
      }
      polys.push(poly);
      const tile = inset(poly, 0.06);
      tiles.push(tile);
      all.prism(tile, 0, TILE_TOP - 0.02, col(C.curb), col(C.curb));
      all.prism(inset(tile, 0.1), TILE_TOP - 0.03, TILE_TOP, col("#EFE9DB"), col("#EFE9DB"));
      // pick a kind: busier near town, mostly homes and parks further out
      let r = rng.next(), kind: Kind = "housing", maxS = 2;
      if (ri === 1) { kind = r < 0.75 ? "housing" : "park"; maxS = 2; }
      else for (const [kk, w, m] of kinds) { if (r < w) { kind = kk; maxS = m; break; } r -= w; }
      const b: Building = { kind, stories: kind === "park" || kind === "bar" || kind === "food" ? 1 : rng.int(1, ri === 0 ? maxS : 1) };
      const spots: LifeSpots = { benches: [], strolls: [] };
      const ps = makeBuilding(b, { poly: tile, center: centroid(tile), rng: new Rng(seed ^ (ri * 977 + k * 131)), spots, index: k, townSalt: seed % 5 });
      for (const pc of ps) {
        pc.obj.updateMatrixWorld(true);
        pc.obj.traverse((o) => {
          if (!(o instanceof THREE.Mesh)) return;
          const g = o.geometry.clone().applyMatrix4(o.matrixWorld);
          (o.material === MAT_GLOW ? glows : pieces).push(g);
          o.geometry.dispose();
        });
      }
      if (spots.strolls.length) idle.push(spots.strolls[0]);
    }
  });
  pieces.push(all.build());
  const merged = mergeGeometries(pieces.map((g) => (g.index ? g.toNonIndexed() : g)));
  if (merged) {
    const mesh = new THREE.Mesh(merged, MAT_OUTER);
    mesh.castShadow = true; mesh.receiveShadow = true;
    group.add(mesh);
  }
  if (glows.length) { const mg = mergeGeometries(glows.map((g) => (g.index ? g.toNonIndexed() : g))); if (mg) group.add(new THREE.Mesh(mg, MAT_GLOW)); }
  void glow; void MAT_MAIN;
  const covers = (p: V2) => polys.some((q) => pointInPolygon(p, q)) || roadStrips.some(([a, b]) => segDist(p, a, b) < 0.5);
  return { group, streets, lamps, idle, covers, onTile: (p: V2) => tiles.some((q) => pointInPolygon(p, q)) };
}

function treeAt(m: GB, p: V2, rng: Rng) {
  m.sway = 1; m.swayBase = 0.03;
  const s = rng.range(0.8, 1.2);
  m.geom(SHAPES.cyl, trs(p.x, 0.16 * s, -p.y, 0.05 * s, 0.32 * s, 0.05 * s), col(C.trunk));
  m.geom(SHAPES.ball, trs(p.x, 0.5 * s, -p.y, 0.3 * s, 0.28 * s, 0.3 * s, rng.range(0, 6)), col(rng.pick([C.leaf, "#6FCB72", "#57B567"])));
  m.sway = 0;
}

// ---------- countryside life ----------

/** Lamp posts whose heads and light pools glow at dusk. */
export class Lamps {
  readonly group = new THREE.Group();
  private heads: THREE.InstancedMesh;
  private pools: THREE.InstancedMesh;
  constructor(parent: THREE.Object3D, spots: V2[]) {
    parent.add(this.group);
    const n = Math.max(1, spots.length);
    const poles = new THREE.InstancedMesh(new THREE.CylinderGeometry(0.022, 0.03, 0.75, 6).translate(0, 0.375, 0), new THREE.MeshStandardMaterial({ color: col("#6B7A99"), roughness: 0.6 }), n);
    this.heads = new THREE.InstancedMesh(new THREE.SphereGeometry(0.07, 10, 8).translate(0, 0.78, 0), new THREE.MeshBasicMaterial({ color: col("#F4F1E8"), toneMapped: false }), n);
    const pool = new THREE.CanvasTexture((() => { const cv = document.createElement("canvas"); cv.width = cv.height = 64; const g = cv.getContext("2d")!; const gr = g.createRadialGradient(32, 32, 2, 32, 32, 31); gr.addColorStop(0, "rgba(255,214,140,0.9)"); gr.addColorStop(1, "rgba(255,214,140,0)"); g.fillStyle = gr; g.fillRect(0, 0, 64, 64); return cv; })());
    this.pools = new THREE.InstancedMesh(new THREE.PlaneGeometry(1.5, 1.5).rotateX(-Math.PI / 2).translate(0, 0.04, 0), new THREE.MeshBasicMaterial({ map: pool, transparent: true, opacity: 0, depthWrite: false, blending: THREE.AdditiveBlending }), n);
    this.pools.renderOrder = 3;
    const m = new THREE.Matrix4();
    spots.forEach((p, i) => { m.makeTranslation(p.x, 0, -p.y); poles.setMatrixAt(i, m); this.heads.setMatrixAt(i, m); this.pools.setMatrixAt(i, m); });
    for (const im of [poles, this.heads, this.pools]) { im.count = spots.length; this.group.add(im); }
    poles.castShadow = true;
  }
  update(night: number) {
    (this.heads.material as THREE.MeshBasicMaterial).color.copy(col("#F4F1E8")).lerp(col("#FFD27A"), night);
    (this.pools.material as THREE.MeshBasicMaterial).opacity = night * 0.55;
  }
}

/** Birds: a small flock crosses the sky now and then, flapping. */
export class Birds {
  private wings: THREE.InstancedMesh;
  private n = 9;
  constructor(parent: THREE.Object3D, private c: V2, private R: number, private seed: number) {
    const g = new THREE.BufferGeometry();
    // one wing: a thin triangle from the body out to the tip (mirrored per instance)
    g.setAttribute("position", new THREE.Float32BufferAttribute([0, 0, -0.05, 0, 0, 0.06, 0.32, 0, 0.0], 3));
    g.computeVertexNormals();
    this.wings = new THREE.InstancedMesh(g, new THREE.MeshBasicMaterial({ color: col("#4A5470"), side: THREE.DoubleSide }), this.n * 2);
    this.wings.frustumCulled = false;
    parent.add(this.wings);
  }
  update(t: number) {
    const P = 34, k = Math.floor(t / P), u = (t % P) / P;
    const rng = new Rng(this.seed ^ (k * 7919));
    const a = rng.range(0, Math.PI * 2), side = rng.range(-0.5, 0.5);
    const dir = v2(Math.cos(a), Math.sin(a)), perp = v2(-dir.y, dir.x);
    const span = this.R * 6;
    const head = add(add(this.c, mul(perp, side * this.R * 2)), mul(dir, (u - 0.5) * span));
    const m = new THREE.Matrix4(), q = new THREE.Quaternion(), e = new THREE.Euler();
    for (let i = 0; i < this.n; i++) {
      // a loose V
      const row = Math.ceil(i / 2), sgn = i % 2 ? 1 : -1;
      const p = add(add(head, mul(dir, -row * 0.9)), mul(perp, sgn * row * 0.7 + Math.sin(t * 0.7 + i) * 0.15));
      const y = 7 + Math.sin(t * 0.5 + i * 1.3) * 0.4;
      const flap = Math.sin(t * 9 + i * 0.8) * 0.6;
      for (const w of [0, 1]) {
        e.set(0, Math.atan2(dir.y, dir.x) + (w ? Math.PI : 0), 0, "YXZ");
        q.setFromEuler(e);
        const qq = new THREE.Quaternion().setFromAxisAngle(new THREE.Vector3(1, 0, 0), 0).multiply(q);
        m.compose(new THREE.Vector3(p.x, y, -p.y), qq, new THREE.Vector3(1, 1, 1));
        // tilt the wing up/down around the body axis
        m.multiply(new THREE.Matrix4().makeRotationZ((w ? -1 : 1) * flap));
        // turn the wing to point sideways from the body
        m.multiply(new THREE.Matrix4().makeRotationY(Math.PI / 2));
        this.wings.setMatrixAt(i * 2 + w, m);
      }
    }
    this.wings.instanceMatrix.needsUpdate = true;
    this.wings.visible = u > 0.02 && u < 0.98;
  }
}

/** Puffs of chimney smoke rising from far cottages. */
export class Smoke {
  private puffs: THREE.InstancedMesh;
  constructor(parent: THREE.Object3D, private spots: { p: V2; h: number }[]) {
    const tex = new THREE.CanvasTexture((() => { const cv = document.createElement("canvas"); cv.width = cv.height = 64; const g = cv.getContext("2d")!; const gr = g.createRadialGradient(32, 32, 2, 32, 32, 30); gr.addColorStop(0, "rgba(255,255,255,0.9)"); gr.addColorStop(1, "rgba(255,255,255,0)"); g.fillStyle = gr; g.fillRect(0, 0, 64, 64); return cv; })());
    this.puffs = new THREE.InstancedMesh(new THREE.PlaneGeometry(1, 1), new THREE.MeshBasicMaterial({ map: tex, color: col("#F2F0F4"), transparent: true, opacity: 0.75, depthWrite: false }), Math.max(1, spots.length * 4));
    this.puffs.frustumCulled = false;
    parent.add(this.puffs);
  }
  update(t: number, cam: THREE.Quaternion) {
    const m = new THREE.Matrix4();
    let k = 0;
    this.spots.forEach((s, i) => {
      for (let j = 0; j < 4; j++) {
        const u = ((t * 0.12 + j / 4 + i * 0.37) % 1 + 1) % 1;
        const sz = 0.12 + u * 0.45;
        const fade = Math.sin(u * Math.PI);
        m.compose(new THREE.Vector3(s.p.x + u * 0.5 + Math.sin(t + j) * 0.05, s.h + u * 1.4, -s.p.y - u * 0.2), cam, new THREE.Vector3(sz * fade, sz * fade, 1));
        this.puffs.setMatrixAt(k++, m);
      }
    });
    this.puffs.count = k;
    this.puffs.instanceMatrix.needsUpdate = true;
  }
}

/** A windmill whose sails turn, and a few sheep grazing in a fenced pasture next to crop fields. */
export class Farm {
  readonly group = new THREE.Group();
  private sails = new THREE.Group();
  private sheep: THREE.InstancedMesh;
  private heads: THREE.InstancedMesh;
  private flock: { c: V2; r: number; ph: number; sp: number }[] = [];
  constructor(parent: THREE.Object3D, at: V2, face: V2, rng: Rng) {
    parent.add(this.group);
    const m = new GB();
    const side = v2(-face.y, face.x);
    // crop fields: two plots of rows, and a pasture with a fence
    const plot = (p: V2, w: number, d: number, a: string, b: string) => {
      const P = [add(add(p, mul(side, -w / 2)), mul(face, -d / 2)), add(add(p, mul(side, w / 2)), mul(face, -d / 2)), add(add(p, mul(side, w / 2)), mul(face, d / 2)), add(add(p, mul(side, -w / 2)), mul(face, d / 2))];
      m.prism(P, 0, 0.025, col(a), col(a));
      const rows = Math.floor(w / 0.35);
      for (let i = 0; i < rows; i++) {
        const q = add(p, mul(side, -w / 2 + (i + 0.5) * (w / rows)));
        const ang = Math.atan2(face.y, face.x);
        m.geom(SHAPES.box, trs(q.x, 0.05, -q.y, d * 0.92, 0.05, 0.14, ang), col(b));
      }
    };
    plot(add(at, mul(side, -4.2)), 4, 3, "#C8A57A", "#8DBF5E");
    plot(add(add(at, mul(side, -4.2)), mul(face, 3.4)), 4, 3, "#E6C873", "#F2D98A");
    // pasture fence
    const pc = add(at, mul(side, 3.6));
    const corners = [add(add(pc, mul(side, -2.4)), mul(face, -2)), add(add(pc, mul(side, 2.4)), mul(face, -2)), add(add(pc, mul(side, 2.4)), mul(face, 2)), add(add(pc, mul(side, -2.4)), mul(face, 2))];
    for (let i = 0; i < 4; i++) {
      const a = corners[i], b = corners[(i + 1) % 4], L = dist(a, b), d = norm(sub(b, a));
      for (let s = 0; s <= L; s += 0.5) { const q = add(a, mul(d, s)); m.geom(SHAPES.box, trs(q.x, 0.13, -q.y, 0.05, 0.26, 0.05), col("#B98B6A")); }
      const md = add(a, mul(d, L / 2));
      m.geom(SHAPES.box, trs(md.x, 0.2, -md.y, L, 0.03, 0.03, Math.atan2(d.y, d.x)), col("#C99A72"));
    }
    // windmill: a white tower with a cap
    m.geom(SHAPES.cyl, trs(at.x, 0.9, -at.y, 0.42, 1.8, 0.42), col("#FFF8EC"));
    m.geom(SHAPES.cone, trs(at.x, 2.05, -at.y, 0.5, 0.5, 0.5), col(C.coral));
    m.geom(SHAPES.box, trs(at.x + face.x * 0.41, 0.25, -(at.y + face.y * 0.41), 0.25, 0.4, 0.04, Math.atan2(face.x, face.y)), col("#8A5A3B"));
    const mesh = new THREE.Mesh(m.build(), alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.9 }), { clouds: true }));
    mesh.castShadow = true; mesh.receiveShadow = true;
    this.group.add(mesh);
    const sm = new GB();
    for (let k = 0; k < 4; k++) {
      const a = (k / 4) * Math.PI * 2;
      const tip = v2(Math.cos(a), Math.sin(a));
      const mat = new THREE.Matrix4().makeRotationZ(a).multiply(new THREE.Matrix4().makeTranslation(0.65, 0, 0)).multiply(new THREE.Matrix4().makeScale(1.2, 0.26, 0.02));
      sm.geom(SHAPES.box, mat, col(k % 2 ? "#FFFFFF" : "#F7E6D0"));
      void tip;
    }
    sm.geom(SHAPES.ballLo, new THREE.Matrix4().makeScale(0.1, 0.1, 0.1), col("#8A5A3B"));
    this.sails.add(new THREE.Mesh(sm.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.8, side: THREE.DoubleSide })));
    this.sails.position.set(at.x + face.x * 0.5, 1.75, -(at.y + face.y * 0.5));
    this.sails.rotation.y = Math.atan2(face.x, face.y);
    this.group.add(this.sails);
    // sheep: a woolly body and a dark head, wandering slowly
    const n = 7;
    this.sheep = new THREE.InstancedMesh(new THREE.IcosahedronGeometry(0.17, 1).scale(1.3, 0.95, 1), new THREE.MeshStandardMaterial({ color: col("#FBFAF6"), roughness: 1 }), n);
    this.heads = new THREE.InstancedMesh(new THREE.SphereGeometry(0.075, 8, 6).scale(1.1, 1, 0.9), new THREE.MeshStandardMaterial({ color: col("#3E3A44"), roughness: 0.9 }), n);
    for (let i = 0; i < n; i++) this.flock.push({ c: add(pc, add(mul(side, rng.range(-1.6, 1.6)), mul(face, rng.range(-1.3, 1.3)))), r: rng.range(0.15, 0.5), ph: rng.range(0, 6), sp: rng.range(0.05, 0.12) * (rng.chance(0.5) ? 1 : -1) });
    for (const im of [this.sheep, this.heads]) { im.castShadow = true; im.frustumCulled = false; this.group.add(im); }
  }
  update(t: number) {
    this.sails.rotation.z = -t * 0.9;
    const m = new THREE.Matrix4(), q = new THREE.Quaternion();
    this.flock.forEach((s, i) => {
      const a = s.ph + t * s.sp;
      const p = add(s.c, v2(Math.cos(a) * s.r, Math.sin(a) * s.r));
      const h = Math.atan2(-Math.sin(a) * Math.sign(s.sp), Math.cos(a) * Math.sign(s.sp));
      q.setFromAxisAngle(new THREE.Vector3(0, 1, 0), h);
      m.compose(new THREE.Vector3(p.x, 0.2, -p.y), q, new THREE.Vector3(1, 1, 1));
      this.sheep.setMatrixAt(i, m);
      // grazing: the head dips now and then
      const graze = Math.max(0, Math.sin(t * 0.7 + s.ph * 3)) * 0.12;
      const fwd = new THREE.Vector3(0.24, 0.08 - graze, 0).applyQuaternion(q);
      m.compose(new THREE.Vector3(p.x + fwd.x, 0.2 + fwd.y, -p.y + fwd.z), q, new THREE.Vector3(1, 1, 1));
      this.heads.setMatrixAt(i, m);
    });
    this.sheep.instanceMatrix.needsUpdate = true;
    this.heads.instanceMatrix.needsUpdate = true;
  }
}

export { U };
