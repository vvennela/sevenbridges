// The metro line to downtown, and the downtown skyline it comes from. Looks only:
// where the line enters comes from the puzzle (`puzzle.metro.from`) when Lean sends it;
// which block has the station comes from the player's plan.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { add, ccw, dist, mul, norm, sub, v2, type V2 } from "./geom";
import { C, SUBWAY_COLOR } from "./palette";
import { Rng } from "./rng";
import { U, alive } from "./ambient";

const DECK_Y = 1.0;

export class Metro {
  readonly group = new THREE.Group();
  /** The tunnel portal just outside the ring road, where the line goes underground. */
  readonly portal: V2;
  /** Plan points of the viaduct, from downtown to the portal. */
  private line: V2[];
  private train: THREE.Group;
  private branch: THREE.Mesh | null = null;
  private lineLen: number;
  /** The middle of downtown (plan point). */
  readonly downtown: V2;
  private beacons: THREE.InstancedMesh | null = null;

  constructor(parent: THREE.Object3D, center: V2, radius: number, readonly dir: V2, outer: V2[], seed: number) {
    parent.add(this.group);
    const rng = new Rng(seed ^ 0x3e7);
    // where the line meets the town: the ring-road point furthest along `dir`, pushed out a little
    let edge = outer[0];
    for (const q of outer) if ((q.x - center.x) * dir.x + (q.y - center.y) * dir.y > (edge.x - center.x) * dir.x + (edge.y - center.y) * dir.y) edge = q;
    this.portal = add(edge, mul(dir, 1.3));
    // downtown sits far out past the outer city and the meadow; the line ends at its station
    this.downtown = add(center, mul(dir, radius + 64));
    const far = add(this.downtown, mul(dir, -8));
    this.line = [far, add(this.portal, mul(dir, 3.2)), this.portal];
    this.lineLen = dist(far, this.portal);

    const m = new GB();
    const side = v2(-dir.y, dir.x);
    const deckH = (p: V2) => { const s = dist(p, this.portal); return s < 3.2 ? DECK_Y * Math.max(0, (s - 0.4) / 2.8) : DECK_Y; };
    // viaduct: a white deck with a metro-colored stripe, two rails, and round pillars
    const step = 0.8;
    for (let s = 0.4; s < this.lineLen; s += step) {
      const a = add(this.portal, mul(dir, s)), b = add(this.portal, mul(dir, s + step));
      const ya = deckH(a), yb = deckH(b);
      const wd = 0.42;
      const q = (p: V2, k: number) => add(p, mul(side, k));
      m.quad(w3(q(a, -wd), ya), w3(q(b, -wd), yb), w3(q(b, wd), yb), w3(q(a, wd), ya), col(C.white), [0, 1, 0]);
      for (const k of [-wd, wd]) m.quad(w3(q(a, k), ya), w3(q(b, k), yb), w3(q(b, k), yb - 0.16), w3(q(a, k), ya - 0.16), col(SUBWAY_COLOR), [side.x * k, 0, -side.y * k]);
      for (const k of [-0.13, 0.13]) m.quad(w3(q(a, k - 0.02), ya + 0.03), w3(q(b, k - 0.02), yb + 0.03), w3(q(b, k + 0.02), yb + 0.03), w3(q(a, k + 0.02), ya + 0.03), col("#9AA3BE"), [0, 1, 0]);
    }
    for (let s = 3.6; s < this.lineLen; s += 2.4) {
      const p = add(this.portal, mul(dir, s));
      m.geom(SHAPES.cyl, trs(p.x, DECK_Y / 2 - 0.08, -p.y, 0.12, DECK_Y - 0.16, 0.12), col("#EDEAF4"));
    }
    // the tunnel portal: a chunky arch the train slides into
    const ang = Math.atan2(side.y, side.x);
    const pp = add(this.portal, mul(dir, -0.15));
    m.geom(SHAPES.box, trs(pp.x, 0.42, -pp.y, 1.25, 0.84, 0.5, ang), col("#F4F1FA"));
    m.geom(SHAPES.box, trs(pp.x + dir.x * 0.03, 0.32, -(pp.y + dir.y * 0.03), 0.78, 0.64, 0.5, ang), col("#3A3F5C"));
    m.geom(SHAPES.box, trs(pp.x, 0.86, -pp.y, 1.35, 0.1, 0.6, ang), col(SUBWAY_COLOR));
    const mesh = new THREE.Mesh(m.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.8 }));
    mesh.castShadow = true; mesh.receiveShadow = true;
    this.group.add(mesh);

    // the station at the end of the line: an elevated platform with a canopy and stairs
    {
      const st = new GB();
      const S = far, ang2 = Math.atan2(side.y, side.x);
      const at = (al: number, ac: number) => add(add(S, mul(dir, al)), mul(side, ac));
      const P = ccw([at(-1.2, -1.3), at(-1.2, 1.3), at(2.2, 1.3), at(2.2, -1.3)]);
      st.prism(P, DECK_Y - 0.12, DECK_Y, col(C.white), col("#EDEAF4"));
      for (const al of [-0.9, 1.9]) for (const ac of [-1.1, 1.1]) { const q = at(al, ac); st.geom(SHAPES.cyl, trs(q.x, DECK_Y / 2, -q.y, 0.1, DECK_Y, 0.1), col("#EDEAF4")); }
      for (const ac of [-1.1, 1.1]) for (const al of [-0.8, 0.5, 1.8]) { const q = at(al, ac); st.geom(SHAPES.cyl, trs(q.x, DECK_Y + 0.35, -q.y, 0.03, 0.7, 0.03), col("#6B7A99")); }
      const R0 = ccw([at(-1.3, -1.4), at(-1.3, 1.4), at(2.3, 1.4), at(2.3, -1.4)]);
      st.prism(R0, DECK_Y + 0.7, DECK_Y + 0.78, col(SUBWAY_COLOR), col(SUBWAY_COLOR));
      const sq = at(0.4, 1.9);
      st.geom(SHAPES.box, trs(sq.x, DECK_Y / 2, -sq.y, 1.6, DECK_Y, 0.6, ang2 + Math.PI / 2), col("#F4F1FA"));
      const sg = at(-1.25, 0);
      st.geom(SHAPES.cyl, trs(sg.x, DECK_Y + 1.05, -sg.y, 0.22, 0.04, 0.22), col(SUBWAY_COLOR));
      const sm = new THREE.Mesh(st.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.8 }));
      sm.castShadow = true;
      this.group.add(sm);
    }
    this.buildDowntown(rng, side);

    // a little three-car train
    this.train = new THREE.Group();
    const tm = new GB();
    for (let k = 0; k < 3; k++) {
      const x = -k * 0.66;
      tm.geom(SHAPES.box, trs(x, 0.17, 0, 0.6, 0.26, 0.3), col(C.white));
      tm.geom(SHAPES.box, trs(x, 0.09, 0, 0.62, 0.07, 0.32), col(SUBWAY_COLOR));
      tm.geom(SHAPES.box, trs(x, 0.21, 0, 0.5, 0.09, 0.31), col("#6F8FC9"));
    }
    tm.geom(SHAPES.box, trs(0.31, 0.2, 0, 0.04, 0.12, 0.2), col("#6F8FC9"));
    const tmesh = new THREE.Mesh(tm.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.5 }));
    tmesh.castShadow = true;
    this.train.add(tmesh);
    this.group.add(this.train);
  }

  /** Where the metro runs under the town to the station: a dotted line on the ground. */
  setStation(spot: V2 | null) {
    if (this.branch) { this.group.remove(this.branch); this.branch.geometry.dispose(); this.branch = null; }
    if (!spot) return;
    const m = new GB();
    const L = dist(this.portal, spot), d = norm(sub(spot, this.portal)), n = v2(-d.y * 0.07, d.x * 0.07);
    for (let s = 0.2; s < L - 0.2; s += 0.42) {
      const a = add(this.portal, mul(d, s)), b = add(this.portal, mul(d, Math.min(L, s + 0.22)));
      m.quad(w3(add(a, n), 0.24), w3(add(b, n), 0.24), w3(sub(b, n), 0.24), w3(sub(a, n), 0.24), col(SUBWAY_COLOR), [0, 1, 0]);
    }
    this.branch = new THREE.Mesh(m.build(), new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: 0.55, depthWrite: false }));
    this.branch.renderOrder = 4;
    this.group.add(this.branch);
  }

  /** Is a plan point near the viaduct (keeps trees out from under it)? */
  near(p: V2, pad = 1.2): boolean {
    const a = this.portal, d = norm(sub(this.line[0], a));
    const t = (p.x - a.x) * d.x + (p.y - a.y) * d.y;
    if (t < -1 || t > this.lineLen) return false;
    const q = add(a, mul(d, t));
    return dist(p, q) < pad;
  }

  /**
   * Downtown: a natural cluster (tall towers in the middle stepping down to mid-rises and low
   * streets at the edge) in the town's pastel style, slightly desaturated, with window grids that
   * glow at dusk, setbacks and crowns, rooftop water towers and gardens, a clock tower and an
   * art-deco spire. Distance and fog give it atmospheric perspective. One merged mesh.
   */
  private buildDowntown(rng: Rng, side: V2) {
    const D = this.downtown, dir = this.dir;
    const g = new GB();
    // atmospheric perspective, baked in: colors slightly desaturated and lifted toward the sky haze
    // (the material skips scene fog, so facades and window grids stay readable at this distance)
    const gray = new THREE.Color("#C8CCD8"), haze = new THREE.Color(C.skyHaze);
    const soft = (hex: string, k = 0.08) => col("#" + new THREE.Color(hex).lerp(gray, k).lerp(haze, 0.12).getHexString());
    const facades = ["#F7C99A", "#B9D3F2", "#D7C4F2", "#FBE0A6", "#B8E4D2", "#F5B9B0", "#EBDDC6"];
    const win = col("#" + new THREE.Color("#6F8FC9").lerp(haze, 0.22).getHexString());
    U.uWin3.value.copy(win);
    const beacons: V2[] = [], beaconH: number[] = [];
    const rect = (p: V2, w: number, d: number, k = 1) => ccw([add(add(p, mul(side, -w / 2 * k)), mul(dir, -d / 2 * k)), add(add(p, mul(side, w / 2 * k)), mul(dir, -d / 2 * k)), add(add(p, mul(side, w / 2 * k)), mul(dir, d / 2 * k)), add(add(p, mul(side, -w / 2 * k)), mul(dir, d / 2 * k))]);
    /** One tier: walls, a window strip per floor on each face, pillars between windows, a cap. */
    const tier = (p: V2, w: number, d: number, y0: number, y1: number, face: THREE.Color, capC: THREE.Color) => {
      const F = rect(p, w, d);
      g.prism(F, y0, y1, face, capC);
      const fh = 0.62;
      const out = F.map((q) => add(p, mul(sub(q, p), 1.01)));
      for (let y = y0 + 0.24; y + 0.36 < y1; y += fh) g.prism(out, y, y + 0.36, win, null);
      // pillars: the facade color drawn over the window strips, so they read as a grid
      for (let e = 0; e < 4; e++) {
        const a = out[e], b = out[(e + 1) % 4], L = dist(a, b), n = Math.max(2, Math.round(L / 0.42));
        const nrm = norm(v2(b.y - a.y, a.x - b.x)), off = mul(nrm, 0.012);
        for (let j = 1; j < n; j++) {
          const c = add(add(a, mul(sub(b, a), j / n)), off), dd = mul(norm(sub(b, a)), 0.05);
          g.quad(w3(sub(c, dd), y0 + 0.2), w3(add(c, dd), y0 + 0.2), w3(add(c, dd), y1 - 0.1), w3(sub(c, dd), y1 - 0.1), face, [nrm.x, 0, -nrm.y]);
        }
      }
      g.prism(F.map((q) => add(p, mul(sub(q, p), 1.05))), y1 - 0.08, y1 + 0.04, col("#FBFAF6"), col("#F2F0EA"));
      return F;
    };
    const roofProps = (p: V2, w: number, d: number, y: number) => {
      const r = rng.next();
      if (r < 0.3) { // a little water tower on legs
        const q = add(p, add(mul(side, w * 0.2), mul(dir, d * 0.15)));
        for (const [dx, dz] of [[-0.12, -0.12], [0.12, -0.12], [-0.12, 0.12], [0.12, 0.12]]) g.geom(SHAPES.cyl, trs(q.x + dx, y + 0.18, -q.y + dz, 0.02, 0.36, 0.02), col("#8A6A55"));
        g.geom(SHAPES.cyl, trs(q.x, y + 0.5, -q.y, 0.2, 0.32, 0.2), col("#B88A6A"));
        g.geom(SHAPES.cone, trs(q.x, y + 0.74, -q.y, 0.23, 0.16, 0.23), col("#8A6A55"));
      } else if (r < 0.55) { // a rooftop garden
        g.prism(rect(p, w * 0.7, d * 0.7), y, y + 0.08, soft("#8FCB7A"), soft("#8FCB7A"));
        for (let k = 0; k < 3; k++) { const q = add(p, add(mul(side, rng.range(-w, w) * 0.25), mul(dir, rng.range(-d, d) * 0.25))); g.geom(SHAPES.ball, trs(q.x, y + 0.28, -q.y, 0.2, 0.2, 0.2), soft(C.leaf)); }
      } else if (r < 0.75) { // antenna
        g.geom(SHAPES.cyl, trs(p.x, y + 0.9, -p.y, 0.035, 1.8, 0.035), col("#D8D4E2"));
        return y + 1.8;
      }
      return y;
    };
    const tower = (p: V2, h: number, w: number, d: number) => {
      const face = soft(rng.pick(facades)), capC = col("#F2F0EA");
      const tiers = h > 12 ? 3 : h > 7 ? 2 : 1;
      let y = 0, cw = w, cd = d, top = h;
      for (let t2 = 0; t2 < tiers; t2++) {
        const th = t2 === tiers - 1 ? h - y : h * (t2 === 0 ? 0.55 : 0.28);
        tier(p, cw, cd, y, y + th, face, capC);
        y += th; cw *= 0.74; cd *= 0.74;
      }
      top = roofProps(p, cw / 0.74, cd / 0.74, y);
      if (h > 13) { beacons.push(p); beaconH.push(top + 0.15); }
    };
    // the cluster: tall in the middle, stepping down to the edges
    const placed: { p: V2; r: number }[] = [];
    const free = (p: V2, r: number) => placed.every((q) => dist(q.p, p) > q.r + r) && dist(p, this.line[0]) > r + 2.6 && !this.near(p, r + 1.4);
    for (let k = 0; k < 260 && placed.length < 46; k++) {
      const rr = Math.pow(rng.next(), 0.75) * 20, a = rng.range(0, Math.PI * 2);
      const p = add(D, v2(Math.cos(a) * rr, Math.sin(a) * rr));
      const w = rng.range(1.7, 3.1), d = rng.range(1.7, 2.9);
      if (!free(p, Math.hypot(w, d) / 2 + 0.35)) continue;
      const h = 2.5 + 14 * Math.pow(Math.max(0, 1 - rr / 21), 1.4) * rng.range(0.75, 1.15);
      placed.push({ p, r: Math.hypot(w, d) / 2 + 0.35 });
      tower(p, h, w, d);
    }
    // landmarks: an art-deco spire in the middle, and a clock tower to one side
    {
      const p = add(D, mul(side, 0.5));
      if (free(p, 1.6)) {
        let y = 0;
        const face = soft("#F2E3C6");
        for (const [w, h] of [[3.0, 7], [2.3, 4], [1.6, 3], [1.0, 2.4]] as const) { tier(p, w, w, y, y + h, face, col("#F7EFD9")); y += h; }
        g.geom(SHAPES.cone, trs(p.x, y + 2.2, -p.y, 0.45, 4.4, 0.45), col("#E8C26A"));
        beacons.push(p); beaconH.push(y + 4.5);
        placed.push({ p, r: 2.2 });
      }
      const q = add(add(D, mul(side, -9)), mul(dir, -3));
      if (free(q, 1.2)) {
        tier(q, 1.6, 1.6, 0, 11, soft("#F3D0CB"), col("#F7EFE9"));
        for (let e = 0; e < 4; e++) { // clock faces
          const n = [dir, side, mul(dir, -1), mul(side, -1)][e];
          const c = add(q, mul(n, 0.83));
          const ang = Math.atan2(n.x, n.y);
          g.geom(SHAPES.cyl, new THREE.Matrix4().compose(new THREE.Vector3(c.x, 10.1, -c.y), new THREE.Quaternion().setFromEuler(new THREE.Euler(Math.PI / 2, ang, 0, "YXZ")), new THREE.Vector3(0.55, 0.04, 0.55)), col("#FFFDF5"));
          g.geom(SHAPES.box, trs(c.x + n.x * 0.03, 10.25, -(c.y + n.y * 0.03), 0.05, 0.32, 0.02, ang), col(C.ink));
        }
        g.geom(SHAPES.cone, trs(q.x, 12.0, -q.y, 1.25, 2.0, 1.25), col(C.coral));
        placed.push({ p: q, r: 1.4 });
      }
    }
    // the low city around it: small buildings, trees and streets, so the skyline stands on a town
    for (let k = 0; k < 220; k++) {
      const rr = rng.range(17, 32), a = rng.range(0, Math.PI * 2);
      const p = add(D, v2(Math.cos(a) * rr, Math.sin(a) * rr));
      if (!free(p, 0.9)) continue;
      if (rng.chance(0.3)) { g.geom(SHAPES.ball, trs(p.x, 0.6, -p.y, 0.5, 0.5, 0.5), soft(rng.pick([C.leaf, "#6FCB72"]))); g.geom(SHAPES.cyl, trs(p.x, 0.2, -p.y, 0.07, 0.4, 0.07), col(C.trunk)); placed.push({ p, r: 0.5 }); continue; }
      const w = rng.range(1, 1.8), h = rng.range(0.7, 2.2);
      const F = rect(p, w, w * 0.8);
      g.prism(F, 0, h, soft(rng.pick(facades), 0.25), col("#F2F0EA"));
      g.prism(F.map((q) => add(p, mul(sub(q, p), 1.01))), h * 0.4, h * 0.4 + 0.22, win, null);
      if (rng.chance(0.5)) g.geom(SHAPES.cone, trs(p.x, h + 0.3, -p.y, w * 0.6, 0.6, w * 0.6), soft(rng.pick([C.coral, "#E0707E", "#F59A6B"]), 0.25));
      placed.push({ p, r: 0.7 });
    }
    // streets on the ground, and a road leading in beside the metro
    const road = (a: V2, b: V2, wd: number) => { const d0 = norm(sub(b, a)), n = v2(-d0.y * wd / 2, d0.x * wd / 2); g.quad(w3(add(a, n), 0.02), w3(add(b, n), 0.02), w3(sub(b, n), 0.02), w3(sub(a, n), 0.02), col(C.road), [0, 1, 0]); };
    road(add(this.portal, add(mul(dir, 8), mul(side, 1.6))), add(D, mul(side, 1.6)), 0.7);
    for (const rr of [9, 16, 24]) for (let k = 0; k < 36; k++) {
      const a0 = (k / 36) * Math.PI * 2, a1 = ((k + 1) / 36) * Math.PI * 2;
      road(add(D, v2(Math.cos(a0) * rr, Math.sin(a0) * rr)), add(D, v2(Math.cos(a1) * rr, Math.sin(a1) * rr)), 0.5);
    }
    g.prism(Array.from({ length: 40 }, (_, k) => add(D, v2(Math.cos((k / 40) * 6.283) * 33, Math.sin((k / 40) * 6.283) * 33))), -0.005, 0.005, soft("#C9DDB2", 0.1), soft("#C9DDB2", 0.1));
    const mesh = new THREE.Mesh(g.build(), alive(new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.9, fog: false }), { windows: true }));
    this.group.add(mesh);
    // aviation lights on the tallest, blinking
    this.beacons = new THREE.InstancedMesh(new THREE.SphereGeometry(0.16, 8, 6), new THREE.MeshBasicMaterial({ color: col("#FF4A3D"), toneMapped: false }), Math.max(1, beacons.length));
    const m4 = new THREE.Matrix4();
    beacons.forEach((p, i) => { m4.makeTranslation(p.x, beaconH[i], -p.y); this.beacons!.setMatrixAt(i, m4); });
    this.beacons.count = beacons.length;
    this.group.add(this.beacons);
    // a soft haze at the base, so the towers fade into the ground
    const tex = new THREE.CanvasTexture((() => { const cv = document.createElement("canvas"); cv.width = 128; cv.height = 64; const c2 = cv.getContext("2d")!; const gr = c2.createRadialGradient(64, 32, 4, 64, 32, 62); gr.addColorStop(0, "rgba(255,255,255,0.85)"); gr.addColorStop(1, "rgba(255,255,255,0)"); c2.fillStyle = gr; c2.fillRect(0, 0, 128, 64); return cv; })());
    for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2, rr = 22 + (k % 3) * 4;
      const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, color: col(C.skyHaze), transparent: true, opacity: 0.7, depthWrite: false }));
      sp.position.set(D.x + Math.cos(a) * rr, 1.6, -(D.y + Math.sin(a) * rr));
      sp.scale.set(26, 5, 1);
      this.group.add(sp);
    }
  }

  /** The train shuttles from downtown into the tunnel and back, pausing at each end. */
  update(t: number) {
    if (this.beacons) this.beacons.visible = Math.sin(t * 3.2) > -0.2; // aviation lights blink
    const v = 4, run = this.lineLen / v, pause = 3, P = 2 * (run + pause);
    const u = ((t % P) + P) % P;
    let s: number;
    let inbound = true;
    if (u < run) s = this.lineLen - u * v;
    else if (u < run + pause) s = -2;
    else if (u < 2 * run + pause) { s = (u - run - pause) * v; inbound = false; }
    else s = this.lineLen;
    s = Math.min(s, this.lineLen - 0.2);
    const p = add(this.portal, mul(this.dir, Math.max(-2, s)));
    const y = s < 3.2 ? DECK_Y * Math.max(0, (s - 0.4) / 2.8) - (s < 0.4 ? 0.6 : 0) : DECK_Y;
    this.train.visible = s > -0.5;
    this.train.position.set(p.x, y, -p.y);
    const head = inbound ? mul(this.dir, -1) : this.dir;
    this.train.rotation.y = Math.atan2(head.y, head.x);
  }
}
