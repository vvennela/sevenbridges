// The metro line to downtown, and the downtown skyline it comes from. Looks only:
// where the line enters comes from the puzzle (`puzzle.metro.from`) when Lean sends it;
// which block has the station comes from the player's plan.
import * as THREE from "three";
import { GB, SHAPES, col, trs, w3 } from "./builder";
import { add, dist, mul, norm, sub, v2, type V2 } from "./geom";
import { C, SUBWAY_COLOR } from "./palette";
import { Rng } from "./rng";

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

  constructor(parent: THREE.Object3D, center: V2, radius: number, readonly dir: V2, outer: V2[], seed: number) {
    parent.add(this.group);
    const rng = new Rng(seed ^ 0x3e7);
    // where the line meets the town: the ring-road point furthest along `dir`, pushed out a little
    let edge = outer[0];
    for (const q of outer) if ((q.x - center.x) * dir.x + (q.y - center.y) * dir.y > (edge.x - center.x) * dir.x + (edge.y - center.y) * dir.y) edge = q;
    this.portal = add(edge, mul(dir, 1.3));
    const far = add(center, mul(dir, radius + 90));
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

    // downtown: a cluster of tall towers around the far end of the line
    const sky = new GB();
    // pastel towers, pre-mixed toward the sky haze (atmospheric distance without fog washing them out)
    const haze = new THREE.Color(C.skyHaze);
    const distant = (hex: string, k = 0.3) => "#" + new THREE.Color(hex).lerp(haze, k).getHexString();
    const tones = ["#A9C3EA", "#C3B4EC", "#9FC0E6", "#D4C6F0", "#B5D0EE", "#F2C9B8"].map((h) => distant(h));
    const base = add(center, mul(dir, radius + 16));
    for (let k = 0; k < 34; k++) {
      const along = rng.range(0, 22), across = rng.range(-16, 16) * (0.5 + along / 30);
      const p = add(add(base, mul(dir, along)), mul(side, across));
      if (Math.abs(across) < 1.4 && along < 12) continue; // keep the line clear
      const w = rng.range(1.4, 2.8), d = rng.range(1.4, 2.6);
      const h = rng.range(4, 9) + (1 - Math.min(1, Math.abs(across) / 16)) * rng.range(3, 10);
      const tone = col(rng.pick(tones));
      const F = [add(add(p, mul(side, -w / 2)), mul(dir, -d / 2)), add(add(p, mul(side, w / 2)), mul(dir, -d / 2)), add(add(p, mul(side, w / 2)), mul(dir, d / 2)), add(add(p, mul(side, -w / 2)), mul(dir, d / 2))];
      sky.prism(F, 0, h, tone, col("#F2F0FA"));
      // window bands
      for (let y = 0.8; y < h - 0.4; y += 0.9) sky.prism(F.map((q) => add(p, mul(sub(q, p), 1.012))), y, y + 0.3, col(distant("#7E9CCB", 0.35)), null);
      if (rng.chance(0.3)) {
        const top = h + rng.range(0.6, 1.6);
        sky.prism(F.map((q) => add(p, mul(sub(q, p), 0.6))), h, top, tone, col("#F2F0FA"));
        if (rng.chance(0.5)) sky.geom(SHAPES.cyl, trs(p.x, top + 0.9, -p.y, 0.05, 1.8, 0.05), col("#E8E4F2"));
      }
    }
    const skyMesh = new THREE.Mesh(sky.build(), new THREE.MeshStandardMaterial({ vertexColors: true, roughness: 0.9, fog: false }));
    this.group.add(skyMesh);

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

  /** The train shuttles from downtown into the tunnel and back, pausing at each end. */
  update(t: number) {
    const v = 4, run = this.lineLen / v, pause = 3, P = 2 * (run + pause);
    const u = ((t % P) + P) % P;
    let s: number;
    let inbound = true;
    if (u < run) s = this.lineLen - u * v;
    else if (u < run + pause) s = -2;
    else if (u < 2 * run + pause) { s = (u - run - pause) * v; inbound = false; }
    else s = this.lineLen;
    const p = add(this.portal, mul(this.dir, Math.max(-2, s)));
    const y = s < 3.2 ? DECK_Y * Math.max(0, (s - 0.4) / 2.8) - (s < 0.4 ? 0.6 : 0) : DECK_Y;
    this.train.visible = s > -0.5 && s < this.lineLen - 2;
    this.train.position.set(p.x, y, -p.y);
    const head = inbound ? mul(this.dir, -1) : this.dir;
    this.train.rotation.y = Math.atan2(head.y, head.x);
  }
}
