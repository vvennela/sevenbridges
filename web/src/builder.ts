// A small mesh builder: flat-shaded triangles with per-vertex colors.
// Faces take a "normal hint" so they always face the right way.
import * as THREE from "three";
import type { V2 } from "./geom";

export type P3 = [number, number, number];

/** Plan point at height h, as a world point. */
export const w3 = (p: V2, h: number): P3 => [p.x, h, -p.y];

const sub3 = (a: P3, b: P3): P3 => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const cross = (a: P3, b: P3): P3 => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const dot3 = (a: P3, b: P3) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const normalize = (a: P3): P3 => { const l = Math.hypot(a[0], a[1], a[2]) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };

const colorCache = new Map<string, THREE.Color>();
export function col(hex: string): THREE.Color {
  let c = colorCache.get(hex);
  if (!c) { c = new THREE.Color(hex); colorCache.set(hex, c); }
  return c;
}

export class GB {
  pos: number[] = [];
  nor: number[] = [];
  colr: number[] = [];
  /** Wind: while `sway` > 0, vertices get a sway weight that grows with height above `swayBase`. */
  sway = 0;
  swayBase = 0;
  private sw: number[] = [];

  get empty() { return this.pos.length === 0; }

  private put(p: P3, n: P3, c: THREE.Color) {
    this.sw.push(this.sway > 0 ? this.sway * Math.max(0, p[1] - this.swayBase) : 0);
    this.pos.push(p[0], p[1], p[2]);
    this.nor.push(n[0], n[1], n[2]);
    this.colr.push(c.r, c.g, c.b);
  }

  tri(a: P3, b: P3, c: P3, color: THREE.Color, hint?: P3) {
    let n = cross(sub3(b, a), sub3(c, a));
    if (hint && dot3(n, hint) < 0) { [b, c] = [c, b]; n = [-n[0], -n[1], -n[2]]; }
    n = normalize(n);
    this.put(a, n, color); this.put(b, n, color); this.put(c, n, color);
  }

  /** A flat polygon (convex or nearly), fanned from its first point. */
  poly(pts: P3[], color: THREE.Color, hint?: P3) {
    let nw: P3 = [0, 0, 0];
    for (let i = 0; i < pts.length; i++) {
      const a = pts[i], b = pts[(i + 1) % pts.length];
      nw = [nw[0] + (a[1] - b[1]) * (a[2] + b[2]), nw[1] + (a[2] - b[2]) * (a[0] + b[0]), nw[2] + (a[0] - b[0]) * (a[1] + b[1])];
    }
    let order = pts;
    if (hint && dot3(nw, hint) < 0) { order = [...pts].reverse(); nw = [-nw[0], -nw[1], -nw[2]]; }
    const n = normalize(nw);
    for (let i = 1; i < order.length - 1; i++) { this.put(order[0], n, color); this.put(order[i], n, color); this.put(order[i + 1], n, color); }
  }

  quad(a: P3, b: P3, c: P3, d: P3, color: THREE.Color, hint?: P3) { this.poly([a, b, c, d], color, hint); }

  /** Walls (and a top) of a CCW plan footprint between heights y0 and y1. */
  prism(foot: V2[], y0: number, y1: number, color: THREE.Color, topColor: THREE.Color | null = color) {
    for (let i = 0; i < foot.length; i++) {
      const a = foot[i], b = foot[(i + 1) % foot.length];
      const out: P3 = [b.y - a.y, 0, b.x - a.x]; // plan right-normal (dy,-dx) in world coords
      this.quad(w3(a, y0), w3(b, y0), w3(b, y1), w3(a, y1), color, out);
    }
    if (topColor) this.poly(foot.map((p) => w3(p, y1)), topColor, [0, 1, 0]);
  }

  /** Append a three.js geometry, transformed by m, in one color. */
  geom(g: THREE.BufferGeometry, m: THREE.Matrix4, color: THREE.Color) {
    const src = g.index ? g.toNonIndexed() : g;
    const p = src.getAttribute("position");
    const v = new THREE.Vector3();
    const tmp: P3[] = [];
    for (let i = 0; i < p.count; i++) {
      v.fromBufferAttribute(p, i).applyMatrix4(m);
      tmp.push([v.x, v.y, v.z]);
      if (tmp.length === 3) {
        const n = normalize(cross(sub3(tmp[1], tmp[0]), sub3(tmp[2], tmp[0])));
        for (const q of tmp) this.put(q, n, color);
        tmp.length = 0;
      }
    }
  }

  build(offset?: P3): THREE.BufferGeometry {
    const g = new THREE.BufferGeometry();
    g.setAttribute("position", new THREE.Float32BufferAttribute(this.pos, 3));
    g.setAttribute("normal", new THREE.Float32BufferAttribute(this.nor, 3));
    g.setAttribute("color", new THREE.Float32BufferAttribute(this.colr, 3));
    g.setAttribute("sway", new THREE.Float32BufferAttribute(this.sw, 1));
    if (offset) g.translate(-offset[0], -offset[1], -offset[2]);
    g.computeBoundingSphere();
    return g;
  }
}

/** Shared unit shapes, already non-indexed. */
export const SHAPES = {
  ball: new THREE.IcosahedronGeometry(1, 1).toNonIndexed(),
  ballLo: new THREE.IcosahedronGeometry(1, 0).toNonIndexed(),
  /** A round bulb (string lights): enough segments to look round up close. */
  bulb: new THREE.SphereGeometry(1, 14, 10).toNonIndexed(),
  cyl: new THREE.CylinderGeometry(1, 1, 1, 7).toNonIndexed(),
  box: new THREE.BoxGeometry(1, 1, 1).toNonIndexed(),
  cone: new THREE.ConeGeometry(1, 1, 7).toNonIndexed(),
};

const _m = new THREE.Matrix4();
const _q = new THREE.Quaternion();
const _e = new THREE.Euler();
export function trs(x: number, y: number, z: number, sx: number, sy: number, sz: number, rotY = 0): THREE.Matrix4 {
  _e.set(0, rotY, 0);
  _q.setFromEuler(_e);
  return _m.compose(new THREE.Vector3(x, y, z), _q, new THREE.Vector3(sx, sy, sz));
}
