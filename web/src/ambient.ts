// A living world, cheaply: wind in the trees, cloud shadows sliding over the land,
// sparkling water, windows that glow at dusk, and a light that follows the time of day.
// Looks only. Everything here runs in shaders or on a handful of instanced meshes.
import * as THREE from "three";
import { col } from "./builder";
import { C } from "./palette";

/** Shared uniforms: one update per frame drives every material. */
export const U = {
  uTime: { value: 0 },
  /** 0 = day, 1 = dusk/night (windows and lamps glow). */
  uNight: { value: 0 },
  /** How strong the cloud shadows are (weaker at dusk). */
  uCloud: { value: 1 },
  /** Sunlight on the water sparkles. */
  uSun: { value: 1 },
  uWin1: { value: col(C.window).clone() },
  uWin2: { value: col("#5F86C8").clone() },
  /** Downtown's window color (lifted toward the haze). */
  uWin3: { value: new THREE.Color(0, 0, 0) },
  uWarm: { value: new THREE.Color(1.0, 0.72, 0.36) },
};

const NOISE = /* glsl */ `
float sbHash(vec2 p) { p = fract(p * vec2(123.34, 456.21)); p += dot(p, p + 45.32); return fract(p.x * p.y); }
float sbNoise(vec2 p) {
  vec2 i = floor(p), f = fract(p);
  vec2 u = f * f * (3.0 - 2.0 * f);
  return mix(mix(sbHash(i), sbHash(i + vec2(1, 0)), u.x), mix(sbHash(i + vec2(0, 1)), sbHash(i + vec2(1, 1)), u.x), u.y);
}
`;

interface Opts { wind?: boolean; clouds?: boolean; windows?: boolean; water?: boolean }

/** Add wind sway, cloud shadows, glowing windows and/or water sparkle to a standard material. */
export function alive<T extends THREE.MeshStandardMaterial>(mat: T, o: Opts): T {
  const key = `${o.wind ? "w" : ""}${o.clouds ? "c" : ""}${o.windows ? "n" : ""}${o.water ? "s" : ""}`;
  mat.customProgramCacheKey = () => `alive-${key}`;
  mat.onBeforeCompile = (sh) => {
    Object.assign(sh.uniforms, U);
    sh.vertexShader = sh.vertexShader
      .replace("#include <common>", `#include <common>
attribute float sway;
uniform float uTime;
varying vec3 vSbWorld;`)
      .replace("#include <begin_vertex>", `#include <begin_vertex>
${o.wind ? `{
  vec4 wp0 = modelMatrix * vec4(transformed, 1.0);
  // gusts roll across the land as a slow travelling wave
  float gust = 0.5 + 0.5 * sin(dot(wp0.xz, vec2(0.13, 0.09)) - uTime * 0.8);
  gust = 0.35 + gust * gust * gust;
  float ph = wp0.x * 0.9 + wp0.z * 0.6;
  float a = sway * 0.055 * gust;
  transformed.x += a * (sin(uTime * 1.7 + ph) + 0.35 * sin(uTime * 3.9 + ph * 1.7));
  transformed.z += a * 0.6 * cos(uTime * 1.3 + ph);
}` : ""}`)
      .replace("#include <worldpos_vertex>", `#include <worldpos_vertex>
vSbWorld = (modelMatrix * vec4(transformed, 1.0)).xyz;`);
    sh.fragmentShader = sh.fragmentShader
      .replace("#include <common>", `#include <common>
uniform float uTime; uniform float uNight; uniform float uCloud; uniform float uSun;
uniform vec3 uWin1; uniform vec3 uWin2; uniform vec3 uWin3; uniform vec3 uWarm;
varying vec3 vSbWorld;
${NOISE}`)
      .replace("#include <color_fragment>", `#include <color_fragment>
${o.water ? `{
  // water: drifting ripples and sun sparkles on the blue parts only
  float blue = smoothstep(0.05, 0.2, diffuseColor.b - diffuseColor.r);
  vec2 q = vSbWorld.xz;
  float r1 = sbNoise(q * 2.2 + vec2(uTime * 0.35, uTime * 0.21));
  float r2 = sbNoise(q * 3.1 - vec2(uTime * 0.27, uTime * 0.38));
  float ripple = smoothstep(0.55, 0.85, r1 * 0.6 + r2 * 0.6);
  float spark = smoothstep(0.86, 0.95, r1 * r2 * 1.6);
  diffuseColor.rgb += blue * (ripple * 0.08 + spark * 0.6 * uSun);
}` : ""}`)
      .replace("#include <emissivemap_fragment>", `#include <emissivemap_fragment>
${o.windows ? `#ifdef USE_COLOR
{
  // windows light up at dusk
  float d = min(min(distance(vColor.rgb, uWin1), distance(vColor.rgb, uWin2)), distance(vColor.rgb, uWin3));
  totalEmissiveRadiance += (1.0 - smoothstep(0.015, 0.05, d)) * uNight * uWarm;
}
#endif` : ""}`)
      .replace("#include <lights_fragment_end>", `#include <lights_fragment_end>
${o.clouds ? `{
  // soft cloud shadows sliding over the land: they only dim the sunlight
  vec2 q = vSbWorld.xz * 0.035 + vec2(uTime * 0.018, uTime * 0.009);
  float n = sbNoise(q) * 0.65 + sbNoise(q * 2.3 + 7.1) * 0.35;
  float shade = smoothstep(0.5, 0.72, n) * 0.42 * uCloud;
  reflectedLight.directDiffuse *= 1.0 - shade;
  reflectedLight.directSpecular *= 1.0 - shade;
}` : ""}`);
  };
  return mat;
}

/** Time of day → light. `d` runs 0..4 over the simulated day (morning, lunch, evening, night). */
export interface Light { sun: THREE.Color; sunI: number; hemiSky: THREE.Color; hemiGround: THREE.Color; hemiI: number; exposure: number; fog: THREE.Color; night: number; elev: number; az: number }
const K: [number, Light][] = [
  [0.0, { sun: new THREE.Color("#FFE9CF"), sunI: 2.3, hemiSky: new THREE.Color("#DCEBFF"), hemiGround: new THREE.Color("#BFE0A0"), hemiI: 1.2, exposure: 1.08, fog: new THREE.Color(C.skyHaze), night: 0, elev: 0.55, az: -1.1 }],
  [1.5, { sun: new THREE.Color("#FFE4BD"), sunI: 2.6, hemiSky: new THREE.Color("#D6ECFF"), hemiGround: new THREE.Color("#BFE0A0"), hemiI: 1.25, exposure: 1.12, fog: new THREE.Color(C.skyHaze), night: 0, elev: 0.95, az: -0.2 }],
  [2.55, { sun: new THREE.Color("#FFC27E"), sunI: 2.5, hemiSky: new THREE.Color("#FFE3C8"), hemiGround: new THREE.Color("#C9D99A"), hemiI: 1.1, exposure: 1.08, fog: new THREE.Color("#F6E6D6"), night: 0.1, elev: 0.42, az: 0.9 }],
  [3.3, { sun: new THREE.Color("#F0B9C8"), sunI: 1.5, hemiSky: new THREE.Color("#CFC8F2"), hemiGround: new THREE.Color("#BCC9A6"), hemiI: 1.15, exposure: 1.04, fog: new THREE.Color("#E6DCEE"), night: 1, elev: 0.35, az: 1.4 }],
  [3.85, { sun: new THREE.Color("#E9D4F0"), sunI: 1.6, hemiSky: new THREE.Color("#D4D4F2"), hemiGround: new THREE.Color("#BFCDAA"), hemiI: 1.15, exposure: 1.05, fog: new THREE.Color("#E4E2F0"), night: 0.8, elev: 0.4, az: -1.5 }],
  [4.0, { sun: new THREE.Color("#FFE9CF"), sunI: 2.3, hemiSky: new THREE.Color("#DCEBFF"), hemiGround: new THREE.Color("#BFE0A0"), hemiI: 1.2, exposure: 1.08, fog: new THREE.Color(C.skyHaze), night: 0, elev: 0.55, az: -1.1 }],
];

export function lightAt(d: number): Light {
  d = ((d % 4) + 4) % 4;
  let i = 0;
  while (i < K.length - 2 && d > K[i + 1][0]) i++;
  const [d0, a] = K[i], [d1, b] = K[i + 1];
  const u = Math.min(1, Math.max(0, (d - d0) / (d1 - d0)));
  const s = u * u * (3 - 2 * u);
  const m = (x: number, y: number) => x + (y - x) * s;
  return {
    sun: a.sun.clone().lerp(b.sun, s), sunI: m(a.sunI, b.sunI), hemiSky: a.hemiSky.clone().lerp(b.hemiSky, s), hemiGround: a.hemiGround.clone().lerp(b.hemiGround, s),
    hemiI: m(a.hemiI, b.hemiI), exposure: m(a.exposure, b.exposure), fog: a.fog.clone().lerp(b.fog, s), night: m(a.night, b.night), elev: m(a.elev, b.elev), az: m(a.az, b.az),
  };
}
