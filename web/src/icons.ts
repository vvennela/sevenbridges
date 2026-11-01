// Small hand-drawn SVG icons for the HUD (colors from palette.ts).
import { C } from "./palette";

const svg = (body: string, vb = "0 0 24 24") => `<svg viewBox="${vb}" aria-hidden="true">${body}</svg>`;

export const ICON = {
  heart: (color = C.coral) => svg(`<path d="M12 20.5C5 15.6 2.5 12.4 2.5 8.9 2.5 6.2 4.6 4 7.3 4c1.9 0 3.5 1 4.7 2.6C13.2 5 14.8 4 16.7 4c2.7 0 4.8 2.2 4.8 4.9 0 3.5-2.5 6.7-9.5 11.6z" fill="${color}"/><ellipse cx="8" cy="8.5" rx="1.8" ry="1.2" fill="#fff" opacity=".7" transform="rotate(-30 8 8.5)"/>`),
  coin: () => svg(`<circle cx="12" cy="12" r="9" fill="${C.sunflower}"/><circle cx="12" cy="12" r="6.6" fill="none" stroke="#E9A92A" stroke-width="1.4"/><path d="M12 8.2v7.6M14.1 9.6c-.5-.7-1.3-1-2.2-1-1.2 0-2.1.6-2.1 1.5 0 2 4.5 1.1 4.5 3.3 0 .9-1 1.6-2.3 1.6-1 0-1.9-.4-2.4-1.1" stroke="#B5781A" stroke-width="1.5" fill="none" stroke-linecap="round"/>`),
  star: (on: boolean) => svg(`<path d="M12 2.8l2.7 5.7 6.2.8-4.6 4.3 1.2 6.2L12 16.8 6.5 19.8l1.2-6.2L3.1 9.3l6.2-.8z" fill="${on ? C.sunflower : "#E4E1EE"}" stroke="${on ? "#E9A92A" : "#D2CEE0"}" stroke-width="1.2" stroke-linejoin="round"/>`),
  dice: () => svg(`<rect x="4" y="4" width="16" height="16" rx="4" fill="#fff" stroke="${C.ink}" stroke-width="1.6"/><circle cx="9" cy="9" r="1.5" fill="${C.ink}"/><circle cx="15" cy="15" r="1.5" fill="${C.ink}"/><circle cx="15" cy="9" r="1.5" fill="${C.ink}"/><circle cx="9" cy="15" r="1.5" fill="${C.ink}"/>`),
  clear: () => svg(`<path d="M5 15.5l8.5-8.5 5 5-6 6H8z" fill="#FFC3D3" stroke="${C.ink}" stroke-width="1.5" stroke-linejoin="round"/><path d="M13.5 7l5 5" stroke="${C.ink}" stroke-width="1.5"/><path d="M8 18.5h11" stroke="${C.ink}" stroke-width="1.5" stroke-linecap="round"/>`),
  up: () => svg(`<path d="M6 14l6-6 6 6" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"/>`),
  down: () => svg(`<path d="M6 10l6 6 6-6" fill="none" stroke="currentColor" stroke-width="2.6" stroke-linecap="round" stroke-linejoin="round"/>`),
  bus: (color: string) => svg(`<rect x="3" y="5" width="18" height="12" rx="3.5" fill="${color}"/><rect x="5" y="7.5" width="14" height="4.5" rx="1.4" fill="#fff" opacity=".9"/><rect x="3" y="13.5" width="18" height="1.4" fill="#fff" opacity=".55"/><circle cx="7.5" cy="18" r="2" fill="${C.ink}"/><circle cx="16.5" cy="18" r="2" fill="${C.ink}"/>`),
  subway: (color: string) => svg(`<circle cx="12" cy="11" r="8.5" fill="${color}"/><circle cx="12" cy="11" r="8.5" fill="none" stroke="#fff" stroke-width="1.6"/><path d="M7.8 15V7.2l4.2 5 4.2-5V15" fill="none" stroke="#fff" stroke-width="2" stroke-linejoin="round" stroke-linecap="round"/><rect x="11" y="19" width="2" height="4" fill="#8A93B8"/>`),
  no: () => svg(`<circle cx="12" cy="12" r="9" fill="#fff" stroke="#E2675A" stroke-width="2.4"/><path d="M6 6l12 12" stroke="#E2675A" stroke-width="2.4"/>`),
  wish: () => svg(`<circle cx="12" cy="12" r="9" fill="#EEF3FF"/><path d="M12 6.5l1.5 3.4 3.7.4-2.8 2.5.8 3.6L12 14.6l-3.2 1.8.8-3.6L6.8 10.3l3.7-.4z" fill="#9CCAF4"/>`),
  oops: () => svg(`<circle cx="12" cy="12" r="9" fill="#FFE9E5"/><path d="M12 7v6" stroke="#E2675A" stroke-width="2.4" stroke-linecap="round"/><circle cx="12" cy="16.6" r="1.4" fill="#E2675A"/>`),
  bridge: () => svg(`<path d="M2 15h20v3H2z" fill="#C9A27E"/><path d="M3 15c3-6 15-6 18 0" fill="none" stroke="#D9CDB8" stroke-width="3"/><path d="M2 20c3 1 5-1 7 0s5 1 7 0 4-1 6 0" stroke="#8FD3EA" stroke-width="1.8" fill="none"/>`),
  briefcase: () => svg(`<rect x="3.5" y="7.5" width="17" height="11.5" rx="2.5" fill="#C9A27E"/><path d="M9 7.5V6a1.5 1.5 0 0 1 1.5-1.5h3A1.5 1.5 0 0 1 15 6v1.5" fill="none" stroke="#8C6A4C" stroke-width="1.6"/><rect x="3.5" y="11.5" width="17" height="1.6" fill="#8C6A4C" opacity=".5"/>`),
  cloud: () => svg(`<path d="M7 17a4 4 0 0 1-.6-7.95A5 5 0 0 1 16 8.6 3.7 3.7 0 1 1 17.2 17z" fill="#A9B2C6"/>`),
  /** A round cat face in a group color (the residents are cats). */
  avatar: (color: string, fur = "#E8914A", kind: "tie" | "scarf" = "tie") => svg(`<path d="M4.2 9.5 5 2.8l5 3.6M19.8 9.5 19 2.8l-5 3.6" fill="${fur}" stroke="${fur}" stroke-width="1.2" stroke-linejoin="round"/><path d="M6.2 5.6l.4-1.6 1.6 1.2M17.8 5.6l-.4-1.6-1.6 1.2" fill="#FF9FB0"/><ellipse cx="12" cy="12.6" rx="9.2" ry="8" fill="${fur}"/><ellipse cx="12" cy="15.3" rx="4.4" ry="3.1" fill="#fff"/><circle cx="8.6" cy="11.8" r="1.25" fill="${fur === "#33343B" ? "#FFE19A" : C.ink}"/><circle cx="15.4" cy="11.8" r="1.25" fill="${fur === "#33343B" ? "#FFE19A" : C.ink}"/><path d="M11.1 14h1.8l-.9 1z" fill="#FF8FA3"/><path d="M5.2 25c1.3-3 3.8-4.2 6.8-4.2s5.5 1.2 6.8 4.2z" fill="#3A3F4B"/>${kind === "tie"
    ? `<path d="M10.2 20.9 12 23.3l1.8-2.4z" fill="#fff"/><path d="M11.3 21.4h1.4l.5 3.1-1.2 1-1.2-1z" fill="${color}"/>`
    : `<ellipse cx="12" cy="21.2" rx="4.6" ry="1.6" fill="${color}"/><path d="M13.6 21.6l1.6 3-1.8-.4z" fill="${color}"/>`}`, "0 0 24 26"),
};

/** Culture factor glyphs. */
export const FACTOR_ICON: Record<string, string> = {
  parks: svg(`<rect x="11" y="13" width="2" height="7" rx="1" fill="${C.trunk}"/><circle cx="12" cy="10" r="6" fill="${C.leaf}"/><circle cx="14" cy="8" r="2.6" fill="${C.leafLight}"/>`),
  nightlife: svg(`<path d="M5 5h14l-7 8z" fill="${C.lavender}" stroke="#8E74C9" stroke-width="1.3" stroke-linejoin="round"/><path d="M12 13v6M8.5 19.5h7" stroke="#8E74C9" stroke-width="1.6" stroke-linecap="round"/><circle cx="15.5" cy="4" r="1.6" fill="${C.coral}"/>`),
  quiet: svg(`<path d="M15.5 4.5a7.5 7.5 0 1 0 4 12.6A6.2 6.2 0 0 1 15.5 4.5z" fill="#B8C4F0"/><circle cx="7" cy="6" r="1" fill="#B8C4F0"/><circle cx="19" cy="5" r=".8" fill="#B8C4F0"/>`),
  shortCommute: svg(`<circle cx="12" cy="12" r="8.5" fill="#fff" stroke="${C.ink}" stroke-width="1.6"/><path d="M12 7.5V12l3 2" stroke="${C.coral}" stroke-width="1.9" stroke-linecap="round" fill="none"/>`),
  walkability: svg(`<ellipse cx="9" cy="8" rx="2.6" ry="4" fill="${C.mint}" stroke="#4FB08B" stroke-width="1.2"/><ellipse cx="15" cy="15" rx="2.6" ry="4" fill="${C.mint}" stroke="#4FB08B" stroke-width="1.2"/>`),
  transit: svg(`<rect x="4" y="4.5" width="16" height="12" rx="3.2" fill="${C.sky}"/><rect x="6" y="7" width="12" height="4.5" rx="1.2" fill="#fff"/><circle cx="8" cy="18" r="1.8" fill="${C.ink}"/><circle cx="16" cy="18" r="1.8" fill="${C.ink}"/>`),
  shops: svg(`<path d="M6 9h12l-1 11H7z" fill="${C.mint}" stroke="#4FB08B" stroke-width="1.2" stroke-linejoin="round"/><path d="M9 9V7.5a3 3 0 0 1 6 0V9" fill="none" stroke="#4FB08B" stroke-width="1.5"/>`),
};
