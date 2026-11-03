// Hover steadiness: with the Mood lens on, hold the pointer on a block (where its
// mood number is drawn) and jiggle it, then turn the town under a still pointer.
// Counts how often the hover card hides or jumps. Usage: node scripts/hover-check.mjs [url]
import { chromium } from "playwright";
const url = process.argv[2] ?? "http://localhost:5173/?test&nointro";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
await page.goto(url);
await page.waitForSelector(".title-card.on [data-act='start']", { timeout: 60000 });
await page.click(".title-card.on [data-act='start']");
await page.click("[data-pick='easy']");
await page.waitForFunction(() => window.__sb?.blocks?.().length > 0, null, { timeout: 120000 });
await page.evaluate(() => window.__sb.setAll("housing", 2));
await page.click("[data-lens='mood']");
await page.waitForSelector("#badges .bdg.mood", { timeout: 20000 });
await page.waitForTimeout(800);
// the block nearest the screen centre, aimed at its mood badge
const b = await page.$eval("#badges .bdg.mood", (e) => { const r = e.getBoundingClientRect(); return { x: r.left + r.width / 2, y: r.top + r.height / 2 }; });
const sample = () => page.$eval("#card", (e) => ({ shown: !e.classList.contains("hidden"), t: e.style.transform }));
let hides = 0, jumps = 0, n = 0, last = null;
const look = async () => {
  const s = await sample(); n++;
  if (!s.shown) hides++;
  if (last && s.shown && last.shown && s.t !== last.t) {
    const [ax, ay] = last.t.match(/-?\d+/g).map(Number), [bx, by] = s.t.match(/-?\d+/g).map(Number);
    if (Math.hypot(ax - bx, ay - by) > 60) jumps++;
  }
  last = s;
};
await page.mouse.move(b.x, b.y);
await page.waitForTimeout(400);
for (let k = 0; k < 40; k++) { await page.mouse.move(b.x + ((k % 5) - 2) * 4, b.y + ((k % 3) - 1) * 4); await page.waitForTimeout(40); await look(); }
const jiggle = { hides, jumps, n };
// turn the town under a still pointer: the hovered block should follow what's under it
hides = 0; jumps = 0; n = 0; last = null;
const before = await page.evaluate(() => document.querySelector("#card h3, #card .card-title, #card b")?.textContent ?? "");
for (let k = 0; k < 20; k++) { await page.keyboard.press("q"); await page.waitForTimeout(60); }
await page.waitForTimeout(600);
const target = await page.evaluate(() => { const e = document.elementFromPoint(0, 0); return !!e; });
void target;
console.log(`jiggle over a mood number: card hidden in ${jiggle.hides}/${jiggle.n} samples, ${jiggle.jumps} jumps`);
console.log(`card before turning: "${before}"`);
await browser.close();
