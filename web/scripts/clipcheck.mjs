// Hunt for cats clipping into the ground: low-angle frames at the edges of blocks (curb crossings),
// a home block, and the bar with forced scuffles. Usage: node scripts/clipcheck.mjs [extraQuery] [outPrefix]
import { chromium } from "playwright";
const extra = process.argv[2] ?? "";
const out = process.argv[3] ?? "/tmp/sb-shots/r16b";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?nocoach&test${extra}`);
await page.waitForSelector("#loading.gone", { timeout: 90000 });
await page.waitForTimeout(6000);
const blocks = () => page.evaluate(() => window.__sb.blocks());
const open = (await blocks()).filter((b) => !b.fixed && b.p);
const place = async (tool, b, times = 1) => { await page.locator(`[data-tool='${tool}']`).click(); for (let k = 0; k < times; k++) await page.mouse.click(b.p.x, b.p.y + 20); await page.waitForTimeout(150); };
await place("housing", open[0], 2);
await place("bar", open[1]);
await place("housing", open[2], 3);
if (open[3]) await place("park", open[3]);
await page.locator("[data-route='0']").click().catch(() => {});
await page.mouse.move(700, 30);
await page.waitForTimeout(500);
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.click("[data-act='close-pc']");
await page.mouse.move(1435, 450);
const shoot = async (name, i, elev, d, frames, gap, edge = false) => {
  await page.evaluate(([i, e, d, edge]) => { if (edge) { window.__sb.demoWalk(i); window.__sb.edge(i, d, e); } else { window.__sb.focus(i); window.__sb.low(e, d); } }, [i, elev, d, edge]);
  await page.waitForTimeout(1500);
  for (let k = 1; k <= frames; k++) { await page.screenshot({ path: `${out}-${name}-${k}.png` }); await page.waitForTimeout(gap); }
};
const bs = await blocks();
const home = bs.find((b) => b.kind === "housing");
const bar = bs.find((b) => b.kind === "bar");
if (!process.env.BARONLY && !process.env.PROPS) for (const b of bs.filter((x) => x.kind === "housing").slice(0, 3)) await shoot(`curb${b.i}`, b.i, 0.2, 4.2, 4, 700, true);
if (!process.env.PROPS) await page.evaluate((i) => window.__sb.focus(i), bar.i);
await page.waitForTimeout(1500);
if (!process.env.PROPS) for (let k = 1; k <= 8; k++) { await page.screenshot({ path: `${out}-bar-${k}.png` }); await page.waitForTimeout(900); }
// bar close-up: beers and a smoker
for (const kind of ["beer", "cig"]) {
  await page.evaluate((kind) => window.__sb.propLook(kind, 2.6, 0.95), kind);
  await page.waitForTimeout(1500);
  for (let k = 1; k <= 3; k++) { await page.screenshot({ path: `${out}-${kind}-${k}.png` }); await page.waitForTimeout(1200); }
}
console.log("cig:", JSON.stringify(await page.evaluate(() => window.__sb.cigAt())));
console.log("counts:", JSON.stringify(await page.evaluate(() => window.__sb.counts())));
console.log("rating:", await page.textContent(".ring-num"));
await browser.close();
