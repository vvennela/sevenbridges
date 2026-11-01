// r17: busy spots (no overlaps) and a forced crime sequence (?crime).
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/r17";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?nocoach&test&crime`);
await page.waitForSelector("#loading.gone", { timeout: 90000 });
await page.waitForTimeout(6000);
const blocks = () => page.evaluate(() => window.__sb.blocks());
const open = (await blocks()).filter((b) => !b.fixed && b.p);
const place = async (tool, b, times = 1) => { await page.locator(`[data-tool='${tool}']`).click(); for (let k = 0; k < times; k++) await page.mouse.click(b.p.x, b.p.y + 20); await page.waitForTimeout(150); };
await place("housing", open[0], 2);
await place("shop", open[1]);
await place("housing", open[2], 3);
if (open[3]) await place("park", open[3]);
await page.locator("[data-route='0']").click().catch(() => {});
await page.mouse.move(700, 30);
await page.waitForTimeout(500);
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.click("[data-act='close-pc']");
await page.mouse.move(1435, 450);
const bs = await blocks();
// busy spots
for (const b of bs.slice(0, 7)) {
  await page.evaluate((i) => { window.__sb.focus(i); window.__sb.low(0.95, 0.75); }, b.i);
  await page.waitForTimeout(1200);
  await page.screenshot({ path: `${out}-busy-${b.i}-${b.kind}.png` });
}
if (process.env.BUSYONLY) { await browser.close(); process.exit(0); }
// follow crime scene 0 for two incidents (?crime forces a knockout every other incident)
const seen = new Set();
for (let k = 1; k <= 70; k++) {
  const c = await page.evaluate(() => window.__sb.crimeLook(0, 4.6, 1.3));
  if (c && c.u <= 14) {
    const tag = `${c.ko ? "ko" : "chase"}-${String(Math.round(c.u)).padStart(2, "0")}`;
    if (!seen.has(tag)) { seen.add(tag); await page.waitForTimeout(80); await page.screenshot({ path: `${out}-${tag}.png` }); }
  }
  await page.waitForTimeout(500);
}
console.log([...seen].sort().join(" "));
await browser.close();
