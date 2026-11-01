// r20: river and bridges, lens links, personalities (?mock until Lean sends them).
import { chromium } from "playwright";
const out = process.argv[2] ?? "/tmp/sb-shots/r20";
const extra = process.argv[3] ?? "&mock";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?nocoach&test${extra}`);
await page.waitForSelector("#loading.gone", { timeout: 120000 });
await page.waitForTimeout(6000);
await page.screenshot({ path: `${out}-start.png` });
const blocks = () => page.evaluate(() => window.__sb.blocks());
const open = (await blocks()).filter((b) => !b.fixed && b.p);
const place = async (tool, b, times = 1) => { await page.locator(`[data-tool='${tool}']`).click(); for (let k = 0; k < times; k++) await page.mouse.click(b.p.x, b.p.y + 20); await page.waitForTimeout(200); };
await place("housing", open[0], 2);
await place("park", open[1]);
await place("housing", open[2], 2);
if (open[3]) await place("shop", open[3]);
await page.keyboard.press("Escape");
const sites = await page.evaluate(() => window.__sb.bridgeSites());
console.log("bridge sites:", JSON.stringify(sites));
if (sites[0]?.p) {
  await page.mouse.move(sites[0].p.x, sites[0].p.y); await page.waitForTimeout(700);
  await page.screenshot({ path: `${out}-bridge-hover.png` });
  await page.mouse.click(sites[0].p.x, sites[0].p.y); await page.waitForTimeout(1200);
}
await page.mouse.move(700, 30);
await page.screenshot({ path: `${out}-edit.png` });
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.click("[data-act='close-pc']");
await page.click("[data-lens='mood']");
await page.waitForTimeout(1200);
const home = (await blocks()).find((b) => b.kind === "housing");
if (home) { await page.mouse.move(home.p.x, home.p.y + 20); await page.waitForTimeout(800); }
await page.screenshot({ path: `${out}-mood.png` });
await page.click("[data-lens='none']");
await page.evaluate((i) => window.__sb.lookBlock(i, 4.5, 0.7), home.i);
await page.waitForTimeout(2000);
await page.screenshot({ path: `${out}-close.png` });
await browser.close();
