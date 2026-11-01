// Close-ups for checking cats: a bar block (beers, smokers, scuffles) and a low-angle ground check.
// Usage: node scripts/closeups.mjs [extraQuery] [outPrefix]
import { chromium } from "playwright";
const extra = process.argv[2] ?? "";
const out = process.argv[3] ?? "/tmp/sb-shots/r16";
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1440, height: 900 } });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
await page.goto(`http://localhost:5173/?nocoach&test${extra}`);
await page.waitForSelector("#loading.gone", { timeout: 90000 });
await page.waitForTimeout(2500);
const blocks = () => page.evaluate(() => window.__sb.blocks());
const open = (await blocks()).filter((b) => !b.fixed && b.p);
const place = async (tool, b, times = 1) => { await page.locator(`[data-tool='${tool}']`).click(); for (let k = 0; k < times; k++) await page.mouse.click(b.p.x, b.p.y + 20); };
await place("housing", open[0], 2);
await place("bar", open[1]);
await place("housing", open[2], 3);
if (open[3]) await place("park", open[3]);
await page.mouse.move(700, 30);
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.click("[data-act='close-pc']");
const bar = (await blocks()).find((b) => b.kind === "bar");
await page.evaluate((i) => { window.__sb.focus(i); window.__sb.low(0.75, 0.75); }, bar.i);
await page.mouse.move(1435, 450);
for (const [k, wait] of [[1, 2500], [2, 2600], [3, 2600]]) { await page.waitForTimeout(wait); await page.screenshot({ path: `${out}-bar-${k}.png` }); }
const park = (await blocks()).find((b) => b.kind === "park") ?? (await blocks()).find((b) => b.kind === "housing");
await page.evaluate((i) => { window.__sb.focus(i); window.__sb.low(0.3, 0.85); }, park.i);
await page.waitForTimeout(2500);
await page.screenshot({ path: `${out}-ground.png` });
console.log("rating:", await page.textContent(".ring-num"));
await browser.close();
