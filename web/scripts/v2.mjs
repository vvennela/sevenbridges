// Version 2 walkthrough: title → rules → size → wait → level card → play → hover links → build.
// Usage: node scripts/v2.mjs [outPrefix] [width] [height] [extraQuery]
import { chromium } from "playwright";

const out = process.argv[2] ?? "/tmp/sb-shots/v2";
const W = Number(process.argv[3] ?? 1440), H = Number(process.argv[4] ?? 900);
const extra = process.argv[5] ?? "";
const size = process.argv[6] ?? "easy";
const base = `http://localhost:5173/?test&nocoach${extra ? "&" + extra : ""}`;
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: W, height: H }, deviceScaleFactor: 1 });
page.on("pageerror", (e) => console.log("[pageerror]", e.message, e.stack?.split("\n")[1]));
page.on("console", (m) => { if (m.type() === "error") console.log("[console]", m.text()); });
const shot = async (name) => { await page.screenshot({ path: `${out}-${name}.png` }); console.log("shot", name); };

await page.goto(base);
await page.waitForSelector(".title-card.on", { timeout: 60000 });
await page.waitForTimeout(2500);
await shot("title");
await page.click("[data-act='rules']");
await page.waitForTimeout(700);
await shot("rules");
await page.click(".title-card.on [data-act='start']");
await page.waitForTimeout(600);
await shot("size");
await page.click(`[data-pick='${size}']`);
await page.waitForTimeout(150);
await shot("wait");
await page.waitForSelector(".intro-card", { timeout: 120000 });
await page.waitForTimeout(1800);
await shot("level-card");
console.log("card:", (await page.locator(".intro-meta").count()) ? (await page.textContent(".intro-meta"))?.trim() : "(no meta)");
await page.click("[data-act='go']");
await page.waitForTimeout(500);

const blocks = async () => page.evaluate(() => window.__sb.blocks());
const bs = await blocks();
const tool = async (k) => page.locator(`[data-tool='${k}']`).click().catch(() => console.log("no tool", k));
const plan = ["housing", "office", "food", "housing", "park", "shop", "bar", "housing", "office"];
for (const [i, b] of bs.entries()) {
  if (!b.p) continue;
  const k = plan[i % plan.length];
  await tool(k);
  await page.mouse.click(b.p.x, b.p.y + 20);
  const ups = k === "office" ? (i === 1 ? 4 : 1) : k === "housing" && i === 0 ? 1 : 0;
  for (let u = 0; u < ups; u++) { await page.waitForTimeout(120); await page.mouse.click(b.p.x, b.p.y + 20); }
  await page.waitForTimeout(150);
}
await page.keyboard.press("Escape");
await page.mouse.move(W / 2, 30);
await page.waitForTimeout(2500);
await shot("play");
if (process.env.ROUTES) { await page.locator("[data-route='0']").click().catch(() => {}); await page.waitForTimeout(1500); }
const home = (await blocks()).find((b) => b.kind === "housing");
if (home) { await page.mouse.move(home.p.x, home.p.y + 20); await page.waitForTimeout(900); await shot("hover-home"); }
const off = (await blocks()).find((b) => b.kind === "office");
if (off) { await page.mouse.move(off.p.x, off.p.y + 20); await page.waitForTimeout(900); await shot("hover-office"); }
await page.evaluate(() => window.__sb.setAllBridges(true));
await page.waitForTimeout(400);
await page.locator("[data-route='0']").click().catch(() => {});
await page.locator("[data-route='1']").click().catch(() => {});
await page.mouse.move(W - 5, H / 2);
for (let k = 0; k < 40; k++) { await page.waitForTimeout(1000); const c = await page.evaluate(() => window.__sb.day()); if (c && c.phase === 1 && c.u > 0.2) break; }
console.log("clock:", JSON.stringify(await page.evaluate(() => window.__sb.day())));
await shot("midday");
await page.evaluate(() => window.__sb.zoom(0.6));
await page.waitForTimeout(1200);
await shot("midday-close");
await page.evaluate(() => window.__sb.recenter());
await page.waitForTimeout(1200);
await page.locator("[data-route='0']").click().catch(() => {});
await page.locator("[data-route='1']").click().catch(() => {});
await page.mouse.move(W / 2, 30);
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 120000 });
await page.waitForTimeout(3000);
await shot("built");
console.log("renderer:", JSON.stringify(await page.evaluate(() => window.__sb.info())));
await page.click("[data-act='close-pc']").catch(() => {});
await page.mouse.move(W - 5, H / 2);
const kinds = (await blocks()).map((b) => b.kind);
console.log("kinds:", kinds.join(","));
for (const k of ["food", "office", "housing"]) {
  const i = kinds.indexOf(k);
  if (i < 0) continue;
  await page.evaluate((i) => window.__sb.lookBlock(i, 9, 0.62), i);
  await page.waitForTimeout(1500);
  await shot(`close-${k}`);
}
await page.evaluate(() => window.__sb.far());
await page.waitForTimeout(1500);
await shot("far");
await browser.close();
