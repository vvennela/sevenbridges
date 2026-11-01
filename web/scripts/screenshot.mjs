// Plays the running app (npm run dev) with real clicks and saves screenshots.
// Usage: node scripts/screenshot.mjs [url] [outPrefix] [width] [height] [full|edit]
import { chromium } from "playwright";

const base = process.argv[2] ?? "http://localhost:5173/";
const out = process.argv[3] ?? "/tmp/sb-shots/shot";
const W = Number(process.argv[4] ?? 1440), H = Number(process.argv[5] ?? 900);
const flow = process.argv[6] ?? "full";
const url = base + (base.includes("?") ? "&" : "?") + "test";

const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: W, height: H }, deviceScaleFactor: 1 });
page.on("pageerror", (e) => console.log("[pageerror]", e.message));
page.on("console", (m) => { if (m.type() === "error") console.log("[console]", m.text()); });
await page.goto(url);
await page.waitForFunction(() => document.querySelector("#tools .tile") !== null && document.querySelector("#loading.gone"), null, { timeout: 120000 });
await page.waitForTimeout(2500);
const blocks = async () => page.evaluate(() => window.__sb.blocks());
const open = (await blocks()).filter((b) => !b.fixed && b.p);
await page.screenshot({ path: `${out}-start.png` });

// pick Homes and build on a few open blocks; raise one; lower another
await page.locator("[data-tool='housing']").click();
for (const b of open.slice(0, 3)) await page.mouse.click(b.p.x, b.p.y + 20);
if (open[1]) await page.mouse.click(open[1].p.x, open[1].p.y + 20);
if (open[3]) { await page.locator("[data-tool='park']").click(); await page.mouse.click(open[3].p.x, open[3].p.y + 20); }
if (open[4]) { await page.locator("[data-tool='shop']").click().catch(() => {}); await page.mouse.click(open[4].p.x, open[4].p.y + 20); }
await page.locator("[data-tool='housing']").click();
await page.mouse.move(W / 2, 40);
await page.waitForTimeout(1800);
console.log("money:", (await page.textContent(".bar-row.over, .bar-row:nth-child(2)"))?.replace(/\s+/g, " ").trim());
await page.screenshot({ path: `${out}-edit.png` });

// hover a built block
const hb = (await blocks()).find((b) => b.kind === "housing");
if (hb) { await page.mouse.move(hb.p.x, hb.p.y + 20); await page.waitForTimeout(700); await page.screenshot({ path: `${out}-hover.png` }); }
const site = (await page.evaluate(() => window.__sb.sites())).find((s) => s.p);
if (site) { await page.mouse.move(site.p.x, site.p.y + 18); await page.waitForTimeout(700); await page.screenshot({ path: `${out}-site.png` }); }
if (flow === "edit") { await browser.close(); process.exit(0); }

await page.mouse.move(W / 2, 40);
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.waitForTimeout(3000);
console.log("rating:", await page.textContent(".ring-num"), "|", await page.textContent(".pc-head"));
await page.screenshot({ path: `${out}-built.png` });
console.log("renderer:", JSON.stringify(await page.evaluate(() => window.__sb.info())));

await page.click("[data-act='close-pc']");
await page.waitForTimeout(500);
// close-up of a home block with its cats
const homes = (await blocks()).filter((b) => b.kind === "housing");
await page.evaluate((i) => window.__sb.focus(i), (homes[1] ?? homes[0])?.i ?? 0);
await page.mouse.move(W - 5, H / 2);
await page.waitForTimeout(2500);
await page.screenshot({ path: `${out}-close.png` });
// lenses, back at the default view
await page.reload();
await page.waitForSelector("#loading.gone", { timeout: 60000 });
await page.waitForTimeout(1500);
for (const b of open.slice(0, 3)) { await page.locator("[data-tool='housing']").click(); await page.mouse.click(b.p.x, b.p.y + 20); }
if (open[3]) { await page.locator("[data-tool='park']").click(); await page.mouse.click(open[3].p.x, open[3].p.y + 20); }
await page.locator("[data-route='0']").click().catch(() => {});
await page.click("#build");
await page.waitForSelector(".pc-head", { timeout: 60000 });
await page.click("[data-act='close-pc']");
for (const l of ["mood", "jobs", "transit"]) {
  await page.click(`[data-lens='${l}']`);
  await page.waitForTimeout(1200);
  const tgt = (await blocks()).find((b) => (l === "mood" ? b.kind === "housing" : l === "jobs" ? b.kind === "office" : b.kind === "housing"));
  if (tgt && l !== "transit") { await page.mouse.move(tgt.p.x, tgt.p.y + 20); await page.waitForTimeout(700); }
  await page.screenshot({ path: `${out}-lens-${l}.png` });
  await page.mouse.move(W / 2, 30);
}
await page.click("[data-lens='none']");
await page.locator("[data-tool='bar']").hover().catch(() => {});
await page.waitForTimeout(500);
await page.screenshot({ path: `${out}-trayinfo.png` });
await browser.close();
