// End-to-end randomness check, the way a player plays: open the game, press
// Start, pick a size, note the town; reload and do it again. Every run must
// give a different town (town number, simulation number, groups).
// Usage: node scripts/randomness-e2e.mjs [runs] [url]
import { chromium } from "playwright";

const runs = Number(process.argv[2] ?? 10);
const url = process.argv[3] ?? "http://localhost:5173/";
const sizes = ["easy", "medium", "hard"];
const browser = await chromium.launch({ args: ["--use-angle=metal", "--enable-gpu", "--ignore-gpu-blocklist"] });
const page = await browser.newPage({ viewport: { width: 1280, height: 800 } });
await page.addInitScript(() => localStorage.setItem("sb-tutorial-done", "1")); // straight to the size picker

const seen = [];
for (let i = 0; i < runs; i++) {
  const size = sizes[i % 3];
  await page.goto(url);                                   // a fresh visit / reload each time
  await page.waitForSelector(".title-card.on", { timeout: 60000 });
  await page.click(".title-card.on [data-act='start']");
  await page.click(`[data-pick='${size}']`);
  await page.waitForSelector(".intro-card", { timeout: 180000 });
  const meta = (await page.textContent(".intro-meta"))?.trim() ?? "";
  const groups = await page.$$eval("#hud .group-name, .grp-name, .groups .name", (els) => els.map((e) => e.childNodes[0]?.textContent?.trim() ?? ""));
  const town = meta.match(/Town #(\d+)/)?.[1], sim = meta.match(/simulation #(\d+)/)?.[1];
  const addr = page.url();
  seen.push({ size, town, sim, groups: groups.join(", "), addr });
  console.log(`${i + 1}. ${size.padEnd(6)} Town #${town}  sim #${sim}  ${groups.join(", ") || "(groups not read)"}  url=${new URL(addr).search || "(clean)"}`);
}
await browser.close();
const towns = new Set(seen.map((s) => s.town)), sims = new Set(seen.map((s) => s.sim));
console.log(`\ndistinct towns: ${towns.size}/${seen.length}, distinct simulations: ${sims.size}/${seen.length}`);
console.log(`addresses left clean after starting: ${seen.filter((s) => !new URL(s.addr).search.includes("seed")).length}/${seen.length}`);
process.exit(towns.size === seen.length && sims.size === seen.length ? 0 : 1);
