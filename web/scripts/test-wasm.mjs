// End-to-end test of the static build with the in-browser (WebAssembly) engine.
//   npx vite build && npx vite preview &   then   node scripts/test-wasm.mjs [url]
// For each size: title -> Start -> size -> town opens -> place buildings -> Build
// -> rating shown -> View solution -> Next town opens.
import { chromium } from "playwright";

const URL0 = process.argv[2] ?? "http://localhost:4173/sevenbridges/?test";
const browser = await chromium.launch({ args: ["--use-gl=swiftshader", "--enable-unsafe-swiftshader"] });
let fails = 0;
for (const size of ["easy", "medium", "hard"]) {
  const page = await browser.newPage();
  const errors = [];
  page.on("pageerror", (e) => errors.push(String(e)));
  await page.goto(URL0);
  await page.click('[data-act="start"] >> visible=true');
  const t0 = Date.now();
  await page.click(`[data-pick="${size}"]`);
  await page.waitForSelector('[data-act="go"]', { timeout: 180000 });
  const startMs = Date.now() - t0;
  await page.click('[data-act="go"]');
  await page.evaluate(() => window.__sb.placeRandom(7));
  await page.waitForTimeout(500);
  const t1 = Date.now();
  await page.click("#build");
  await page.waitForFunction(() => window.__sb.facts().built?.rating, null, { timeout: 120000 });
  const buildMs = Date.now() - t1;
  const rating = await page.evaluate(() => window.__sb.facts().built.rating);
  await page.click('[data-act="reveal"] >> visible=true');
  await page.click('[data-act="reveal-yes"]');
  await page.waitForFunction(() => document.body.innerText.includes("Next town"), null, { timeout: 120000 });
  const seed1 = await page.evaluate(() => window.__sb.facts().level?.seed);
  const t2 = Date.now();
  await page.click("#build");   // "Next town" once the plan was shown
  await page.waitForFunction((s) => window.__sb.facts().level?.seed !== s && document.querySelector('[data-act="go"]'), seed1, { timeout: 180000 });
  const nextMs = Date.now() - t2;
  const ok = rating && typeof rating.rating === "number" && errors.length === 0;
  if (!ok) fails++;
  console.log(`${size}: start ${startMs} ms, build->rating ${buildMs} ms (rating ${rating?.rating}/100), next town ${nextMs} ms, errors ${errors.length} ${errors.slice(0, 2).join(" | ")}`);
  await page.close();
}
await browser.close();
process.exit(fails ? 1 : 0);
