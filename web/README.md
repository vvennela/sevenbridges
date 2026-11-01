# Seven Bridges: browser frontend

A three.js diorama and HUD for the Seven Bridges puzzle. All rules live in the
compiled Lean binary; this frontend only draws what Lean replies.

```
Browser (Vite + TypeScript + three.js)  --ws /ws-->  server/bridge.mjs  --stdin/stdout-->  .lake/build/bin/sevenbridges
```

## Run

Build the Lean binary first (`lake build` at the repo root), then:

```sh
cd web
npm install        # also installs server/ (postinstall)
npm run dev        # starts the bridge (port 8787) and Vite (http://localhost:5173)
```

- `npm run build`: type-check (`tsc`) and build to `web/dist/`.
- `npm run preview`: serve `dist/` (still needs the bridge: `npm run bridge`).
- `npm run screenshot`: with `npm run dev` running, build a few blocks, BUILD
  and Compare, and save `screenshot.png` / `screenshot-built.png` (Playwright).
  Arguments: `[url] [outPrefix] [width] [height] [full|edit]`.
- Bridge on its own: `cd server && npm start [port]`. Env: `SB_BIN` (binary
  path), `PORT`. Round-trip test: `cd server && npm test` while it runs.
- Point the page at another bridge with `?ws=ws://host:port`.

## How to play

1. Pick a building in the tray at the bottom (Homes, Offices, Shops, Park,
   Bar, or Clear). Open lots glow. Left-click a lot to build there; left-click
   again to add a floor; right-click to take a floor off (and clear at the
   lowest). Hover any block for a card with up/down buttons and its residents.
2. Click a colored route on the road (or its bus tile) to run that bus. Faint
   subway entrances show where a station could go; click one to build it.
3. Hearts and little clouds over homes show how residents feel (from Lean's
   report after every change). Money left is under the rating.
4. Press Build: Lean rates the town out of 100 (stars at 50, 80, 100) and a
   postcard says what residents love and wish for. 100 means no plan can do
   better (proven in Lean); the best layout itself is never shown. "Try for
   100" goes back to editing. The frontend never calls `solve`.
5. The dice button tries a new generated neighborhood (`?seed=N`). The plain
   URL always loads the demo, Old Harbor (via the `demo` command).

The surroundings are cosmetic: meadow by default, a river or coast on one
side for some seeds (`?setting=inland|river|coast` forces one). `?nocoach`
hides the first-play tips; `?test` exposes a small hook for the screenshot
script.

## Rule: the frontend never decides outcomes

Cost, validity, problems, score, happiness, productivity, crime, riders and
trips are read from Lean replies (`src/types.ts` mirrors `fixtures/*.json`).
The only arithmetic on them is for display: the budget bar width, the red
"over budget" color (cost > budget), and "your % of best".

Looks only, no rule depends on them: the quad grid in blocks, building
modules, colors, the street path a dot follows for a trip (shortest street
path in `src/transit.ts`), bus motion, and the distant city.

## Files

- `src/main.ts`: game flow and HUD (residents panel, rating ring, toy tray, hover card, postcard, coach marks).
- `src/world.ts`: scene, meadow and surroundings, plots, picking, feelings (hearts/clouds), camera.
- `src/buildings.ts`: building models per kind and floor count; tray thumbnail models (`src/thumbs.ts` renders them).
- `src/transit.ts`: route ribbons and stops, buses, subway entrances, walking cats (the residents).
- `src/palette.ts`, `src/icons.ts`: shared colors, names, plain-language factor sentences, SVG icons.
- `src/api.ts`, `src/types.ts`: bridge client and reply types. `src/geom.ts`, `src/builder.ts`, `src/rng.ts`: helpers.
- `../server/bridge.mjs`: the bridge; `../server/test-bridge.mjs`: round-trip test.
