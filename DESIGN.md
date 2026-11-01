# Seven Bridges: Design

Seven Bridges is a small neighborhood-planning puzzle. Each puzzle is a
neighborhood of 5–8 blocks. The player chooses what to build on each block,
which bus routes to run, and whether to build a metro station. Lean simulates
the cats' day, computes the score, and proves that the game's "best possible
layout" really is the best.

Items marked **[ASSUMED]** are placeholders. Change them freely.

---

## 1. Goals

1. **Lean owns the rules.** Every outcome (cost, happiness, crime, score) is
   computed by Lean code. The frontend only draws it.
2. **The benchmark is proven optimal for every puzzle.** One theorem, proven
   once, covers every puzzle the game can generate (see §8).
3. **Fast to prove, hard to solve.** The solver proves each puzzle in under a
   second. The best layout should still be hard for a player to find.
4. **The rules are readable.** A player or reviewer can read the score rules in
   plain words, and the Lean definitions match those words.

Not in this version: hills, footpaths, energy, trams. (A river and bridges
are in: §2.4.)

---

## 2. The map

### 2.1 Roads come first, blocks are the spaces between them

The map is a **road network**: intersections joined by road segments.
Each intersection has whole-number x, y coordinates.

- A **block** is an area enclosed by roads. It is given by the loop of
  intersections around its edge. A neighborhood has **5–9 blocks** (generated levels: 5, 7 or 8).
- Two blocks are **neighbors** if they share a road segment on land, or a
  river segment with a bridge built on it (§2.4).
- A segment's **length** is the distance between its two ends, rounded to a
  whole number **[ASSUMED]**.
- A few intersections on the ring road are **gateways**, where outside buses
  and cars enter the neighborhood (§4.3).

Lean checks every map before using it:

- each block's edge is a closed loop of real road segments,
- each inner segment borders exactly two blocks, and each outer segment
  borders one,
- river segments are inner segments (they border two blocks),
- the blocks are connected (counting shared river segments).

A map that fails a check is rejected.

### 2.2 Making irregular shapes **[ASSUMED]**

1. **Outline.** Start with a circle and wobble its radius with smooth noise
   from the puzzle seed. Sample it at about 24 points.
2. **Seed points.** Scatter 5–9 points inside the outline. Spread them out by
   moving each point to the center of its area a few times (Lloyd
   relaxation). This keeps blocks of similar size and roughly round, so they
   are irregular but not wild.
3. **Regions.** Split the neighborhood into the areas closest to each point (a
   Voronoi diagram) and clip them to the outline. The borders between areas
   become **streets**. The outline becomes the **ring road**.
4. **Round** all coordinates to whole numbers and pass the map to Lean, which
   runs the checks in §2.1.

Where this runs: the geometry can be computed in TypeScript (for example with
`d3-delaunay`). That's safe because Lean checks the result, and the main
theorem holds for every map. Lean sends the coordinates back, and the frontend
draws roads from Lean's segments, so the drawing and the rules can't disagree.

### 2.3 Getting around

- **Walking and driving** use the road network. A trip from block A to
  block B goes from A's center to one of its corners, along roads to a corner
  of B, then to B's center. The shortest such trip counts. (Measuring from
  centers matters: neighbors share corners, so corner-to-corner distance
  would be 0.)
- **Bus stops** are at intersections. A block is **served** if a bus route
  that is on stops at an intersection on its edge.
- **The metro** runs underground to downtown (§4.2). It does not use streets.

### 2.4 The river and bridges

Each segment has a **kind** (only streets so far) and a **terrain**: `ground`
or `stream`.

- **The river.** `tools/genmap.mjs` picks a chain of inner segments that runs
  from one edge of town to the other and marks them `stream` (JSON
  `"stream"`). The river cuts the town in two.
- **Across the river, blocks are neighbors only over a bridge.** Two blocks
  whose only shared segments are river segments are **not** neighbors unless a
  bridge is built on one of those segments. (Blocks that also share a land
  road are neighbors anyway.)
- **Bridge sites.** Each puzzle lists up to 7 river segments where a bridge may
  be built (`Puzzle.bridgeSites`, segment numbers). The player turns each
  bridge on or off (`Solution.bridges`). Each bridge costs `bridgeCost`.
- **Buses cross only on bridges.** A bus route crosses the river only by
  driving along a river segment, and only if the bridge there is built. A
  route that is on without its bridges is **not valid**. (A route that drives
  along a river segment with no bridge site can never run.) The map generator
  makes routes cross the river only along a river segment, never through a
  river point on two land roads, and the puzzle generator makes every river
  segment a route uses a bridge site.

---

## 3. What the player builds

### 3.1 Building options

Each block gets **one** of these:

| Option | Floors | Provides |
|---|---|---|
| Empty | – | nothing |
| Housing | 1–3 | homes: 20 residents (4 cats) per floor |
| Office | 1–5 | 20 jobs per floor |
| Shop | 1–2 | sales to 20 customers a day per floor |
| Food (café/restaurant) | – | lunch for offices next door, dinner for neighbors |
| Park | – | green space, clean air next door |
| Bar | – | nightlife |

That's 14 choices in the catalog (`Building.catalog`). A building of 3 or
more floors, and a bar, is **loud**: it breaks "quiet" next door. Costs:
housing 100, office 120, shop 80 per floor, plus 30 per floor above the
first; food 70, park 40, bar 60.

### 3.2 Each level limits the choices

- **Allowed buildings.** Each level allows some of the catalog (§8.5 sizes).
- **No already-built blocks.** Generated levels start with every block open
  (`Generator.generate_no_fixed`). The rules still allow fixed blocks
  (`Puzzle.fixed`); only the Old Harbor test fixture uses them.

---

## 4. Transit

### 4.1 Bus routes

- Each puzzle comes with a fixed list of possible routes. A route is a path
  along streets. The player turns each route on or off.
- A block is **served** if a route that runs stops on its edge. Two blocks are
  **one bus ride apart** if one route that runs stops at both.
- A route **runs** if it is on and the bridges it needs are built (§2.4).

**Route rule.** A route that is on has its bridges built and at least
`minRouteRiders` riders a day (daily cost ÷ fare, rounded up). Riders are
the cats who ride it to work on the simulated day (5 residents each, §5.3),
plus downtown workers it carries from the metro station, counting only those
who got on a bus in the rush-hour process (§14.2).

### 4.2 Metro line to downtown

- A metro line enters the town at an edge block and runs 2 blocks inward
  (`Puzzle.metroSites`, from the edge in; `Puzzle.metroEntry` is where it
  enters, for drawing). The player may build **at most one** station, on one
  of those blocks.
- **Reach.** The station reaches its own block, its neighbors, and blocks one
  bus ride away (`Transit.stationReaches`).
- Cats in reach can **ride the metro downtown** to work (or to study).
- **Downtown workers** come by metro to fill the jobs in reach that cats from
  town leave open, at most 20 per block, and outside shoppers come to shops
  in reach.
- Transit lovers like living by it; a station on or next to a block breaks
  "quiet" there.

**Station rule.** A station that is built has at least `minStationRiders`
riders a day: cats riding it (5 residents each), downtown workers and
shoppers.

### 4.3 Cars

A working cat drives if it is a driver, or if nothing it can reach without
a car has a free job and its block is not in metro reach (then it drives
downtown). Car trips make **traffic** on the driver's block and the blocks
next to it. Traffic breaks "quiet" and dirties the air (no "clean air"),
unless a park is next door.

---

## 5. Residents and culture

### 5.1 Groups, personalities and cats

Each level has 2–3 resident groups from a pool: families, students,
professionals, the elderly, artists, urbanites, rural newcomers
(`Generator.groupPool`), with shares like 50/30/20. Each group has **2–3
personality types**: the usual one, and one or two that flip one factor.
Each group also says how its cats spend the day, in percent: work / study /
retired, drive / bus / walk, eat out at lunch, go out in the evening.

**Cats.** Each housing block has one cat per 5 residents. Cat number `i` on
block `h` gets its traits from the level's simulation seed
(`catTraits`, `Rules/Cats.lean`): its resident type (by the types' shares),
what it does all day, how it gets around (a cat that hates transit always
drives), and whether it eats out and goes out. Building more floors adds
cats; the first cats stay the same.

### 5.2 Culture

For each personality and each factor, the puzzle says whether it **cares
about** it (+2), is **neutral** (0), or **hates** it (−1).

| Factor | Residents of a housing block have it if… |
|---|---|
| Parks | a park is next to their block |
| Nightlife | a bar is next to their block |
| Shops | a shop is next to their block |
| Food | a café or restaurant is next to their block |
| Quiet | nothing loud next door, no traffic, and no metro station on or next to the block |
| Transit | a route that runs stops at their block, or the station is on or next to it |
| Variety | at least 3 different kinds of building are next to their block |
| Clean air | no traffic on their block, or a park next to it |

"Next to" means a neighbor (§2.1): across the river only over a built bridge.

### 5.3 One simulated day (`Rules/Day.lean`)

The same every time for a layout and seed:

1. **Morning commute.** Cats go one at a time, block by block. A working cat
   takes a free job (one per 5 jobs) at an office it can reach: next door
   first (walk), then one bus ride away (bus; walkers don't take the bus).
   Drivers always drive (to such an office, or downtown). With no job in
   reach, a cat rides the metro downtown if its block is in metro reach,
   else drives downtown. Students ride the metro downtown if they can, else
   study at home. Retired cats stay home.
2. **Lunch.** A cat at an office that eats out walks to a café or restaurant
   next to the office, and back.
3. **Home** the same way it came.
4. **Evening.** A cat that goes out walks to a bar next to home (or else a
   café or restaurant), and back home.

Bus riders wait for buses in the rush-hour process (§14.2); routes count
the riders who got on. `report.cats` is exactly this day.

---

## 6. How a layout is scored

The layout and the seed decide the day (§5.3). Then for each block
(`Rules/Score.lean`):

1. **Happiness** (housing): each cat adds 5 × its happiness per person (its
   personality's feelings about the factors its block has).
2. **Crime** (housing): each cat below `unhappyLine` (1) costs
   `unhappyCost` × (line − happiness) × 5.
3. **Productivity** (offices): `jobWorth` (5) × filled jobs × (100 + bonus)
   ÷ 100. Jobs are filled by the cats who came to work there (5 workers
   each), plus downtown workers by metro. Bonus: 20% per office next door,
   at most 40%, plus 20% with a café or restaurant next door (lunch).
4. **Downtown jobs** (housing): 5 residents × 3 points for each working cat
   that rides the metro downtown, × 1 point if it drives downtown.
5. **Sales** (shops): `saleWorth` × min(customers it can serve, residents next
   door or one bus ride away, plus metro shoppers).

**Score** = sum over blocks of (happiness + productivity + downtown jobs +
sales − crime) − `shortageCost` × shortage (jobs − homes − downtown workers,
never below 0). All numbers are whole numbers.

**Rating** = 100 × (score − empty-town score) ÷ (best − empty-town score),
rounded down, at least 0; invalid layouts get 0.

---

## 7. Budget and validity

- **Cost** = buildings on open blocks + each route that is on (build plus
  `years` of running) + the station, if built (the same) + `bridgeCost` per
  bridge built.

A **solution** is one choice per block, the routes that are on, the metro
station (or none), and the bridges built. It is **valid** if:

1. it fits the puzzle (allowed buildings, fixed blocks, one switch per route
   and per bridge site, station on a block along the metro line),
2. total cost ≤ budget,
3. every route that is on has its bridges built and at least
   `minRouteRiders` riders on the simulated day, and
4. the station, if built, has at least `minStationRiders` riders.

The empty layout (nothing built, no routes, no station, no bridges) is always
valid (`empty_valid`).

---

## 8. What is proven

### 8.1 Main theorem (plain words)

> For every puzzle, if the solver returns a solution, that solution is valid,
> and no valid solution has a higher score.

In Lean, roughly:

```lean
theorem solve_is_best (p : Puzzle) (s : Solution) (h : solve p = some s) :
    Valid p s ∧ ∀ t, Valid p t → score p t ≤ score p s
```

The solver has a step limit, so it can return `none` ("ran out of steps").
The generator throws those puzzles away (§8.5), so players only see puzzles
with a proven best. The theorem covers the three original goals:

- **Solvable**: the returned solution is valid.
- **A best layout exists**: the returned solution is one.
- **The benchmark is right**: the game grades against it.

### 8.2 What a reviewer must read

The theorem means what `Puzzle`, `Solution`, `Valid` and `score` mean.
**Those definitions are the game rules.** Reviewing them means reviewing
§3–§7. The solver's code does not need review, because the proof covers it.
Run `#spec_surface solve_is_best` to list exactly what to read.

### 8.3 Checks that the rules mean what we think

- **Satisfiable**: an `example` on a concrete 7-block puzzle where `solve`
  returns a solution, with every rule checked.
- **Rejects bad solutions** (`#guard`s in `SevenBridges/Demo.lean`): each of
  these is not valid:
  - a route that is on without the bridge it crosses
  - a route with too few riders to pay for itself
  - a station with fewer than `minStationRiders` riders a day
  - a layout that goes over budget
  - a building the puzzle doesn't allow, or a change to a fixed block
- **The river**: in Old Harbor, blocks 0 and 3 share only a river segment;
  they are not neighbors without the bridge, and are with it.
- **Reference comparison**: on small puzzles, `solve` gives the same score as
  plain search through every solution (`bestByChecking`).

### 8.4 Keeping the solver fast

Without limits, 12 choices on 9 blocks, times bus routes, times station
options, is tens of billions of solutions. Compiled Lean can score about a
million per second. These steps close the gap:

| Step | What it does | Remaining work | Proof effort |
|---|---|---|---|
| 1. Puzzle limits (§3.2) | ~6 choices per block, 0–3 fixed blocks | 50,000 – 10 million layouts | none (puzzle data) |
| 2. Precompute distances | road distances for each transit choice, computed once per puzzle | each score is table lookups, ~1 µs | small |
| 3. One question, not a search for the best | ask only "is anything better than the planted score L?" | most branches cut early | medium |
| 4. Bounds | cut a partial layout when its best case ≤ L, or its cheapest finish is over budget | usually 10,000–100,000 checked | one lemma per cut |
| 5. Step limit | stop and return `none` after a fixed number of steps | worst case capped | small |
| 6. Parallel | each bus-and-station combination on its own core | ÷ number of cores | none (take the best) |

**How the bounds work.** For a search node (each block's remaining options,
and a group of transit choices) each block gets a **cap** for each option,
from what is still possible next to it (`Bound.lean`): facts that could
happen count if good, facts that must happen count if bad. The bound is the
best sum of caps within the budget (a knapsack), or a quicker trade-off
estimate. Two caps are tried, and the smaller bound is used:

- `valueCap`: happiness at the best mix of neighbors, every job an office
  could fill, every downtown job a block's working cats could have, sales.
- `valueCapW`, which **counts each worker once**: a cat works in one place,
  so instead of counting jobs at the offices, it counts at home 40 points
  (5 residents × 8, the most a worker makes with the biggest office bonus)
  per working cat, and at the offices only the downtown workers.

Traffic from the cats' day is bounded with the same could/must idea: a
block whose cats work could have cars; one with a working driver surely has
them.

**What the proof needs** (`BoundProofs.lean`, `DayProofs.lean`):

- **Bounds are correct:** no valid layout in a node scores above its bound
  (`score_le_bound`, `score_le_of_knapsackCut`). One lemma per part of the
  score; the day facts used: a cat only works where it can get to, only
  working cats drive, working drivers always drive, only cats in metro reach
  ride the metro, and each cat is in the day once.
- **Cutting is safe**, and **nothing is missed** (`BranchProofs.lean`).

### 8.5 Level generation

`SevenBridges/Generator.lean`, not trusted: `solve_is_best` guarantees the
best plan of every level it returns.

1. **Map** from `tools/genmap.mjs` (§2.2).
2. **Random level**: 2–3 groups from the pool with random minority types,
   allowed buildings (by size, below), bridge sites, the metro line (an
   edge block and the touching block closest to the middle), and the
   simulation seed. No starting blocks.
3. **Budget**: the cost of a random layout plus 60–160.
4. **Proof**: run `solve` with at most `attemptFuel` steps.
5. **Keep** the level if the best plan has homes and beats the empty town,
   its happiness and its productivity (with sales) are each at least a
   tenth of its score, and **random play does badly**: of up to 500 random layouts that fit the
   budget (random choices, cut to the budget, transit dropped if it breaks a
   rule), the median rates at most 50 and 95% rate at most 85.
6. Otherwise try another random level on the same map, until
   `generatorStepBudget` steps are used. The bridge then tries up to two new
   maps (seed + 7919, + 2·7919).

**Sizes.** Less choice on bigger maps, so the proven solver finishes in time:

| Size | Blocks | Homes | Offices | Food, shop, bar, park | Shops | Metro blocks | Bridge sites |
|---|---|---|---|---|---|---|---|
| easy | 5 | 1–3 floors | 1 or 2 floors, plus 2 other heights of 1–5 | all 4 | 1–2 floors | 2 | up to 2 |
| medium | 7 | 1–3 | 1 or 2 floors | 3 of 4 | 1–2 | 2 | 1 |
| hard | 8 | 1–2 | 1 or 2 floors | 1 of 4 | 1 | 2 | 1 |

Hard levels are 8 blocks, not 9: with 9 open blocks the proof took 2–10
million steps (10–40 s).

### 8.6 Time limits, as proven step limits

Lean can't prove anything about seconds. It proves a bound on **work**
(search steps and random layouts tried); seconds = work × time per step,
measured.

| Theorem | Says |
|---|---|
| `solveWithFuel_steps_le` | the fast solver takes at most `fuel` steps (`searchFuel` = 12,000,000 for `solve`) |
| `solveWork_le` | plain search scores at most `stepLimit` layouts |
| `Generator.generate_work_le` | the generator takes at most `generatorStepBudget` (1,500,000) steps in total, at most `attemptFuel` (450,000) of search per attempt |

Measured on this machine (12 cores), `node tools/timegen.mjs <binary>
[blocks:seed …]`, one Lean call per map, seeds 31–36 and 41–43:

| Size | Times (ms) | Found a level |
|---|---|---|
| easy (5) | 2187, 1710, 1318, 574, 1131, 3502, 921, 1182, 1197 | 9 of 9 |
| medium (7) | 8841, 2237, 1700, 2221, 1760, 6280, 3657, 6000, 7940 | 7 of 9 |
| hard (8) | 7660, 706, 2667, 8673, 7086, 373, 615, 1593, 1223 (seeds 31–36, 41–43) | 8 of 9 |

Every call took under 9 s (about 5 µs per step). A call that finds no
level is retried by the bridge on a new map, up to 3 maps (so up to about
25 s in the rare worst case).

**The search.** Transit choices are grouped by (routes, bridges); each group
holds every station choice. The search splits each block's options (homes
or not, then kind), then picks the transit, then 3+ floors or not, then the
building. The first guess climbs from the empty layout and from each allowed
building on every block. Pieces run one after another with 50,000 steps; if
that runs out, they are dealt into 12 hands that run in parallel.

---

## 9. Architecture

```
Browser (Three.js + TypeScript)
   │  WebSocket, JSON
Bridge (Node or Bun, ~50 lines, no game logic)
   │  stdin/stdout, one JSON message per line
Lean binary (all rules, solver, generator)
```

### Messages

| From → To | Message | Contents |
|---|---|---|
| Frontend → Lean | `newPuzzle` | seed, size (`easy`, `medium`, `hard`) |
| Lean → Frontend | `puzzle` | blocks, roads, allowed buildings, routes, `metroSites` (also as `stationSites`), `metroEntry`, `simSeed`, bridge sites, groups, culture text, budget |
| Frontend → Lean | `evaluate` | a solution |
| Lean → Frontend | `result` | valid?, which rules failed, the report (below) |
| Frontend → Lean | `solve` | – |
| Lean → Frontend | `best` | best solution, its report, name of the proven theorem |
| Bridge → Lean | `generate` | a map and routes from `tools/genmap.mjs`, and a seed |
| Lean → Bridge | `generated` | the new level (now the current one), `seed`, `info` (attempts, work, `randomPlay` {median, p95, rated}), `verified` |

New JSON fields (Version 2):

- `verified`: `{"theorem": "SevenBridges.solve_is_best", "simSeed": N, "bestScore": S}`.
- `puzzle.simSeed`: number. `puzzle.metroSites`: block numbers, from the
  edge in. `puzzle.metroEntry`: `{"x", "y"}`.
- `report.cats`: one per cat, in town order: `{"id": "3-0", "home", "group",
  "type", "mobility": "walker"|"bus"|"driver", "day": "works"|"studies"|"retired",
  "eatsOut", "goesOut", "happiness", "legs": [{"from", "to", "mode":
  "walk"|"bus"|"car"|"metro", "phase": "commute"|"lunch"|"evening"|"home",
  "route"?}]}`. A place is a block number or `"downtown"`; `route` is on bus
  legs only.
- `report.carTrips`: cats who drive. `report.streets`: `[{"segment", "cars"}]`,
  the driving cats of the blocks each segment borders.
- `report.blocks[]`: adds `traffic`, `polluted` (booleans), `cars` (driving
  cats of the block and the blocks next to it), and `neighbors`:
  `[{"block", "change"}]`, the neighbor's value with this block empty minus
  its value now.

The frontend never computes a score or decides a trip. It only animates the
trips Lean returns.

---

## 10. Frontend look

A cozy, hand-built look made from soft, irregular shapes.

- **Roads**: drawn along Lean's road segments (§2.1), with intersection
  coordinates taken from Lean. Corners can be rounded for looks.
- **Shoreline**: the land around the ring road gets a soft edge, shaped by
  smooth noise from the puzzle seed.
- **Inside each block**: an irregular grid of four-sided cells filling the
  block's shape. Build it by splitting the block into triangles, joining
  random pairs of triangles into four-sided cells, splitting each of those
  into four, then smoothing the points so the cells look organic. The seed
  drives the randomness, so the same puzzle always looks the same.
- **Buildings**: stacked modules on the cells. The number of floors drawn
  matches the stories Lean reports.
- **Subway**: a station entrance on its block. Outside riders appear there.
- **People and buses**: move along the trips Lean returns. Movement between
  points is smoothed in the browser.

- **Distant city**: around the neighborhood, desaturated, almost gray city
  buildings fading into haze, to show the neighborhood is part of a city.

Everything in this section is for looks only. No rule depends on it.

### 10.1 Camera

| | Isometric (orthographic) | Perspective, narrow field of view (chosen) |
|---|---|---|
| Reading the puzzle | block sizes compare fairly | almost as fair at 20–25° field of view |
| Look | clean diorama | same diorama look, plus real depth |
| Distant city | no natural fade with distance | fades into fog naturally |
| Picking blocks | easy | easy |

Chosen: perspective with a narrow field of view at an isometric-like angle,
orbit around the vertical axis, and zoom.

### 10.2 Screen and flow

Heads-up display: **Score**, **Objective**, **Culture**, **Buildings you can
place** (with prices, plus route and station switches), **Budget**,
**Happiness**.

1. **Edit**: choose what goes on each open block, which routes run, and where
   the station goes. The budget updates live (Lean computes the cost).
2. **BUILD**: the buildings go up, Lean scores the layout, and the score card
   is published: score, happiness, productivity, crime, and any broken rules.
3. **Edit again**: the current build is kept, so the player can change it and
   press BUILD again.
4. **Compare with best**: Lean's proven best score, and the player's percent
   of it.

---

## 11. Toolchain

- Lean 4.35.0 (newest stable), pinned in `lean-toolchain`. Core only: no
  Mathlib, no Batteries, so builds take seconds.
- The final `lake check` / `lake comparator` run needs Linux. Use Docker.
- `#print axioms solve_is_best` must show only `propext`,
  `Classical.choice` and `Quot.sound`. No `native_decide`.
  `Checks/Audit.lean` runs this check.

---

## 12. Build order

1. Lean types: road network, map checks, `Puzzle`, `Solution`, `Valid`,
   `score`, with one hand-made 7-block map and `#guard` tests.
2. `solve` by plain search with a step limit, plus `solve_is_best`.
3. Lean binary + JSON + bridge. Frontend shows flat block polygons, roads
   and numbers.
4. Map generator (§2.2) and solution-first puzzle generator (§8.5).
5. Bounds and cuts (§8.4, steps 3, 4 and 6) and their proofs.
6. Three.js art: irregular grid, buildings, animation.
7. Later: terrain, bridges, footpaths, area-based housing shortage.

---

## 13. Open questions

1. Housing shortage: across the whole neighborhood (current), or per area?
2. Do groups spread evenly across housing (current), or pick blocks?
3. How to combine happiness and productivity: equal weight, or set by
   culture?
4. Are trips other than work (shops, parks, bars) real trips that use
   transit, or only counted by nearness (current)?
5. The player-difficulty thresholds in §8.5 (85%, 5%).
6. All other numbers marked **[ASSUMED]**. In code they all live in
   `SevenBridges/Rules/Puzzle.lean`, namespace `Numbers`.
7. Generator filter "culture matters" (§8.5) is not built yet: it needs a
   second full solve per attempt.

Decided:

- Planted solutions are random, then fixed quickly (§8.5).
- Footpaths through parks come later (§2.4).
- It's a neighborhood of blocks, with a small transit network (§4).
- Walkability is a culture factor, not a given (§5.2).
- People come in from outside, by gateway or subway (§4.2, §4.3).
- Fast to prove, but hard for the player (§1, §8.5).
- The subway pays for itself by reaching a minimum number of riders a day
  (§4.2).
- Outside workers arriving by subway reduce the housing shortage (§6).
- A station sits on a block alongside a building (§4.2).
- Subways are quiet: a station does not count against "quiet". A station
  near nothing (no jobs, shops or bars) gets no riders and fails its rule.
- Lean version: 4.35.0, the newest stable release. Core only, no Mathlib.
- Generating a puzzle must take at most 10 seconds (§8.6).
- UI: edit, press BUILD to get a score, edit again (§10.1).

---

## 14. Next: more strategy, and a realistic bus process (planned)

Both keep the rules **local** (a block's value depends only on the blocks it
watches), so the branch-and-bound bound still works: every new factor needs
only a "could it still happen?" and a "must it happen?" check.

### 14.1 Strategy rework (after playtesting)

**Problem found.** On Old Harbor, 3,000 random layouts: the valid ones rate a
median of 0 and the top 10% rate 47 or more; sensible plans rate about 30–60; the
proven best leaves a lot empty. The score has *cliffs* (one extra job triggers
crime on every block) and jobs are worth little next to happiness, so careful
play feels no better than luck, and the best plan isn't explainable.

**Done** (rules now as in §4–§7): proportional shortage and crime, jobs worth
points, shops need customers, office clusters, variety, the rating. Then cut
to a smaller visible set: no short-commute or walkability factor, no park
bonus for offices, shops and bars have no jobs, one route rule (riders), and
the river, bridges and personalities were added.

**Strategy check** (`lake exe ratingdist`, not in the generator): over 2,000
random valid layouts, the median rating should be at most 50 and the 95th
percentile at most 85, so thinking clearly beats luck. Puzzles come in three sizes: easy (5
blocks), medium (7), hard (9).

### 14.2 Realistic bus process (not random)

Lean simulates one morning rush hour, step by step, the same way every time:

1. **Who waits where.** Each group whose commute is by bus waits at the stop
   nearest their home, heading for the stop nearest their job.
2. **Buses run on a schedule.** Each route runs `busesPerRush` buses in each
   direction, evenly spaced. Waiting riders arrive evenly over the rush hour,
   so each bus finds its share waiting.
3. **At each stop**, a bus first lets off riders for this stop, then lets on
   waiting riders heading its way, until it is full (`busCapacity`).
4. **Left behind.** Riders who don't fit wait for the next bus. Anyone still
   waiting after the last bus doesn't count as having a short commute.

The report lists boardings and alightings per stop and the fullest load per
bus. The animation shows exactly these cats getting on and off.

Proofs about the process:

- a bus never carries more than `busCapacity`,
- every rider who gets on gets off at their stop,
- riders = boardings = alightings,
- the riders who get on plus those left behind = everyone who waited.

---

## 15. Version 2 (decided 2026-11-01)

### 15.1 Player experience

- **Title screen**: "Seven Bridges", buttons **Start** and **The rules**.
- **The rules**, as few bullets as possible:
  - Build on every block: homes, offices, shops, food, parks, bars.
  - Neighbors matter: what's next door decides how happy and how productive each block is.
  - Connect the town: roads, bridges, buses, a metro to downtown. Cars work too, but bring traffic and pollution.
  - Stay within budget.
  - Your rating is out of 100. 100 is the best possible plan, proven by Lean for this town's cats.
- **Every level is a new random map** (easy 5, medium 7, hard 8 blocks; hard was 9, cut to 8 so the proof fits in 10 s, §8.5). No starting blocks.
- **Verified before you start**: a level opens only after Lean has proven its best plan.
  The title card shows the level's seed: "Town #N, simulation #N, best plan proven ✓".
- **Two numbers matter**: happiness (homes) and productivity (jobs). The score adds them.
  The trade-off is the game: offices next to homes help commutes but hurt quiet and air.

### 15.2 The cats: a seeded simulation, proven per level

- Each level has a **simulation seed**. From it, every resident cat gets its own traits:
  group, personality, how it gets around (walker, bus rider, driver), and its day
  (works, studies, retired; eats out or not; goes out at night or not).
- **One simulated day**, step by step and the same every time for that seed:
  morning commute, lunch, evening out, back home.
- Each cat picks places it can reach: next door, one bus ride away, by metro, or by car.
  Drivers who find no job nearby drive downtown.
- The day produces: who works where (productivity), who eats and drinks where, car trips
  (traffic and pollution), bus and metro riders (with the rush-hour process), and each
  cat's happiness.
- **The score is a function of the layout and the seed**, so `solve_is_best` proves the best
  plan for exactly this simulation. Different levels have different simulations.
- **Proven about the simulation** (`DayProofs.lean`): every cat ends the day at home, along
  trips that each start where the last one ended (`legs_return_home`); the day has one entry per
  cat in town and no cat twice (`simulate_cats`, `population_nodup`); at every moment the cats at
  all places add up to all cats (`cats_conserved`); buses never exceed capacity and
  boarded + left behind = waited (`BusProofs.lean`).
- The animation plays exactly the day Lean simulated (`report.cats`), so what you see is what
  was scored.

### 15.3 Rules (bounded per block, so the solver stays fast)

Built as described in §3–§6. Changes from the plan: neutral factors are worth 0 (only
cares and hates count), the unhappy line is 1, and pollution is the "clean air" factor.


| Building | Effect |
|---|---|
| Home (1–3 floors) | happiness from what's next door, each cat by its own tastes |
| Office (1–5 floors) | jobs filled by cats who can reach it; bonus next to offices and food |
| Shop (1–2 floors) | sales to cats who can reach it |
| Food (café/restaurant) | lunch for workers nearby (office bonus), dinner for residents; some cats love it |
| Park | happiness for neighbors; cleans the air next to it |
| Bar | nightlife: some love it, some hate the noise |

- **Cars**: a cat drives when walking, bus and metro don't reach its destination. Each car
  trip adds traffic and pollution to its home block and its neighbors. Traffic hurts quiet;
  pollution hurts everyone's happiness; parks next door reduce it.
- **Metro line to downtown**: a line enters from one edge of the map; pick one station block
  among the blocks along it, or none. Cats in reach can commute to downtown jobs; downtown
  workers can reach your offices (capped). Transit lovers love living by it; it's noisy next door.
  Needs a minimum number of riders.
- **Buses and bridges** as now. Budget as now.
- **Groups pool**: families, students, professionals, the elderly, artists, urbanites, rural
  newcomers. Each level picks 2–3.

### 15.4 Look

- Taller offices (up to 5 floors) and a downtown skyline of tall towers in the distance,
  where the metro line comes from.
- Every block arranges its buildings differently (seeded layout templates and rotations).
- Food places: cafés with terraces, a small restaurant with a sign.
- Cars driving on streets, haze over polluted blocks, cleaner air near parks.
