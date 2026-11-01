# Seven Bridges: Design

Seven Bridges is a small neighborhood-planning puzzle. Each puzzle is a
neighborhood of 5–9 blocks. The player chooses what to build on each block,
which bus routes to run, and whether to build a subway station. Lean computes
the score, and Lean proves that the game's "best possible layout" really is
the best.

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
  intersections around its edge. A neighborhood has **5–9 blocks**.
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
- **The subway** runs underground. It does not use streets and does not slow
  traffic (§4.2).

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

| Option | Stories | Provides |
|---|---|---|
| Empty | – | nothing |
| Housing | 1–3 | homes |
| Office | 1–3 | jobs |
| Shop | 1–3 | jobs and shopping |
| Park | – | green space |
| Bar | – | nightlife and some jobs |

That's 12 choices in the full catalog.

Per story: housing has 20 residents, an office has 20 jobs, a shop serves
20 customers a day. Only offices have jobs. Parks and bars score no points of
their own: they matter through their neighbors (§5.2).

Taller buildings give more homes or jobs, cost more, and make neighbors
unhappy (see "quiet" in §5). That's why neither "all 3-story" nor
"all 1-story" wins.

### 3.2 Each puzzle limits the choices **[ASSUMED]**

- **Allowed buildings.** Each puzzle allows about 6 of the 12 catalog
  choices, for example "no bars, and offices up to 2 stories."
- **Already-built blocks.** 0–3 blocks come fixed, for example an old church
  or a school. The player can't change them, but they still count for
  neighbors, trips and happiness.

These limits make puzzles more varied, and they are the cheapest way to keep
the solver fast (§8.4).

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
residents who ride it to a job (they have no job next door, don't hate
transit, and the route stops at a block with jobs), plus subway workers it
carries from the station.

### 4.2 Subway station

- The player may build **at most one** station, on any block (generated
  puzzles list every block as a site).
- The station sits on a block alongside whatever is built there.
- **Reach.** The station reaches its own block, its neighbors, and blocks one
  bus ride away.
- **Outside workers** come by subway to fill the jobs in reach that local
  residents don't fill. They fill those jobs and reduce the housing shortage.
- **Outside shoppers**: `shoppersPerShopStory` per shop story in reach. They
  count as riders.

**Station rule.** A station that is built has at least `minStationRiders`
riders a day (outside workers plus outside shoppers).

### 4.3 People from outside

Only by subway (§4.2): outside workers and shoppers. Gateways for outside cars
and buses are not built.

---

## 5. Residents and culture

### 5.1 Groups and personalities

Each puzzle has 2 resident groups with a fixed mix, for example "60% families,
40% students". Every housing block holds that same mix.

Each group has **2–3 personality types** (`Group.types`). The first is the
usual one; most of the group has it. Each minority type flips one factor, for
example "20% of Families are Night owls, who care about nightlife". A type's
residents on a block are residents × group share × type share, rounded down.

### 5.2 Culture

For each personality and each factor, the puzzle says whether it **cares
about** it (+2), is **neutral** (+1), or **hates** it (−1).

| Factor | A resident of a housing block has it if… |
|---|---|
| Parks | a park is next to their block |
| Nightlife | a bar is next to their block |
| Shops | a shop is next to their block |
| Quiet | no 3-story building and no bar is next to their block |
| Transit | a route that runs stops at their block, or the station is on or next to it |
| Variety | at least 3 different kinds of building are next to their block |

"Next to" means a neighbor (§2.1): across the river only over a built bridge.
The culture text is generated from the groups and their types, so it always
matches the rules.

---

## 6. How a layout is scored

A block's value depends only on the blocks it **watches**: itself, its
neighbors, and blocks one bus ride away (`SevenBridges/Rules/Score.lean`).

For each block:

1. **Happiness** (housing): for each personality type of each group, its
   residents there × its happiness per person (the sum of its feelings about
   the factors it has).
2. **Crime** (housing, a slope): for each type below `unhappyLine`,
   `unhappyCost` × (line − happiness per person) × its residents there.
3. **Productivity** (offices): `jobWorth` × filled jobs × (100 + office
   bonus) ÷ 100. Jobs are filled by residents next door or one bus ride away;
   if the station reaches the block, outside workers fill the rest. The office
   bonus is `officeBonusPerOffice` % per neighboring office, at most
   `officeBonusMax` %.
4. **Sales** (shops): `saleWorth` × min(customers it can serve, residents
   next door or one bus ride away).

Bars and parks score nothing themselves.

**Score** = sum over blocks of (happiness + productivity + sales − crime)
− `shortageCost` × shortage, where shortage = jobs − homes − outside workers
(never below 0). All numbers are whole numbers.

**Rating** = 100 × (score − empty-town score) ÷ (best − empty-town score),
rounded down, at least 0; invalid layouts get 0.

---

## 7. Budget and validity

- **Cost** = buildings on open blocks + each route that is on (build plus
  `years` of running) + the station, if built (the same) + `bridgeCost` per
  bridge built.

A **solution** is one choice per block, the routes that are on, the station
site (or none), and the bridges built. It is **valid** if:

1. it fits the puzzle (allowed buildings, fixed blocks, one switch per route
   and per bridge site, station on a listed site),
2. total cost ≤ budget,
3. every route that is on has its bridges built and at least
   `minRouteRiders` riders, and
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

### 8.4 Keeping the solver under a second for 9 blocks

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

**How the bounds work.** The generator already knows a lower bound: the
planted solution's score L. For any partial layout, the upper bound U is the
score so far, plus each open block's best possible score, plus the best
possible neighbor bonuses. If U ≤ L, nothing in that branch can win, so it's
skipped. Blocks with the most neighbors are filled first, so neighbor bonuses
become exact early and the cuts get sharper.

If the bound for the empty layout already equals L, the proof needs no search
at all.

**Why not binary search on the score?** Each question "is there a layout
scoring at least T?" costs a full search when the answer is no. Asking once,
at T = L + 1, is the cheapest question.

**What the proof needs:**

- **Bounds are correct:** no completion of a partial layout scores above its
  bound. One lemma per part of the score (block value, neighbor bonuses,
  crime, transit).
- **Cutting is safe:** if a branch's bound ≤ L, nothing in it beats L.
- **Nothing is missed:** the search covers every solution that wasn't cut.

Start with steps 1, 2 and 5 on plain search. Add steps 3, 4 and 6 when
puzzles need it.

### 8.5 Puzzle generation: solution first, then the puzzle

The generator picks the answer first, then builds the puzzle around it.

1. **Map.** Make the roads and blocks (§2.2).
2. **Plant a solution.** Pick a **random** layout, route set and station
   choice. Throw it away at once if it is obviously dull, for example no
   housing, no jobs, or every block the same.
3. **Fit the puzzle to it.**
   - Culture: choose groups and their cares/hates so the planted layout's
     features are rewarded and its alternatives are penalized.
   - Limits: choose the allowed buildings and any fixed blocks (§3.2).
   - Routes: offer the planted routes plus 1 decoy that fails a route rule
     (for example, a decoy that only takes riders from a planted route).
   - Budget: the planted solution's cost plus a small margin.
4. **Quick check (fast, not proven).** Try every small change to the planted
   solution: change one block, change one height, turn one route on or off,
   or move the station. That's about 100 tries. If any of them scores higher,
   adjust the culture or budget against that change and try again. Most bad
   attempts fail here in milliseconds.
5. **Gap check.** Compute the upper bound U for the whole puzzle (§8.4). If
   U − L is too large, the proof would be slow: tighten the budget, fix a
   block, or adjust the culture, then go back to step 4.
6. **Full check with the proven solver.** Run `solve`. Keep the puzzle only if
   all the checks below pass.
7. If the full check fails, adjust against the better solution `solve`
   found, as in step 4, and check again. After a few failed rounds
   **[ASSUMED: 5]**, start over with a new seed.

**Checks in step 6.**

The puzzle must be correct:

- `solve` returns a solution (didn't run out of steps),
- its score equals the planted score, and no other valid solution reaches it
  (the best is **unique**).

The puzzle must be interesting:

- the best solution **uses transit** (a bus route or the station),
- the culture **matters**: with every factor set to neutral, the best
  solution changes.

The puzzle must be **hard for the player** **[ASSUMED]**:

- **Greedy fails.** Filling each block with whatever looks best for that block
  alone scores well below the best, for example under 85%.
- **Small fixes aren't enough.** From the greedy layout, making the single
  best change over and over gets stuck below the best.
- **There are traps.** Several clearly different layouts score within 5% of
  the best.
- **The best needs a non-obvious move,** for example leaving a block as a park
  when an office there looks better, or skipping a route that looks useful.

Fast to prove and hard to solve don't conflict. The solver sees the bounds
and the planted score. The player sees neither, and a puzzle with many
near-best traps can still have a small gap between U and L.

**Built so far** (`SevenBridges/Generator.lean`): a random puzzle (groups
with personalities, allowed buildings, bridge sites, built blocks), a random
planted layout that sets the budget, then the proven solver. A puzzle is kept
if its best layout uses transit (a route, the station or a bridge), has homes,
and greedy play scores under 90% of it. The quick check (step 4) and the gap
check (step 5) are not built.

**Sizes.** The generator offers less choice on bigger maps, so the proven
solver finishes in time:

| Size | Blocks | Heights | Bridge sites | Blocks already built |
|---|---|---|---|---|
| easy | 5–6 | 1–3 | up to 3 | 0 |
| medium | 7 | 1–3 | up to 2 | 1 |
| hard | 8–9 | 1–2 (shops 1) | 1 | 3 |

Bridge sites are first the river segments a route uses, so those routes can
run.

**The generator doesn't need a proof and isn't trusted.** It can be clever,
messy, or written in TypeScript. Planting is only a way to aim for good
puzzles. Step 6 is what guarantees the benchmark, and step 6 relies on
`solve_is_best`. If the generator plants a solution that isn't the best,
step 6 finds the better one and the puzzle is fixed or thrown away.

### 8.6 Time limits, as proven step limits

Lean can't prove anything about seconds. It proves a bound on **work** (search
steps and layouts scored); seconds = work × time per step, measured.

| Theorem | Says |
|---|---|
| `solveWithFuel_steps_le` | the fast solver takes at most `fuel` steps (`searchFuel` = 3,000,000 in the game) |
| `solveWork_le` | plain search scores at most `stepLimit` layouts |
| `Generator.generate_work_le` | the generator takes at most `generatorStepBudget` (350,000) steps in total, at most `attemptFuel` (175,000) per attempt |

Measured on this machine (12 cores): 5–25 µs per step, so the generator takes
at most about 8.5 s. `node tools/timegen.mjs <binary> [blocks:seed …]`
re-measures it. On 40 maps of 5–9 blocks, every run took ≤ 8.5 s; runs that
found a puzzle took ≤ 4 s; about 1 in 10 runs gives up (the caller retries
with another seed).

**The search.** Transit choices are grouped by (routes, bridges); each group
holds every station choice. Routes on without their bridges are left out. The
search splits each block's options (homes or not, then kind), then picks the
transit, then heights. The work is first run piece by piece with 200,000
steps; if that runs out, the pieces are dealt into 8 hands that run in
parallel, each with an equal share of the fuel.

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
| Frontend → Lean | `newPuzzle` | seed |
| Lean → Frontend | `puzzle` | blocks, roads, gateways, allowed buildings, fixed blocks, routes, station sites, groups, culture text, budget |
| Frontend → Lean | `evaluate` | a solution |
| Lean → Frontend | `result` | valid?, which rules failed, cost, happiness, crime, productivity, score, trips for animation |
| Frontend → Lean | `solve` | – |
| Lean → Frontend | `best` | best solution, its score, name of the proven theorem |
| Bridge → Lean | `generate` | a map and routes from `tools/genmap.mjs`, and a seed |
| Lean → Bridge | `generated` | the new puzzle (now the current one), attempts and work used |

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
