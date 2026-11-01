import SevenBridges.Proofs

/-!
# An upper bound on the score of a partly decided layout (DESIGN.md §8.4)

The solver narrows down each block's options step by step. Before it goes
deeper, it needs a number that no finished layout can beat. This file
computes that number.

A search node says, for each block, which buildings it may still hold
(`opts j`), and which transit choices are still open (`Plan.group`).

Each block is bounded on its own, from what is still possible next to it:

- **Neighbors.** Across the river, two blocks are neighbors only if the bridge
  between them is built. When that isn't settled yet, the block **could** be a
  neighbor, but need not be.
- **Happiness and crime.** The neighbors of a block can offer it only certain
  mixes of things (a park, a bar, a shop, food, something loud, homes,
  offices, cars), one building each. For each mix that can happen, each
  factor is then known, except "transit", "metro station next door" and
  "traffic". For those we ask: **could** it be true, and **must** it be true?
  A good factor counts if it could happen; a bad one only if it must. The
  best mix counts. Crime counts only as far as even the best happiness is
  below the line.
- **Traffic.** A block whose cats work could have cars; one with a working
  driver surely has them (drivers always drive).
- **Jobs and sales.** At most every job is filled (if the metro could reach
  the block), or as many as the most workers who could live nearby. Offices
  get the biggest bonus their neighbors could give.
- **Downtown jobs.** At most every working cat of the block commutes
  downtown, at the metro rate if the metro could reach it, else the car rate.
- **The shortage penalty** is never negative, so leaving it out is safe.

Each block gets a cap for each building it may hold, together with that
building's cost. The bound is the best total of caps within the budget
(`knapsack`), or a quicker estimate of it (`Plan.bound`).

The proof that the bound is safe is in `SevenBridges/BoundProofs.lean`.
-/

namespace SevenBridges
open Numbers

/-! ## Yes/no facts that are not settled yet -/

/-- What we know about a yes/no fact: `could` = it might be true,
`must` = it is surely true. -/
structure Maybe where
  could : Bool
  must : Bool
deriving Repr, Inhabited, BEq

namespace Maybe

/-- `r` is right about the fact `v`: if `v` must hold, it does; if `v` holds,
it could. -/
def Covers (r : Maybe) (v : Bool) : Prop := (r.must = true → v = true) ∧ (v = true → r.could = true)

/-- A fact we know exactly. -/
def exact (v : Bool) : Maybe := ⟨v, v⟩

/-- Both facts. -/
def and (a b : Maybe) : Maybe := ⟨a.could && b.could, a.must && b.must⟩

/-- Either fact. -/
def or (a b : Maybe) : Maybe := ⟨a.could || b.could, a.must || b.must⟩

/-- The opposite fact. -/
def not (a : Maybe) : Maybe := ⟨!a.must, !a.could⟩

/-- The fact holds for some item of `l`. -/
def anyOf {α : Type} (l : List α) (f : α → Maybe) : Maybe :=
  ⟨l.any fun x => (f x).could, l.any fun x => (f x).must⟩

/-- A test on a building, when the building is one of `l`. -/
def ofTest (l : List Building) (test : Building → Bool) : Maybe := ⟨l.any test, l.all test⟩

/-- At least `k` of the facts hold. -/
def atLeast (k : Nat) (l : List Maybe) : Maybe :=
  ⟨decide ((l.filter (·.could)).length ≥ k), decide ((l.filter (·.must)).length ≥ k)⟩

/-- A number 0–3 for what we know about a fact. -/
def code (r : Maybe) : Nat := (if r.could then 1 else 0) + (if r.must then 2 else 0)

/-- The fact a code 0–3 stands for. -/
def ofCode (i : Nat) : Maybe := ⟨i % 2 == 1, i / 2 % 2 == 1⟩

end Maybe

/-! ## What a block may hold -/

/-- What we know about the building on one block. -/
structure Spot where
  office : Maybe
  food : Maybe
  /-- The most residents it could have. -/
  residents : Nat
deriving Repr, Inhabited

/-- What we know about a block that holds one of the buildings in `l`. -/
def Spot.of (l : List Building) : Spot where
  office := .ofTest l Building.isOffice
  food := .ofTest l Building.isFood
  residents := l.foldl (fun m b => max m b.residents) 0

/-! ## Building numbers -/

/-- A number for each building, 0–18 (for tables, and for copying). -/
@[noinline] def Building.code : Building → Nat
  | .empty => 0
  | .park => 1
  | .bar => 2
  | .food => 3
  | .housing h => 3 + h.stories
  | .office h => 8 + h.stories
  | .shop h => 13 + h.stories

/-- The building with a number. -/
@[noinline] def Building.ofCode : Nat → Building
  | 1 => .park
  | 2 => .bar
  | 3 => .food
  | 4 => .housing .one
  | 5 => .housing .two
  | 6 => .housing .three
  | 7 => .housing .four
  | 8 => .housing .five
  | 9 => .office .one
  | 10 => .office .two
  | 11 => .office .three
  | 12 => .office .four
  | 13 => .office .five
  | 14 => .shop .one
  | 15 => .shop .two
  | 16 => .shop .three
  | 17 => .shop .four
  | 18 => .shop .five
  | _ => .empty

theorem Building.ofCode_code (b : Building) : Building.ofCode b.code = b := by
  cases b <;> (try rename_i h; cases h) <;> rfl

theorem Building.code_lt (b : Building) : b.code < 19 := by
  cases b <;> (try rename_i h; cases h) <;> decide

/-! ## Cars -/

/-- Some cat of block `x` works, when `x` holds building `b`: its cats could drive. -/
def carsCould (c : Context) (x : Nat) (b : Building) : Bool :=
  (residentsOn c x b).any fun r => r.traits.day == .works

/-- Some cat of block `x` works and is a driver, when `x` holds building `b`:
its cats surely drive. -/
def carsMust (c : Context) (x : Nat) (b : Building) : Bool :=
  (residentsOn c x b).any fun r => r.traits.day == .works && r.traits.mobility == .driver

/-- The most cats of block `x` who work, when it holds building `b`. -/
def workingCats (c : Context) (x : Nat) (b : Building) : Nat :=
  ((residentsOn c x b).filter fun r => r.traits.day == .works).length

/-! ## Facts about the transit, for a set of transit choices -/

/-- The cost of the routes, the station and the bridges, as `costOf` counts it. -/
def transitCost (T : Transit) : Nat :=
  (T.on.filter id).length * (routeBuildCost + routeYearlyCost * years)
    + (if T.station.isSome then stationBuildCost + stationYearlyCost * years else 0)
    + (T.bridges.filter id).length * bridgeCost

/-- The cost of the buildings, as `costOf` counts it. -/
def buildCost (p : Puzzle) (build : List Building) : Nat :=
  (List.range p.blockCount).foldl (fun t i =>
    if (p.fixedAt i).isSome then t else t + (build.getD i .empty).cost) 0

/-- The smallest value of `f` on a list (0 for an empty list). -/
def leastOf {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | a :: rest => rest.foldl (fun m x => min m (f x)) (f a)

/-- What we know about each block's transit facts, when the transit is one of a
set of choices. With a single choice, every fact is exact. -/
structure Lines where
  /-- Blocks that could be neighbors of each block, each with whether it surely
  is. -/
  neighbors : Array (List (Nat × Bool))
  /-- Blocks whose workers could reach each block. -/
  workerSources : Array (List Nat)
  /-- The block has the "transit" factor. -/
  transitNear : Array Maybe
  /-- The metro station is on the block or next to it. -/
  stationNear : Array Maybe
  /-- The block is in metro reach. -/
  reaches : Array Maybe
  /-- The least the transit can cost. -/
  leastCost : Nat
deriving Inhabited

/-- What we know when the transit is one of `Ts`. -/
def Lines.make (c : Context) (Ts : List Transit) : Lines where
  neighbors := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    (c.blocks.filter fun j => Ts.any (·.isNeighbor c k j)).map fun j => (j, Ts.all (·.isNeighbor c k j))
  workerSources := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    c.blocks.filter fun h => Ts.any (·.canReach c k h)
  transitNear := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    ⟨Ts.any fun T => T.served c k || T.nearStation c k, Ts.all fun T => T.served c k || T.nearStation c k⟩
  stationNear := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    ⟨Ts.any (·.nearStation c k), Ts.all (·.nearStation c k)⟩
  reaches := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    ⟨Ts.any (·.stationReaches c k), Ts.all (·.stationReaches c k)⟩
  leastCost := leastOf transitCost Ts

/-! ## Mixes of neighbors -/

/-- What a building on block `x` offers its neighbors, as 9 yes/no bits:
park, bar, shop, loud, housing, office, food, cars surely, cars maybe. -/
def profile (c : Context) (x : Nat) (b : Building) : Nat :=
  (if b.isPark then 1 else 0) + (if b.isBar then 2 else 0) + (if b.isShop then 4 else 0)
    + (if b.isLoud then 8 else 0) + (if b.isHousing then 16 else 0) + (if b.isOffice then 32 else 0)
    + (if b.isFood then 64 else 0) + (if carsMust c x b then 128 else 0)
    + (if carsCould c x b then 256 else 0)

/-- What a block's own building adds to the mix: only its cars (bits 7 and 8),
since a block's own cars make traffic on it too. -/
def ownCars (c : Context) (x : Nat) (b : Building) : Nat :=
  (if carsMust c x b then 128 else 0) + (if carsCould c x b then 256 else 0)

/-- Note mix `x` (once): mark it in the table and add it to the list. -/
def markMix (acc : Array Bool × List Nat) (x : Nat) : Array Bool × List Nat :=
  match acc with
  | (marks, l) => if marks.getD x false then (marks, l) else (marks.set! x true, x :: l)

/-- Add one neighbor to a list of possible mixes: the new mixes are each old
mix OR'ed with each of the neighbor's profiles. A table of 512 marks keeps
each mix once. -/
def addNeighbor (mixes : List Nat) (profiles : List Nat) : List Nat :=
  (mixes.foldl (fun acc m => profiles.foldl (fun acc q => markMix acc (m ||| q)) acc)
    (Array.replicate 512 false, [])).2

/-- What a block that could be a neighbor may offer: the profile (`prof`) of
each of its options, or nothing (0) if it might not be a neighbor. -/
def offers (prof : Nat → Building → Nat) (opts : Nat → List Building) (x : Nat × Bool) : List Nat :=
  (opts x.1).map (prof x.1) ++ (if x.2 then [] else [0])

/-- Every mix the block `k` itself (its cars, `own`) and the blocks in `nbrs`
can offer together, when block `j` holds one of `opts j`. `nbrs` lists the
blocks that could be neighbors, each with whether it surely is. -/
def neighborMixes (prof own : Nat → Building → Nat) (k : Nat) (nbrs : List (Nat × Bool))
    (opts : Nat → List Building) : List Nat :=
  nbrs.foldl (fun mixes x => addNeighbor mixes (offers prof opts x)) ((opts k).map (own k))

/-! ## Tables worked out once per puzzle

Only for speed: the search reads these instead of looking at each block's
cats again. `Tables.read` falls back to working the value out. -/

/-- The mood-table number of cat `i` of block `x`: its resident type, or
`typeCount` if that is out of range. -/
def catSlot (c : Context) (x i : Nat) : Nat := min (c.traitsAt x i).kind c.typeCount

/-- Tables of what each block's cats give, for each building. -/
structure Tables where
  /-- `profile c x b` at `[x][b.code]`. -/
  profiles : Array (Array Nat)
  /-- `ownCars c x b` at `[x][b.code]`. -/
  own : Array (Array Nat)
  /-- `workingCats c x b` at `[x][b.code]`. -/
  working : Array (Array Nat)
  /-- `catSlot c x i` at `[x][i]`. -/
  slots : Array (Array Nat)
deriving Inhabited

/-- A table of `f x b` for every block `x` and building `b`, at `[x][b.code]`. -/
def buildingTable (c : Context) (f : Nat → Building → Nat) : Array (Array Nat) :=
  Array.ofFn (n := c.puzzle.blockCount) fun x => Array.ofFn (n := 19) fun i => f x.val (Building.ofCode i.val)

def makeTables (c : Context) : Tables where
  profiles := buildingTable c (profile c)
  own := buildingTable c (ownCars c)
  working := buildingTable c (workingCats c)
  slots := Array.ofFn (n := c.puzzle.blockCount) fun x =>
    Array.ofFn (n := maxCatsPerBlock) fun i => catSlot c x.val i.val

/-- Entry `[x][b.code]` of a table, or `f x b` if the table has no such entry. -/
def readTable (t : Array (Array Nat)) (f : Nat → Building → Nat) (x : Nat) (b : Building) : Nat :=
  if h : x < t.size then
    if h2 : b.code < t[x].size then t[x][b.code] else f x b
  else f x b

/-- Entry `[x][i]` of the slots table, or `catSlot c x i` if it has no such entry. -/
def readSlot (t : Array (Array Nat)) (c : Context) (x i : Nat) : Nat :=
  if h : x < t.size then
    if h2 : i < t[x].size then t[x][i] else catSlot c x i
  else catSlot c x i

/-! ## Happiness: one case per factor -/

/-- What we know about factor `f`, given:
- `m`: the mix of what the neighbors offer (bits as in `profile`),
- `tn`: what we know about the "transit" factor,
- `sn`: what we know about "the metro station is on or next to the block".

One case per factor, following `factorsHad`. -/
def factorMaybe (m : Nat) (tn sn : Maybe) : Factor → Maybe :=
  let bit (i : Nat) : Maybe := .exact (m.testBit i)
  let traffic : Maybe := ⟨m.testBit 8, m.testBit 7⟩
  fun
  | .parks => bit 0
  | .nightlife => bit 1
  | .quiet => (((bit 3).or traffic).or sn).not
  | .transit => tn
  | .shops => bit 2
  | .variety => .atLeast 3 [bit 4, bit 5, bit 2, bit 0, bit 1, bit 6]
  | .food => bit 6
  | .cleanAir => traffic.not.or (bit 0)

/-- The most a factor with feeling value `v` can add: a good factor counts if
it could happen, a bad one only if it must. -/
def factorBest (v : Int) (r : Maybe) : Int :=
  if v > 0 then (if r.could then v else 0) else (if r.must then v else 0)

/-- The most happiness per person residents with personality `t` can have,
given what we know about each factor. -/
def bestEach (t : Personality) (fm : Factor → Maybe) : Int :=
  Factor.all.foldl (fun s f => s + factorBest (t.feeling f).value (fm f)) 0

/-- Best happiness per person of personality `p`, for every neighbor mix `m`,
code `t` of "transit" and code `s` of "station next door", at entry
`16 m + 4 t + s`. Worked out once per puzzle. -/
def moodTable (p : Personality) : Array Int :=
  Array.ofFn (n := 8192) fun e =>
    bestEach p (factorMaybe (e.val / 16) (Maybe.ofCode (e.val / 4 % 4)) (Maybe.ofCode (e.val % 4)))

/-! ## The cap of one block -/

/-- What a block's cap needs to know about its surroundings; none of it depends
on the building on the block itself. -/
structure BlockInfo where
  /-- The block. -/
  block : Nat
  /-- For each neighbor mix that can happen, each resident type's best
  happiness per person. Empty if no option of the block has residents. -/
  eaches : List (Array Int)
  /-- The most workers (and customers) who can reach the block. -/
  workers : Nat
  /-- How many neighbors could be offices. -/
  offices : Nat
  /-- A neighbor could be a café or restaurant. -/
  food : Bool
  /-- The block could be in metro reach. -/
  reached : Bool

/-- Happiness minus crime for `people` residents with happiness `each` per
person. It never goes down when `each` goes up. -/
def moodValue (people : Nat) (each : Int) : Int :=
  (people : Int) * each - (unhappyCost * (unhappyLine - each).toNat * people : Nat)

/-- Happiness minus crime of the cats of a block with building `b`, when cat
`i` has mood-table number `slot i` and table number `j` has happiness
`eaches[j]` per person. -/
def moodWith (slot : Nat → Nat) (b : Building) (eaches : Array Int) : Int :=
  (List.range b.cats).foldl (fun t i => t + moodValue residentsPerCat (eaches.getD (slot i) 0)) 0

/-- The largest value of `F` on a list (0 for an empty list). -/
def maxOver {α : Type} (F : α → Int) : List α → Int
  | [] => 0
  | e :: es => es.foldl (fun m e => max m (F e)) (F e)

/-- The most happiness minus crime on a block with building `b`: the best
over the neighbor mixes that can happen. -/
def bestMood (c : Context) (t : Tables) (info : BlockInfo) (b : Building) : Int :=
  if b.cats = 0 then 0 else maxOver (moodWith (readSlot t.slots c info.block) b) info.eaches

/-- The biggest office bonus, in percent, the neighbors could give. -/
def bonusCap (info : BlockInfo) (b : Building) : Nat :=
  if b.isOffice then
    min officeBonusMax (officeBonusPerOffice * info.offices) + (if info.food then lunchBonus else 0)
  else 0

/-- The most productivity of building `b`: every job filled that the most local
workers, plus downtown workers if the metro could reach it, could fill, with
the biggest office bonus the neighbors could give. -/
def jobsCap (info : BlockInfo) (b : Building) : Nat :=
  let filled := min b.jobs (info.workers + if info.reached then stationWorkersPerBlock else 0)
  jobWorth * filled * (100 + bonusCap info b) / 100

/-- The most points from downtown jobs of the cats of a block with building
`b`: every working cat, at the metro rate if the metro could reach the block,
else at the car rate. -/
def downtownCap (c : Context) (t : Tables) (info : BlockInfo) (b : Building) : Nat :=
  residentsPerCat * readTable t.working (workingCats c) info.block b
    * (if info.reached then metroJobWorth else carJobWorth)

/-- The most sales of building `b`: every customer who could come, served. -/
def salesCap (info : BlockInfo) (b : Building) : Nat :=
  match b with
  | .shop h => saleWorth * min (customersPerShopStory * h.stories)
      (info.workers + if info.reached then shoppersPerShopStory * h.stories else 0)
  | _ => 0

/-- The most block `info.block` can be worth with building `b` on it. -/
def valueCap (c : Context) (t : Tables) (info : BlockInfo) (b : Building) : Int :=
  bestMood c t info b + jobsCap info b + downtownCap c t info b + salesCap info b

/-! ## The bound for a search node -/

/-- Everything the search needs for a set of transit choices, computed once. -/
structure Plan where
  c : Context
  /-- The transit choices this plan covers. -/
  group : List Transit
  L : Lines
  /-- `moodTable` for each resident type. -/
  moods : Array (Array Int)
  tables : Tables
deriving Inhabited

/-- The mood tables of a puzzle's resident types, plus one more (number
`typeCount`) for a cat whose type number is out of range. -/
def moodTables (c : Context) : Array (Array Int) :=
  Array.ofFn (n := c.typeCount + 1) fun k => moodTable (c.residentType k.val).personality

/-- Set up the search for the transit choices `Ts`, given the mood tables and
the cat tables. -/
def makePlan (c : Context) (moods : Array (Array Int)) (tables : Tables) (Ts : List Transit) : Plan :=
  { c, group := Ts, L := Lines.make c Ts, moods, tables }

/-- Work out the `BlockInfo` for block `k`, when block `j` holds one of
`opts j` and `spot j` says what we know about it. -/
def Plan.blockInfo (P : Plan) (spot : Nat → Spot) (opts : Nat → List Building) (k : Nat) :
    BlockInfo :=
  let c := P.c
  let L := P.L
  let near := 4 * (L.transitNear.getD k (.exact false)).code + (L.stationNear.getD k (.exact false)).code
  let nbrs := L.neighbors.getD k []
  { block := k
    eaches := if (opts k).any (·.cats > 0) then
        (neighborMixes (readTable P.tables.profiles (profile c)) (readTable P.tables.own (ownCars c))
          k nbrs opts).map fun m => Array.ofFn (n := c.typeCount + 1) fun ti =>
          (P.moods.getD ti.val #[]).getD (16 * m + near) 0
      else []
    workers := (L.workerSources.getD k []).foldl (fun t h => t + (spot h).residents) 0
    offices := (nbrs.filter fun x => (spot x.1).office.could).length
    food := nbrs.any fun x => (spot x.1).food.could
    reached := (L.reaches.getD k (.exact false)).could }

/-- The cost of building `b` on block `k`, as `costOf` counts it (fixed blocks
are already paid for). -/
def buildCostAt (p : Puzzle) (k : Nat) (b : Building) : Nat :=
  if (p.fixedAt k).isSome then 0 else b.cost

/-- The options of block `j` at a search node (empty past the last block). -/
def optsAt (opts : List (List Building)) (j : Nat) : List Building := opts.getD j [.empty]

/-- What we know about each block at a search node, worked out once. -/
def spotTable (c : Context) (opts : List (List Building)) : Array Spot :=
  Array.ofFn (n := c.puzzle.blockCount) fun j => Spot.of (optsAt opts j.val)

/-- What we know about block `j`, read from the table. -/
def spotAt (tbl : Array Spot) (opts : List (List Building)) (j : Nat) : Spot :=
  if h : j < tbl.size then tbl[j] else Spot.of (optsAt opts j)

/-- The most points one worker can make: `jobWorth` with the biggest office
bonus (`officeBonusMax + lunchBonus` = 60%). A downtown job is worth less. -/
def workerPrice : Nat := 8

/-- The points of a worker counted at home in `valueCapW`; the rest are
counted at the office. -/
def workerShare : Nat := 4

/-- The most productivity of building `b` from downtown workers alone. -/
def jobsCapW (info : BlockInfo) (b : Building) : Nat :=
  jobWorth * (if info.reached then min b.jobs stationWorkersPerBlock else 0) * (100 + bonusCap info b) / 100

/-- **A second cap, that counts each worker once.** A cat works in one place
only: an office in town, or downtown. So instead of counting jobs at the
offices and downtown jobs at home, count `workerPrice` points for each
resident of a working cat, at home, and at the offices only the downtown
workers. -/
def valueCapW (c : Context) (t : Tables) (info : BlockInfo) (b : Building) : Int :=
  valueCap c t info b

/-- Caps and costs for each option of each block: the first list with
`valueCap`, the second with `valueCapW`. -/
abbrev Caps := List (List (Int × Nat)) × List (List (Int × Nat))

/-- Both caps and the cost of building `b` on block `k`. -/
def Plan.capRow (P : Plan) (spot : Nat → Spot) (opts : Nat → List Building) (k : Nat) (b : Building) :
    Int × Int × Nat :=
  let info := P.blockInfo spot opts k
  (valueCap P.c P.tables info b, valueCapW P.c P.tables info b, buildCostAt P.c.puzzle k b)

/-- For each block, each option's caps and cost, when block `j` holds one of
`opts j`. -/
def Plan.optionValues (P : Plan) (opts : List (List Building)) : Caps :=
  let spot := spotAt (spotTable P.c opts) opts
  let rows := P.c.blocks.map fun k =>
    let info := P.blockInfo spot (optsAt opts) k
    (optsAt opts k).map fun b =>
      (valueCap P.c P.tables info b, valueCapW P.c P.tables info b, buildCostAt P.c.puzzle k b)
  (rows.map (·.map fun x => (x.1, x.2.2)), rows.map (·.map fun x => (x.2.1, x.2.2)))

/-! ## Adding up the caps within the budget -/

/-- Rates tried for the budget trade-off, in quarter points per thousand
dollars. Any rates work; they only affect how tight the bound is. -/
def rates : List Nat := [1, 2, 3, 4, 5, 6, 8, 12, 16]

/-- For one block, given (cap, cost) for each option: the best
`4 × cap − rate × cost`. -/
def bestTrade (rate : Nat) : List (Int × Nat) → Int
  | [] => 0
  | (v, c) :: rest => rest.foldl (fun m x => max m (4 * x.1 - (rate * x.2 : Nat)))
      (4 * v - (rate * c : Nat))

/-- For any rate: 4 × total ≤ Σ best (4 × cap − rate × cost) + rate × budget.
(Rate 0 gives the plain sum of caps.) -/
def tradeBound (vals : List (List (Int × Nat))) (left : Nat) (rate : Nat) : Int :=
  ((vals.map (bestTrade rate)).sum + (rate * left : Nat)) / 4

/-- The quick bound, from the blocks' (cap, cost) lists. -/
def Plan.boundOne (P : Plan) (vals : List (List (Int × Nat))) : Int :=
  let left := P.c.puzzle.budget - P.L.leastCost
  rates.foldl (fun m r => min m (tradeBound vals left r)) (tradeBound vals left 0)

/-- The quick bound from both kinds of caps: the smaller. -/
def Plan.boundFrom (P : Plan) (vals : Caps) : Int := min (P.boundOne vals.1) (P.boundOne vals.2)

/-- **Quick upper bound** on the score of every valid layout whose transit is
one of `P.group` and where block `j` holds one of `opts j`: the smallest
trade-off bound over the rates. -/
def Plan.bound (P : Plan) (opts : List (List Building)) : Int :=
  P.boundFrom (P.optionValues opts)

/-- Stands for "no way to stay within the budget". -/
def impossible : Int := -1000000000

/-- One row of the knapsack table: entry `r` is the best total cap of this
block and the ones after it (`next`) with `r` units of money. -/
def knapsackRow (units : Nat) (opts : List (Int × Nat)) (next : Array Int) : Array Int :=
  Array.ofFn (n := units + 1) fun r =>
    opts.foldl (fun m x =>
      if x.2 / 30 ≤ r.val then max m (x.1 + next.getD (r.val - x.2 / 30) impossible) else m)
      impossible

/-- Best total cap when each block picks one option and the costs (in units of
30, rounded down) add up to at most `units`: an exact knapsack over the
blocks' (cap, cost) lists. -/
def knapsack (vals : List (List (Int × Nat))) (units : Nat) : Int :=
  (vals.foldr (knapsackRow units) (Array.replicate (units + 1) 0)).getD units impossible

/-- The knapsack bound, from the blocks' (cap, cost) lists. -/
def Plan.knapsackFrom (P : Plan) (vals : Caps) : Int :=
  min (knapsack vals.1 ((P.c.puzzle.budget - P.L.leastCost) / 30))
    (knapsack vals.2 ((P.c.puzzle.budget - P.L.leastCost) / 30))

/-- **Upper bound** on the score of every valid layout whose transit is one of
`P.group` and where block `j` holds one of `opts j`: the most the caps can add
up to within the budget left after the cheapest transit. -/
def Plan.knapsackBound (P : Plan) (opts : List (List Building)) : Int :=
  P.knapsackFrom (P.optionValues opts)

/-- The least the buildings can cost, when block `j` holds one of `opts j`. -/
def leastBuildCost (p : Puzzle) (opts : List (List Building)) : Nat :=
  (List.range p.blockCount).foldl (fun t k => t + leastOf (buildCostAt p k) (opts.getD k [.empty])) 0

end SevenBridges
