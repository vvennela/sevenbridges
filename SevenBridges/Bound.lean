import SevenBridges.Proofs

/-!
# An upper bound on the score of a partly decided layout (DESIGN.md §8.4)

The solver narrows down each block's options step by step. Before it goes
deeper, it needs a number that no finished layout can beat. This file
computes that number.

A search node says, for each block, which buildings it may still hold
(`opts j`), and which transit choices are still open (`Plan.group`).

Because the rules are local (`Rules/Score.lean`), each block can be bounded on
its own:

- **Neighbors.** Across the river, two blocks are neighbors only if the bridge
  between them is built. When that isn't settled yet, the block **could** be a
  neighbor, but need not be.
- **Happiness and crime.** The neighbors of a block can offer it only certain
  mixes of things (a park, a bar, a shop, something loud, homes, offices), one
  building each. For each mix that can happen, each factor is then known,
  except "transit". For that one we ask: **could** it be true, and **must** it be true? A
  good factor counts if it could happen; a bad one only if it must. The best
  mix counts. Crime counts only as far as even the best happiness is below
  the line.
- **Jobs and sales.** At most every job is filled (if the station could reach
  the block), or as many as the most workers who could live nearby. Offices
  get the biggest bonus their neighbors could give.
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

/-- A building is 3 stories tall or is a bar: it breaks "quiet". -/
def Building.isLoud (b : Building) : Bool := b.stories == 3 || b.isBar

/-- What we know about the building on one block. -/
structure Spot where
  park : Maybe
  bar : Maybe
  shop : Maybe
  loud : Maybe
  housing : Maybe
  office : Maybe
  /-- The most residents it could have. -/
  residents : Nat
deriving Repr, Inhabited

/-- What we know about a block that holds one of the buildings in `l`. -/
def Spot.of (l : List Building) : Spot where
  park := .ofTest l Building.isPark
  bar := .ofTest l Building.isBar
  shop := .ofTest l Building.isShop
  loud := .ofTest l Building.isLoud
  housing := .ofTest l Building.isHousing
  office := .ofTest l Building.isOffice
  residents := l.foldl (fun m b => max m b.residents) 0

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
  /-- The station's outside workers reach the block. -/
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
  reaches := Array.ofFn (n := c.puzzle.blockCount) fun k =>
    ⟨Ts.any (·.stationReaches c k), Ts.all (·.stationReaches c k)⟩
  leastCost := leastOf transitCost Ts

/-! ## Happiness: one case per factor -/

/-- What we know about factor `f`, given:
- `near sel`: what we know about "a neighbor has `sel`",
- `transitNear`: what we know about the "transit" factor.

One case per factor, following `factorsHad`. -/
def factorMaybe (near : (Spot → Maybe) → Maybe) (transitNear : Maybe) : Factor → Maybe
  | .parks => near (·.park)
  | .nightlife => near (·.bar)
  | .quiet => (near (·.loud)).not
  | .transit => transitNear
  | .shops => near (·.shop)
  | .variety => .atLeast 3
      [near (·.housing), near (·.office), near (·.shop), near (·.park), near (·.bar)]

/-- The most a factor with feeling value `v` can add: a good factor counts if
it could happen, a bad one only if it must. -/
def factorBest (v : Int) (r : Maybe) : Int :=
  if v > 0 then (if r.could then v else 0) else (if r.must then v else 0)

/-- The most happiness per person residents with personality `t` can have,
given what we know about each factor. -/
def bestEach (t : Personality) (fm : Factor → Maybe) : Int :=
  Factor.all.foldl (fun s f => s + factorBest (t.feeling f).value (fm f)) 0

/-! ## Mixes of neighbors -/

/-- What a building offers its neighbors, as 6 yes/no bits: park, bar, shop,
loud, housing, office. -/
def Building.profile (b : Building) : Nat :=
  (if b.isPark then 1 else 0) + (if b.isBar then 2 else 0) + (if b.isShop then 4 else 0)
    + (if b.isLoud then 8 else 0) + (if b.isHousing then 16 else 0) + (if b.isOffice then 32 else 0)

/-- What a set of neighbors offers, exactly, from the OR of their profiles. -/
def Spot.ofMask (m : Nat) : Spot where
  park := .exact (m.testBit 0)
  bar := .exact (m.testBit 1)
  shop := .exact (m.testBit 2)
  loud := .exact (m.testBit 3)
  housing := .exact (m.testBit 4)
  office := .exact (m.testBit 5)
  residents := 0

/-- Note mix `x` (once): mark it in the table and add it to the list. -/
def markMix (acc : Array Bool × List Nat) (x : Nat) : Array Bool × List Nat :=
  if acc.1.getD x false then acc else (acc.1.set! x true, x :: acc.2)

/-- Add one neighbor to a list of possible mixes: the new mixes are each old
mix OR'ed with each of the neighbor's profiles. A table of 64 marks keeps
each mix once. -/
def addNeighbor (mixes : List Nat) (profiles : List Nat) : List Nat :=
  (mixes.foldl (fun acc m => profiles.foldl (fun acc q => markMix acc (m ||| q)) acc)
    (Array.replicate 64 false, [])).2

/-- What a block that could be a neighbor may offer: the profile of each of its
options, or nothing (0) if it might not be a neighbor. -/
def offers (opts : Nat → List Building) (x : Nat × Bool) : List Nat :=
  (opts x.1).map Building.profile ++ (if x.2 then [] else [0])

/-- Every mix of profiles the blocks in `nbrs` can offer together, when block
`j` holds one of `opts j`. `nbrs` lists the blocks that could be neighbors,
each with whether it surely is. -/
def neighborMixes (nbrs : List (Nat × Bool)) (opts : Nat → List Building) : List Nat :=
  nbrs.foldl (fun mixes x => addNeighbor mixes (offers opts x)) [0]

/-- Best happiness per person of personality `p`, for every neighbor mix `m`
and code `t` of "transit", at entry `4 m + t`. Worked out once per puzzle. -/
def moodTable (p : Personality) : Array Int :=
  Array.ofFn (n := 256) fun e =>
    bestEach p (factorMaybe (fun sel => sel (Spot.ofMask (e.val / 4))) (Maybe.ofCode (e.val % 4)))

/-! ## The cap of one block -/

/-- What a block's cap needs to know about its surroundings; none of it depends
on the building on the block itself. -/
structure BlockInfo where
  /-- For each neighbor mix that can happen, each resident type's best
  happiness per person. Empty if no option of the block has residents. -/
  eaches : List (List Int)
  /-- The most workers (and customers) who can reach the block. -/
  workers : Nat
  /-- How many neighbors could be offices. -/
  offices : Nat
  /-- The station's outside workers could reach the block. -/
  reached : Bool

/-- Happiness minus crime for `people` residents of a group with happiness
`each` per person. It never goes down when `each` goes up. -/
def moodValue (people : Nat) (each : Int) : Int :=
  (people : Int) * each - (unhappyCost * (unhappyLine - each).toNat * people : Nat)

/-- Happiness minus crime of the residents of building `b`, when resident type
`k` has happiness `eaches[k]` per person. -/
def moodWith (c : Context) (b : Building) (eaches : List Int) : Int :=
  (List.range c.typeCount).foldl (fun t k =>
    t + moodValue (typeResidents b (c.residentType k)) (eaches.getD k 0)) 0

/-- The largest value of `F` on a list (0 for an empty list). -/
def maxOver {α : Type} (F : α → Int) : List α → Int
  | [] => 0
  | e :: es => es.foldl (fun m e => max m (F e)) (F e)

/-- The most happiness minus crime on a block with building `b`: the best
over the neighbor mixes that can happen. -/
def bestMood (c : Context) (info : BlockInfo) (b : Building) : Int :=
  if b.residents = 0 then 0 else maxOver (moodWith c b) info.eaches

/-- The most productivity of building `b`: every job a worker could fill
filled, with the biggest office bonus the neighbors could give. -/
def jobsCap (info : BlockInfo) (b : Building) : Nat :=
  let filled := if info.reached then b.jobs else min b.jobs info.workers
  let bonus := if b.isOffice then min officeBonusMax (officeBonusPerOffice * info.offices) else 0
  jobWorth * filled * (100 + bonus) / 100

/-- The most sales of building `b`: every customer who could come, served. -/
def salesCap (info : BlockInfo) (b : Building) : Nat :=
  match b with
  | .shop h => saleWorth * min (customersPerShopStory * h.stories) info.workers
  | _ => 0

/-- The most block `k` can be worth with building `b` on it. -/
def valueCap (c : Context) (info : BlockInfo) (b : Building) : Int :=
  bestMood c info b + jobsCap info b + salesCap info b

/-! ## The bound for a search node -/

/-- Everything the search needs for a set of transit choices, computed once. -/
structure Plan where
  c : Context
  /-- The transit choices this plan covers. -/
  group : List Transit
  L : Lines
  /-- `moodTable` for each resident type. -/
  moods : Array (Array Int)
deriving Inhabited

/-- The mood tables of a puzzle's resident types. -/
def moodTables (c : Context) : Array (Array Int) :=
  Array.ofFn (n := c.typeCount) fun k => moodTable (c.residentType k.val).personality

/-- Set up the search for the transit choices `Ts`, given the mood tables. -/
def makePlan (c : Context) (moods : Array (Array Int)) (Ts : List Transit) : Plan :=
  { c, group := Ts, L := Lines.make c Ts, moods }

/-- Work out the `BlockInfo` for block `k`, when block `j` holds one of
`opts j` and `spot j` says what we know about it. -/
def Plan.blockInfo (P : Plan) (spot : Nat → Spot) (opts : Nat → List Building) (k : Nat) :
    BlockInfo :=
  let c := P.c
  let L := P.L
  let near := (L.transitNear.getD k (.exact false)).code
  { eaches := if (opts k).any (·.residents > 0) then
        (neighborMixes (L.neighbors.getD k []) opts).map fun m => (List.range c.typeCount).map fun ti =>
          (P.moods.getD ti #[]).getD (4 * m + near) 0
      else []
    workers := (L.workerSources.getD k []).foldl (fun t h => t + (spot h).residents) 0
    offices := ((L.neighbors.getD k []).filter fun x => (spot x.1).office.could).length
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

/-- For each block, each option's cap and cost, when block `j` holds one of
`opts j`. -/
def Plan.optionValues (P : Plan) (opts : List (List Building)) : List (List (Int × Nat)) :=
  let c := P.c
  let spot := spotAt (spotTable c opts) opts
  c.blocks.map fun k =>
    let info := P.blockInfo spot (optsAt opts) k
    (optsAt opts k).map fun b => (valueCap c info b, buildCostAt c.puzzle k b)

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
def Plan.boundFrom (P : Plan) (vals : List (List (Int × Nat))) : Int :=
  let left := P.c.puzzle.budget - P.L.leastCost
  rates.foldl (fun m r => min m (tradeBound vals left r)) (tradeBound vals left 0)

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
      if x.2 / 10 ≤ r.val then max m (x.1 + next.getD (r.val - x.2 / 10) impossible) else m)
      impossible

/-- Best total cap when each block picks one option and the costs (in units of
10, rounded down) add up to at most `units`: an exact knapsack over the
blocks' (cap, cost) lists. -/
def knapsack (vals : List (List (Int × Nat))) (units : Nat) : Int :=
  (vals.foldr (knapsackRow units) (Array.replicate (units + 1) 0)).getD units impossible

/-- The knapsack bound, from the blocks' (cap, cost) lists. -/
def Plan.knapsackFrom (P : Plan) (vals : List (List (Int × Nat))) : Int :=
  knapsack vals ((P.c.puzzle.budget - P.L.leastCost) / 10)

/-- **Upper bound** on the score of every valid layout whose transit is one of
`P.group` and where block `j` holds one of `opts j`: the most the caps can add
up to within the budget left after the cheapest transit. -/
def Plan.knapsackBound (P : Plan) (opts : List (List Building)) : Int :=
  P.knapsackFrom (P.optionValues opts)

/-- The least the buildings can cost, when block `j` holds one of `opts j`. -/
def leastBuildCost (p : Puzzle) (opts : List (List Building)) : Nat :=
  (List.range p.blockCount).foldl (fun t k => t + leastOf (buildCostAt p k) (opts.getD k [.empty])) 0

/-! ## Can the station still get enough riders? -/

/-- The most daily station riders, for transit `T`, when block `j` holds one of
`opts j`: on each block the station reaches, the most jobs that local workers
can't fill (jobs minus the fewest workers), plus the most shoppers. -/
def stationRidersCap (c : Context) (T : Transit) (opts : List (List Building)) : Nat :=
  if T.station.isNone then 0 else
  c.blocks.foldl (fun t j =>
    if T.stationReaches c j then
      let fewestWorkers := (c.blocks.filter (T.canReach c j)).foldl
        (fun t h => t + leastOf Building.residents (opts.getD h [.empty])) 0
      t + (opts.getD j [.empty]).foldl (fun m b => max m (b.jobs - fewestWorkers + shoppersAt b)) 0
    else t) 0

/-- The station rule might still pass: for a plan with a single transit choice
that builds the station, the station could still get enough riders. -/
def Plan.mayPass (P : Plan) (opts : List (List Building)) : Bool :=
  match P.group with
  | [T] => T.station.isNone || decide (stationRidersCap P.c T opts ≥ minStationRiders)
  | _ => true

end SevenBridges
