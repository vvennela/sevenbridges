import SevenBridges.Bound

/-!
# The fast solver: branch and bound (DESIGN.md §8.4)

For each transit choice, fill blocks one at a time, in block order. Before
going deeper, compute an upper bound (`Plan.bound`, `SevenBridges/Bound.lean`)
on the score of every layout that starts this way. If that bound can't beat
the best layout found so far, skip the whole branch. Branches that already
cost more than the budget are skipped too.

The solver has a fuel budget: each step costs one unit, and it stops when the
fuel runs out. If it finishes with fuel left, its answer is the best
(`solve_is_best` in `SevenBridges/BranchProofs.lean`).
-/

namespace SevenBridges
open Numbers

/-- Search state: the best layout so far, its score, fuel left and steps taken. -/
structure Search where
  best : Solution
  bestScore : Int
  fuel : Nat
  steps : Nat

/-- Take one step: spend a unit of fuel. -/
def Search.spend (st : Search) : Search := { st with fuel := st.fuel - 1, steps := st.steps + 1 }

/-- Look at a finished layout: keep it if it is allowed (`keep`), valid, and
beats the best so far. -/
def Search.consider (c : Context) (keep : Solution → Bool) (st : Search) (s : Solution) : Search :=
  if keep s && decide (ValidWith c s) && decide (scoreWith c s > st.bestScore) then
    { st with best := s, bestScore := scoreWith c s }
  else st

/-- With every block decided (`build`), try each transit choice: `exacts` has
one plan per transit choice. -/
def tryTransits (exacts : List Plan) (keep : Solution → Bool) (build : List Building)
    (st : Search) : Search :=
  exacts.foldl (fun st P =>
    if st.fuel = 0 then st else
    let st := st.spend
    match P.group with
    | [T] =>
      if buildCost P.c.puzzle build + transitCost T > P.c.puzzle.budget then st
      else if P.bound (build.map ([·])) ≤ st.bestScore then st
      else st.consider P.c keep ⟨build, T.on, T.station, T.bridges⟩
    | _ => { st with fuel := 0 }) st

/-- The kind of a building: empty, park, bar, food, housing, office or shop. -/
def kindOf : Building → Nat
  | .empty => 0
  | .park => 1
  | .bar => 2
  | .food => 3
  | .housing _ => 4
  | .office _ => 5
  | .shop _ => 6

/-- Whether a building has 3 floors or more. -/
def loudKey (b : Building) : Nat := if b.stories ≥ 3 then 1 else 0

/-- How one search step splits a block's options. -/
inductive Split
  /-- One part per value of `key` below `count`, plus one for the rest. -/
  | byKey (key : Building → Nat) (count : Nat)
  /-- One part per building. -/
  | single

/-- The parts a step splits a block's options into. Every option is in a part. -/
def Split.apply : Split → List Building → List (List Building)
  | .byKey key count, l => ((List.range count).map fun K => l.filter (key · == K))
      ++ [l.filter (count ≤ key ·)] |>.filter (· ≠ [])
  | .single, l => l.map ([·])

/-- One step of the search. -/
inductive Step
  /-- Split block `k`'s options. -/
  | block (k : Nat) (sp : Split)
  /-- Pick the transit choice from the plan's group. -/
  | transit

/-- Visit one search node (plan `P`, options `opts`, caps and costs `vals`): take
a step, then skip the node if its cheapest layout is over budget or its bound
can't beat the best so far; otherwise search below it with `go`. -/
def Search.tryNode (P : Plan) (opts : List (List Building)) (vals : Caps)
    (go : Search → Search) (st : Search) : Search :=
  if st.fuel = 0 then st else
  let st := st.spend
  if leastBuildCost P.c.puzzle opts + P.L.leastCost > P.c.puzzle.budget then st
  else if P.boundFrom vals ≤ st.bestScore then st
  else if P.knapsackFrom vals ≤ st.bestScore then st
  else go st

/-- Search every layout with transit in `P.group` where block `j` holds one of
`opts j`; `exacts` has one plan for each transit choice of the group. Each
step splits one block's options, or picks the transit. After the last step
every block must hold a single option (if not, the search gives up by setting
the fuel to 0). Parts are tried best bound first. -/
def branch (keep : Solution → Bool) :
    List Step → Plan → List Plan → List (List Building) → Search → Search
  | [], _, exacts, opts, st =>
    if opts.all (·.length == 1) then tryTransits exacts keep (opts.map (·.headD .empty)) st
    else { st with fuel := 0 }
  | .block k sp :: steps, P, exacts, opts, st =>
    let parts := ((sp.apply (optsAt opts k)).map fun part =>
      let opts' := opts.set k part
      let vals := P.optionValues opts'
      (opts', vals, P.boundFrom vals)).mergeSort (fun x y => x.2.2 ≥ y.2.2)
    parts.foldl (fun st x => st.tryNode P x.1 x.2.1 (branch keep steps P exacts x.1)) st
  | .transit :: steps, P, exacts, opts, st =>
    let parts := (exacts.map fun P' =>
      let vals := P'.optionValues opts
      (P', vals, P'.boundFrom vals)).mergeSort (fun x y => x.2.2 ≥ y.2.2)
    parts.foldl (fun st x => st.tryNode x.1 opts x.2.1 (branch keep steps x.1 [x.1] opts)) st

/-- Every route that is on has its bridges built. -/
def bridgesReadyFor (c : Context) (on bridges : List Bool) : Bool :=
  (List.range c.puzzle.routes.length).all fun r =>
    !on.getD r false || (⟨on, none, bridges⟩ : Transit).bridgesReady c r

/-- The transit choices, in groups that are searched together: one group per
set of routes and bridges, holding every station choice. Sets where a route is
on without its bridges are left out (they are never valid). -/
def transitGroups (c : Context) : List (List Transit) :=
  let p := c.puzzle
  (((allSwitches p.routes.length).flatMap fun on =>
      (allSwitches p.bridgeSites.length).map fun br => (on, br)).filter
    fun x => bridgesReadyFor c x.1 x.2).map fun x =>
    (none :: p.metroSites.map some).map fun station => ⟨x.1, station, x.2⟩

/-- The search steps: first the kind of every block, then the transit, then
whether each block has 3 floors or more, then the building on each block. -/
def searchSteps (p : Puzzle) : List Step :=
  let blocks := List.range p.blockCount
  blocks.map (Step.block · (.byKey (fun b => if b.isHousing then 1 else 0) 2))
    ++ blocks.map (Step.block · (.byKey kindOf 7)) ++ [.transit]
    ++ blocks.map (Step.block · (.byKey loudKey 2)) ++ blocks.map (Step.block · .single)

/-- A piece of the search: a plan (with one plan per transit choice in
`exacts`), the steps left, and each block's options. -/
structure Job where
  P : Plan
  exacts : List Plan
  steps : List Step
  opts : List (List Building)

/-- Run one piece of the search. -/
def Job.run (keep : Solution → Bool) (j : Job) (st : Search) : Search :=
  branch keep j.steps j.P j.exacts j.opts st

/-- Split a piece of the search at its first step, if that step splits a
block. -/
def Job.expand (j : Job) : List Job :=
  match j.steps with
  | .block k sp :: rest =>
    (sp.apply (optsAt j.opts k)).map fun part => { j with steps := rest, opts := j.opts.set k part }
  | _ => [j]

/-- The whole search: one piece per group of transit choices. -/
def rootJobs (p : Puzzle) : List Job :=
  let c := prepare p
  let moods := moodTables c
  let tables := makeTables c
  (transitGroups c).map fun Ts =>
    { P := makePlan c moods tables Ts, exacts := Ts.map (makePlan c moods tables [·]), steps := searchSteps p,
      opts := p.choices }

/-- Split every piece at its first step, `n` times over. -/
def expandTimes : Nat → List Job → List Job
  | 0, js => js
  | n + 1, js => expandTimes n (js.flatMap Job.expand)

/-- How many times the search is split into smaller pieces, so that the
pieces can be shared fairly between cores. -/
def splitDepth : Nat := 6

/-- The search, cut into pieces: one per group of transit choices, each split
at its first two steps, most promising first. -/
def jobs (p : Puzzle) : List Job :=
  let pieces := expandTimes splitDepth (rootJobs p)
  ((pieces.map fun j => (j, j.P.bound j.opts)).mergeSort (fun x y => x.2 ≥ y.2)).map (·.1)

/-- Run the pieces one after another. -/
def runInTurn (keep : Solution → Bool) (js : List Job) (start : Search) : Search :=
  js.foldl (fun st j =>
    if st.fuel = 0 then st else
    let st := st.spend
    if j.P.bound j.opts ≤ st.bestScore then st else j.run keep st) start

/-- The better of two search results (the first on a tie). -/
def Search.better (a b : Search) : Search := if b.bestScore > a.bestScore then b else a

/-- Hand `h` of `k` when dealing pieces like cards: the pieces whose number
is `h` modulo `k`. -/
def hand {α : Type} (k : Nat) (js : List α) (h : Nat) : List α :=
  ((js.zip (List.range js.length)).filter (·.2 % k == h)).map (·.1)

/-- Deal the pieces into `k` hands, like cards: piece number `i` goes to hand
`i % k`. -/
def deal {α : Type} (k : Nat) (js : List α) : List (List α) :=
  (List.range k).map (hand k js)

/-- Hands the parallel search deals the pieces into. -/
def hands : Nat := 12

/-- Run hands of pieces at the same time, each hand one piece after another,
with an equal share of the fuel and the same starting best. The fuel left is 0
if any hand ran out. -/
def combineHands (start : Search) (share : Nat) (results : List Search) : Search :=
  let _ := share
  let used := results.foldl (fun t r => t + r.steps) 0
  let best := results.foldl Search.better start
  { best := best.best, bestScore := best.bestScore, steps := start.steps + used
    fuel := if results.all (·.fuel > 0) then start.fuel - used else 0 }

/-! ### Fresh copies for the parallel search

Each core works on its own copy of the puzzle's buildings. Sharing them between
threads makes every core wait on the same memory. The copy equals the original
(`Puzzle.fresh_eq`); it only changes where the data lives. -/

/-- The puzzle itself; the extra argument makes each task make its own copy. -/
@[noinline] def Puzzle.withUnit (_ : Unit) (p : Puzzle) : Puzzle := p

/-- A copy of the puzzle with its own building values. -/
def Puzzle.fresh (u : Unit) (p : Puzzle) : Puzzle :=
  let p := p.withUnit u
  { p with allowed := p.allowed.map (fun b => Building.ofCode b.code)
           fixed := p.fixed.map (·.map fun b => Building.ofCode b.code) }

theorem Puzzle.fresh_eq (u : Unit) (p : Puzzle) : p.fresh u = p := by
  have h : (fun b => Building.ofCode b.code) = id := funext Building.ofCode_code
  simp [Puzzle.fresh, Puzzle.withUnit, h]

/-- Run all pieces of the search in `hands` hands at the same time, each on its
own core and its own copy of the puzzle, each hand one piece after another,
with an equal share of the fuel and the same starting best. The fuel left is 0
if any hand ran out. -/
def runTogether (keep : Solution → Bool) (p : Puzzle) (start : Search) : Search :=
  let share := start.fuel / hands
  let tasks := (List.range hands).map fun h => Task.spawn (prio := .dedicated) fun u =>
    runInTurn keep (hand hands (jobs (p.fresh u)) h) { start with fuel := share, steps := 0 }
  combineHands start share (tasks.map Task.get)

/-- The same as `runTogether`, one hand after another, for the proofs. -/
def runHands (keep : Solution → Bool) (hs : List (List Job)) (start : Search) : Search :=
  let share := start.fuel / hs.length
  let tasks := hs.map fun h => Task.spawn fun _ => runInTurn keep h { start with fuel := share, steps := 0 }
  let results := tasks.map Task.get
  let used := results.foldl (fun t r => t + r.steps) 0
  let best := results.foldl Search.better start
  { best := best.best, bestScore := best.bestScore, steps := start.steps + used
    fuel := if results.all (·.fuel > 0) then start.fuel - used else 0 }

/-- Steps for the first, quick pass that looks for a good starting layout. -/
def quickFuel : Nat := 50000

/-- Search everything, from state `start`: first one piece after another with
a little fuel (often enough to finish); if that runs out, all pieces again, in
`hands` hands at the same time, from the best layout found so far. -/
def searchAll (p : Puzzle) (keep : Solution → Bool) (start : Search) : Search :=
  let js := jobs p
  let quick := runInTurn keep js { start with fuel := min quickFuel start.fuel }
  if quick.fuel > 0 then { quick with fuel := start.fuel - (quick.steps - start.steps) }
  else runTogether keep p { quick with fuel := start.fuel - (quick.steps - start.steps) }

/-! ## A good first guess -/

/-- `t` if it is valid and scores more than `v`, else `s`. -/
def tryLayout (c : Context) (sv : Solution × Int) (t : Solution) : Solution × Int :=
  if decide (ValidWith c t) then
    let w := scoreWith c t
    if w > sv.2 then (t, w) else sv
  else sv

/-- One round of small changes: each block to each of its choices, each route
on or off, each station site. -/
def improveOnce (c : Context) (sv : Solution × Int) : Solution × Int :=
  let p := c.puzzle
  let sv := (List.range p.blockCount).foldl (fun sv i =>
    (p.choicesFor i).foldl (fun sv b =>
      tryLayout c sv { sv.1 with build := sv.1.build.set i b }) sv) sv
  let sv := (List.range p.routes.length).foldl (fun sv i =>
    tryLayout c sv { sv.1 with routesOn := sv.1.routesOn.set i !(sv.1.routesOn.getD i false) }) sv
  let sv := (List.range p.bridgeSites.length).foldl (fun sv i =>
    tryLayout c sv { sv.1 with bridges := sv.1.bridges.set i !(sv.1.bridges.getD i false) }) sv
  -- A route together with the bridges it needs.
  let sv := (List.range p.routes.length).foldl (fun sv i =>
    tryLayout c sv { sv.1 with routesOn := sv.1.routesOn.set i true,
                               bridges := (c.bridgesFor i).foldl (fun b k => b.set k true) sv.1.bridges }) sv
  (none :: p.metroSites.map some).foldl (fun sv k => tryLayout c sv { sv.1 with station := k }) sv

/-- Empty blocks from the last one back until the layout fits the budget. -/
def trimToBudget (p : Puzzle) (s : Solution) : Solution :=
  (List.range p.blockCount).reverse.foldl (fun s i =>
    if costOf p s ≤ p.budget || (p.fixedAt i).isSome then s
    else { s with build := s.build.set i .empty }) s

/-- Layouts to start the first guess from: the empty one, and each allowed
building on every open block (cut down to the budget). -/
def startingLayouts (p : Puzzle) : List Solution :=
  let e := emptyLayout p
  e :: (p.allowed.filter (· != .empty)).map fun b =>
    trimToBudget p { e with build := (List.range p.blockCount).map fun i => (p.fixedAt i).getD b }

/-- A quick first guess: from each starting layout, make the best small change,
a few rounds; keep the best result. Only a starting point for the search; it
doesn't need to be the best. -/
def firstGuess (c : Context) : Solution :=
  let start := emptyLayout c.puzzle
  let climb (s : Solution) : Solution × Int :=
    let sv := if decide (ValidWith c s) then (s, scoreWith c s) else (start, scoreWith c start)
    (List.range 4).foldl (fun sv _ => improveOnce c sv) sv
  ((startingLayouts c.puzzle).map climb).foldl (fun best sv => if sv.2 > best.2 then sv else best)
    (start, scoreWith c start) |>.1

/-- The starting state: the first guess if it is valid, else the empty layout. -/
def startSearch (p : Puzzle) (fuel : Nat) : Search :=
  let c := prepare p
  let g := firstGuess c
  let first := if decide (ValidWith c g) then g else emptyLayout p
  ⟨first, scoreWith c first, fuel, 0⟩

/-- Run the solver with `fuel` steps. -/
def solveWithFuel (p : Puzzle) (fuel : Nat) : Search :=
  searchAll p (fun _ => true) (startSearch p fuel)

/-- Fuel for one solve. -/
def searchFuel : Nat := 12000000

/-- **The solver**: the best valid layout, or `none` if it ran out of fuel. -/
def solve (p : Puzzle) : Option Solution :=
  let r := solveWithFuel p searchFuel
  if r.fuel > 0 then some r.best else none

end SevenBridges
