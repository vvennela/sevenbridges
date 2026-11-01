import SevenBridges.BranchProofs

/-!
# Puzzle generator (DESIGN.md §8.5)

The generator takes a map and bus routes (made by `tools/genmap.mjs`) and a
seed. It makes random puzzles on that map, solves each one, and keeps the first
one that is interesting and hard enough.

The generator is **not trusted**: the best solution of the puzzle it returns
is found by the solver, which `solve_is_best` proves right. What we do prove
about the generator is that its work is bounded (`generate_work_le`): it never
takes more than `generatorStepBudget` steps in total.
-/

namespace SevenBridges
namespace Generator

/-! ## Random numbers -/

/-- A seeded random number generator (64-bit linear congruential). -/
structure Rng where
  state : Nat
deriving Repr, Inhabited

def Rng.next (r : Rng) : Nat × Rng :=
  let s := (r.state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  (s / 2 ^ 33, ⟨s⟩)

/-- A random number from `0` to `n - 1` (0 if `n = 0`). -/
def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if n = 0 then 0 else v % n, r)

/-- A random item from a list. -/
def Rng.pick {α : Type} [Inhabited α] (r : Rng) (l : List α) : α × Rng :=
  let (i, r) := r.below l.length
  (l.getD i default, r)

/-- `k` different random items from a list (shuffle, then take `k`). -/
def Rng.choose {α : Type} (r : Rng) (l : List α) (k : Nat) : List α × Rng :=
  let (keyed, r) := l.foldl (fun (acc, r) x =>
    let (v, r) := r.next; (acc ++ [(v, x)], r)) ([], r)
  (((keyed.mergeSort (fun a b => a.1 ≤ b.1)).take k).map (·.2), r)

/-! ## Making a random puzzle -/

def groupNames : List String := ["Families", "Students", "Retirees", "Young professionals", "Artists"]

def shares : List (Nat × Nat) := [(50, 50), (60, 40), (70, 30)]

/-- The name of a personality that cares about (`true`) or hates (`false`)
factor `f`. -/
def typeName : Factor → Bool → String
  | .parks, true => "Nature lovers"
  | .parks, false => "Homebodies"
  | .nightlife, true => "Night owls"
  | .nightlife, false => "Early risers"
  | .quiet, true => "Light sleepers"
  | .quiet, false => "Buzz seekers"
  | .transit, true => "Car-free"
  | .transit, false => "Drivers"
  | .shops, true => "Shoppers"
  | .shops, false => "Minimalists"
  | .variety, true => "Mix lovers"
  | .variety, false => "Purists"

/-- A minority personality: the usual one with factor `f` flipped. A factor
the usual type cares about becomes hated, one it hates becomes cared about,
and one it doesn't mind becomes cared about if `care`, else hated. -/
def flipped (usual : Personality) (f : Factor) (care : Bool) (share : Nat) : Personality :=
  let care := if f ∈ usual.cares then false else if f ∈ usual.hates then true else care
  { name := typeName f care, share
    cares := usual.cares.filter (· != f) ++ (if care then [f] else [])
    hates := usual.hates.filter (· != f) ++ (if care then [] else [f]) }

/-- Shares of the minority types, in percent of the group. -/
def minorityShares : List (List Nat) := [[20], [30], [20, 10], [15, 15]]

/-- A random group: the usual type cares about two factors and maybe hates
one; one or two minority types each flip one factor. -/
def randomGroup (r : Rng) (name : String) (share : Nat) : Group × Rng :=
  let (cares, r) := r.choose Factor.all 2
  let rest := Factor.all.filter fun f => f ∉ cares
  let (hateCount, r) := r.below 2
  let (hates, r) := r.choose rest hateCount
  let (minor, r) := r.pick minorityShares
  let usual : Personality := { name, share := 100 - minor.sum, cares, hates }
  let (flips, r) := r.choose Factor.all minor.length
  let (others, r) := (minor.zip flips).foldl (fun (acc, r) (sh, f) =>
    let (v, r) := r.below 2
    (acc ++ [flipped usual f (v == 1) sh], r)) ([], r)
  ({ name, share, types := usual :: others }, r)

/-- Every height of a building kind. -/
def allHeights (kind : Height → Building) : List Building := [kind .one, kind .two, kind .three]

/-- The river segments of a map, by number. -/
def riverSegments (m : RoadMap) : List Nat :=
  (List.range m.segments.length).filter fun i => (m.segments.getD i default).terrain == .stream

/-- Bridge sites: every river segment some route drives along (so every route
can run), then random others up to `most` sites in all. Never more than 7. -/
def chooseBridgeSites (r : Rng) (m : RoadMap) (routes : List Route) (most : Nat) : List Nat × Rng :=
  let river := riverSegments m
  let used := river.filter fun i => routes.any fun rt => rt.sides.contains (m.segments.getD i default).side
  let (others, r) := r.choose (river.filter (· ∉ used)) (most - min most used.length)
  ((used ++ others).take 7 |>.mergeSort (· ≤ ·), r)

/-- Puzzle sizes. The size sets how much choice a puzzle offers, so that the
proven solver finishes in time (DESIGN.md §8.6). -/
inductive Size
  /-- 6 blocks or fewer: every height, up to 3 bridge sites. -/
  | easy
  /-- 7 blocks: every height, one of shops, bars and parks left out, up to 2
  bridge sites. -/
  | medium
  /-- 8 or 9 blocks: buildings up to 2 stories (shops 1), one of shops, bars
  and parks left out, 1 bridge site (more if routes cross the river). -/
  | hard
deriving Repr, DecidableEq

def Size.ofBlocks (n : Nat) : Size :=
  if n ≤ 6 then .easy else if n = 7 then .medium else .hard

/-- Most bridge sites a puzzle of this size offers. -/
def Size.bridgeSites : Size → Nat
  | .easy => 3
  | .medium => 2
  | .hard => 1

/-- The heights a puzzle of this size offers for a building kind. -/
def Size.heights (sz : Size) (kind : Height → Building) : List Building :=
  if sz = .hard then [kind .one, kind .two] else allHeights kind

/-- A random puzzle on a map (budget not set yet). The station may go on any
block. Each puzzle leaves out at most one of shops, bars and parks, for
variety. No block is already built. Bigger maps offer less choice (`Size`):
fewer bridge sites, and on the biggest maps lower buildings. -/
def randomPuzzle (r : Rng) (m : RoadMap) (routes : List Route) (name : String) :
    Puzzle × Rng :=
  let n := m.blockCount
  let sz := Size.ofBlocks n
  let extras : List (List Building) :=
    [if sz = .hard then [.shop .one] else allHeights .shop, [.bar], [.park]]
  -- 3 means "leave nothing out"; medium and hard puzzles always leave one out.
  let (drop, r) := r.below (if sz = .easy then 4 else 3)
  let kept := (List.range 3).filterMap fun i => if i = drop then none else extras[i]?
  let allowed := sz.heights .housing ++ sz.heights .office ++ kept.flatten
  let (names, r) := r.choose groupNames 2
  let (split, r) := r.pick shares
  let (g1, r) := randomGroup r (names.getD 0 "Families") split.1
  let (g2, r) := randomGroup r (names.getD 1 "Students") split.2
  let (bridgeSites, r) := chooseBridgeSites r m routes sz.bridgeSites
  ({ name, map := m, allowed, fixed := [], routes,
     stationSites := List.range n, bridgeSites, groups := [g1, g2],
     budget := 0 }, r)

/-- A random solution that fits the puzzle: the "planted" answer. -/
def randomSolution (r : Rng) (p : Puzzle) : Solution × Rng :=
  let (build, r) := p.choices.foldl (fun (acc, r) opts =>
    let (b, r) := r.pick opts; (acc ++ [b], r)) ([], r)
  let (routesOn, r) := p.routes.foldl (fun (acc, r) _ =>
    let (v, r) := r.below 2; (acc ++ [v == 1], r)) ([], r)
  let (k, r) := r.below (p.stationSites.length + 1)
  let (bridges, r) := p.bridgeSites.foldl (fun (acc, r) _ =>
    let (v, r) := r.below 2; (acc ++ [v == 1], r)) ([], r)
  ({ build, routesOn, station := if k = 0 then none else p.stationSites[k - 1]?, bridges }, r)

/-! ## Checks on a solved puzzle -/

/-- Greedy play: fill open blocks one at a time with whatever scores best right
then, then try each route and station site. Returns the layout and how many
layouts it scored. -/
def greedy (p : Puzzle) : Solution × Nat :=
  let c := prepare p
  let value (s : Solution) : Option Int :=
    if decide (ValidWith c s) then some (scoreWith c s) else none
  let better (s t : Solution) : Bool :=
    match value s, value t with
    | some a, some b => a > b
    | some _, none => true
    | _, _ => false
  let start : Solution :=
    { build := (List.range p.blockCount).map fun i => (p.fixedAt i).getD .empty
      routesOn := p.routes.map fun _ => false, station := none
      bridges := p.bridgeSites.map fun _ => false }
  let (s, steps) := (List.range p.blockCount).foldl (fun (s, steps) i =>
    (p.choicesFor i).foldl (fun (s, steps) b =>
      let t := { s with build := s.build.set i b }
      (if better t s then t else s, steps + 2)) (s, steps)) (start, 0)
  let (s, steps) := (List.range p.bridgeSites.length).foldl (fun (s, steps) i =>
    let t := { s with bridges := s.bridges.set i true }
    (if better t s then t else s, steps + 2)) (s, steps)
  -- Each route, with the bridges it needs.
  let (s, steps) := (List.range p.routes.length).foldl (fun (s, steps) i =>
    let t := { s with routesOn := s.routesOn.set i true,
                      bridges := (c.bridgesFor i).foldl (fun b k => b.set k true) s.bridges }
    (if better t s then t else s, steps + 2)) (s, steps)
  p.stationSites.foldl (fun (s, steps) k =>
    let t := { s with station := some k }
    (if better t s then t else s, steps + 2)) (s, steps)

/-- Upper bound on the layouts `greedy` scores. -/
def greedyCount (p : Puzzle) : Nat :=
  2 * ((p.choices.map List.length).foldl (· + ·) 0 + p.routes.length + p.bridgeSites.length
    + p.stationSites.length)

/-- The verdict on one solved puzzle. -/
structure Verdict where
  best : Solution
  bestScore : Int
  usesTransit : Bool
  greedyScore : Int
  hard : Bool
deriving Repr

/-- Solve a puzzle with `fuel` steps and judge it. Returns the verdict (`none`
if the solver ran out of steps) and the steps taken. -/
def judge (p : Puzzle) (fuel : Nat) : Option Verdict × Nat :=
  let r := solveWithFuel p fuel
  if r.fuel = 0 then (none, r.steps) else
  let best := r.best
  let bestScore := r.bestScore
  let usesTransit := best.routesOn.any id || best.station.isSome || best.bridges.any id
  let (g, _) := greedy p
  let greedyScore := score p g
  -- Greedy play must fall short of the best by at least 10%.
  let hard := bestScore > 0 && greedyScore * 10 < bestScore * 9
  (some { best, bestScore, usesTransit, greedyScore, hard }, r.steps)

theorem judge_steps_le (p : Puzzle) (fuel : Nat) : (judge p fuel).2 ≤ fuel := by
  have h1 := solveWithFuel_steps_fuel_le p fuel
  unfold judge
  simp only
  split <;> simp only <;> omega

/-- Keep a puzzle whose best layout uses transit, has homes, and beats greedy
play clearly.
(Ties for the best are allowed: on near-symmetric maps, mirror-image layouts
often tie, and the rating only compares scores.) -/
def Verdict.accepted (v : Verdict) : Bool := v.usesTransit && v.hard && v.best.build.any (·.isHousing)

/-! ## The generator, with a step budget -/

/-- Most steps one attempt may take. -/
def attemptFuel : Nat := 900000
/-- Most steps the whole generator may take. -/
def generatorStepBudget : Nat := 1800000
/-- Most attempts. -/
def maxAttempts : Nat := 40

/-- The result of generating. -/
structure Result where
  puzzle : Option Puzzle
  verdict : Option Verdict
  attempts : Nat
  /-- Steps taken (search steps plus layouts scored by greedy play), in total. -/
  work : Nat

/-- A random puzzle with its budget set from a random planted layout. -/
def attemptPuzzle (r : Rng) (m : RoadMap) (routes : List Route) (name : String) : Puzzle × Rng :=
  let (p, r) := randomPuzzle r m routes name
  let (planted, r) := randomSolution r p
  let (margin, r) := r.below 6
  ({ p with budget := costOf p planted + 10 * margin }, r)

/-- Try up to `fuel` more attempts, with `left` steps of work left. Each attempt
makes a puzzle with `attempt`. -/
def loop (attempt : Rng → Puzzle × Rng) :
    Nat → Rng → Nat → Nat → Nat → Result
  | 0, _, _, attempts, work => { puzzle := none, verdict := none, attempts, work }
  | fuel + 1, r, left, attempts, work =>
    let (p, r) := attempt r
    let g := greedyCount p
    if g + 1 > left then
      -- Not enough work left for another attempt: stop.
      { puzzle := none, verdict := none, attempts, work }
    else
      let res := judge p (min attemptFuel (left - g))
      let cost := res.2 + g
      match res.1 with
      | some v =>
        if v.accepted then
          { puzzle := some p, verdict := some v, attempts := attempts + 1, work := work + cost }
        else loop attempt fuel r (left - cost) (attempts + 1) (work + cost)
      | none => loop attempt fuel r (left - cost) (attempts + 1) (work + cost)

/-- Generate a puzzle on map `m` with bus routes `routes`, from a seed. -/
def generate (m : RoadMap) (routes : List Route) (name : String) (seed : Nat) : Result :=
  loop (attemptPuzzle · m routes name) maxAttempts ⟨seed⟩ generatorStepBudget 0 0

/-! ## The generator's work is bounded -/

theorem loop_work_le (attempt : Rng → Puzzle × Rng) :
    ∀ (fuel : Nat) (r : Rng) (left attempts work : Nat),
      (loop attempt fuel r left attempts work).work ≤ work + left := by
  intro fuel
  induction fuel with
  | zero => intro r left attempts work; simp [loop]
  | succ fuel ih =>
    intro r left attempts work
    simp only [loop]
    generalize attempt r = x
    obtain ⟨p, r'⟩ := x
    simp only
    by_cases hg : greedyCount p + 1 > left
    · simp [hg]
    · simp only [hg, if_false]
      have hu := judge_steps_le p (min attemptFuel (left - greedyCount p))
      cases hres : (judge p (min attemptFuel (left - greedyCount p))).1 with
      | none =>
        simp only
        refine Nat.le_trans (ih _ _ _ _) ?_; omega
      | some v =>
        simp only
        split
        · simp only; omega
        · refine Nat.le_trans (ih _ _ _ _) ?_; omega

/-- **The generator never takes more than `generatorStepBudget` steps.** -/
theorem generate_work_le (m : RoadMap) (routes : List Route) (name : String) (seed : Nat) :
    (generate m routes name seed).work ≤ generatorStepBudget := by
  have := loop_work_le (attemptPuzzle · m routes name) maxAttempts ⟨seed⟩ generatorStepBudget 0 0
  simpa [generate] using this

end Generator
end SevenBridges
