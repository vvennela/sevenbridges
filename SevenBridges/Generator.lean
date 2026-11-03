import SevenBridges.BranchProofs
import SevenBridges.Rules.Report

/-!
# Level generator (DESIGN.md §8.5, §15)

The generator takes a map and bus routes (made by `tools/genmap.mjs`) and a
seed. It makes random levels on that map, solves each one, and keeps the
first one that is interesting and hard enough.

The generator is **not trusted**: the best plan of the level it returns is
found by the solver, which `solve_is_best` proves right. What we do prove
about the generator is that its work is bounded (`generate_work_le`) and that
its levels have no starting blocks (`generate_no_fixed`).
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

/-! ## Resident groups -/

/-- The pool of resident groups: what the usual cat of each group cares about
and hates, and how the group's cats spend their day. Each level picks 2 or 3. -/
def groupPool : List Group :=
  [{ name := "Families", share := 0, types := [⟨"Families", 100, [.parks, .quiet, .cleanAir], [.nightlife]⟩]
     works := 55, studies := 25, drives := 45, buses := 30, eatsOut := 25, goesOut := 10 },
   { name := "Students", share := 0, types := [⟨"Students", 100, [.nightlife, .food, .transit], []⟩]
     works := 25, studies := 70, drives := 5, buses := 50, eatsOut := 70, goesOut := 70 },
   { name := "Professionals", share := 0, types := [⟨"Professionals", 100, [.transit, .food, .shops], [.parks]⟩]
     works := 90, studies := 5, drives := 35, buses := 35, eatsOut := 60, goesOut := 40 },
   { name := "Elderly", share := 0, types := [⟨"Elderly", 100, [.quiet, .parks, .cleanAir], [.nightlife]⟩]
     works := 10, studies := 0, drives := 20, buses := 45, eatsOut := 30, goesOut := 5 },
   { name := "Artists", share := 0, types := [⟨"Artists", 100, [.variety, .nightlife, .food], [.shops]⟩]
     works := 50, studies := 20, drives := 10, buses := 40, eatsOut := 50, goesOut := 60 },
   { name := "Urbanites", share := 0, types := [⟨"Urbanites", 100, [.transit, .variety, .shops], [.parks]⟩]
     works := 80, studies := 10, drives := 10, buses := 55, eatsOut := 70, goesOut := 50 },
   { name := "Rural newcomers", share := 0, types := [⟨"Rural newcomers", 100, [.parks, .quiet], [.transit]⟩]
     works := 65, studies := 5, drives := 70, buses := 10, eatsOut := 20, goesOut := 20 }]

/-- How the town's cats split between 2 or 3 groups, in percent. -/
def shares2 : List (Nat × Nat) := [(50, 50), (60, 40), (70, 30)]
def shares3 : List (Nat × Nat × Nat) := [(40, 30, 30), (50, 30, 20), (34, 33, 33)]

/-- The name of a personality that cares about (`true`) or hates (`false`)
factor `f`. -/
def typeName : Factor → Bool → String
  | .parks, true => "Nature lovers"
  | .parks, false => "Homebodies"
  | .nightlife, true => "Night owls"
  | .nightlife, false => "Early risers"
  | .quiet, true => "Light sleepers"
  | .quiet, false => "Buzz seekers"
  | .transit, true => "Transit fans"
  | .transit, false => "Car lovers"
  | .shops, true => "Shoppers"
  | .shops, false => "Minimalists"
  | .variety, true => "Mix lovers"
  | .variety, false => "Purists"
  | .food, true => "Foodies"
  | .food, false => "Home cooks"
  | .cleanAir, true => "Fresh-air fans"
  | .cleanAir, false => "City dwellers"

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

/-- A group from the pool with its share, and one or two minority
personalities that each flip one factor. -/
def randomGroup (r : Rng) (base : Group) (share : Nat) : Group × Rng :=
  let usual0 := base.types.headD default
  let (minor, r) := r.pick minorityShares
  let usual : Personality := { usual0 with share := 100 - minor.sum }
  let (flips, r) := r.choose Factor.all minor.length
  let (others, r) := (minor.zip flips).foldl (fun (acc, r) (sh, f) =>
    let (v, r) := r.below 2
    (acc ++ [flipped usual f (v == 1) sh], r)) ([], r)
  ({ base with share, types := usual :: others }, r)

/-- 2 or 3 random groups from the pool. -/
def randomGroups (r : Rng) (count : Nat) : List Group × Rng :=
  let (bases, r) := r.choose groupPool count
  let (sh, r) : List Nat × Rng :=
    if count ≤ 2 then let (s, r) := r.pick shares2; ([s.1, s.2], r)
    else let (s, r) := r.pick shares3; ([s.1, s.2.1, s.2.2], r)
  (bases.zip sh).foldl (fun (acc, r) (g, s) =>
    let (g, r) := randomGroup r g s; (acc ++ [g], r)) ([], r)

/-! ## The metro line -/

/-- The center of the map: the average of its intersections. -/
def mapCenter (m : RoadMap) : Point :=
  let n : Int := max 1 m.points.length
  ⟨(m.points.foldl (· + ·.x) 0) / n, (m.points.foldl (· + ·.y) 0) / n⟩

/-- Squared distance between two points. -/
def dist2 (p q : Point) : Nat := (p.x - q.x).natAbs ^ 2 + (p.y - q.y).natAbs ^ 2

/-- Blocks on the edge of town: they have a side no other block shares. -/
def edgeBlocks (m : RoadMap) : List Nat :=
  (List.range m.blockCount).filter fun i =>
    (m.block i).sides.any fun side => (m.blocks.filter fun b => b.sides.contains side).length == 1

/-- The metro line: it enters at an edge block and runs `len` blocks toward the
middle of town, each next block the touching one closest to the middle.
Also returns where it enters (the edge block's corner farthest from the
middle). -/
def metroLine (r : Rng) (m : RoadMap) (len : Nat) : (List Nat × Point) × Rng :=
  let mid := mapCenter m
  let (start, r) := r.pick (edgeBlocks m)
  let step (line : List Nat) : List Nat :=
    let last := line.getLastD start
    let next := (List.range m.blockCount).filter fun j => decide (m.Touch last j) && !line.contains j
    match next.foldl (fun best j => match best with
      | none => some j
      | some b => if dist2 (m.center j) mid < dist2 (m.center b) mid then some j else some b) none with
    | some j => line ++ [j]
    | none => line
  let line := (List.range (len - 1)).foldl (fun l _ => step l) [start]
  let entry := (m.block start).corners.foldl (fun best i =>
    if dist2 (m.point i) mid > dist2 best mid then m.point i else best) mid
  ((line, entry), r)

/-! ## Making a random level -/

/-- Level sizes. The size sets how much choice a level offers, so that the
proven solver finishes in time (DESIGN.md §8.6). -/
inductive Size
  /-- 5 blocks or fewer. -/
  | easy
  /-- 6 or 7 blocks. -/
  | medium
  /-- 8 or 9 blocks. -/
  | hard
deriving Repr, DecidableEq

def Size.ofBlocks (n : Nat) : Size :=
  if n ≤ 5 then .easy else if n ≤ 7 then .medium else .hard

/-- Most bridge sites a level of this size offers. -/
def Size.bridgeSites : Size → Nat
  | .easy => 2
  | .medium => 1
  | .hard => 1

/-- Blocks along the metro line. -/
def Size.metroLength : Size → Nat
  | .easy => 2
  | .medium => 2
  | .hard => 2

/-- Office heights a level offers. Every size offers 1–3 floors; small towns
also offer towers of 4 and 5 floors. -/
def Size.offices : Size → List Building
  | .easy => [.office .one, .office .two, .office .three, .office .four, .office .five]
  | _ => [.office .one, .office .two, .office .three]

/-- How many of food, shop, bar and park a level leaves out. -/
def Size.dropExtras : Size → Nat
  | .easy => 0
  | .medium => 1
  | .hard => 3

/-- Home heights: 1–3 floors on every size. -/
def Size.homes : Size → List Building
  | _ => [.housing .one, .housing .two, .housing .three]

/-- The river segments of a map, by number. -/
def riverSegments (m : RoadMap) : List Nat :=
  (List.range m.segments.length).filter fun i => (m.segments.getD i default).terrain == .stream

/-- Bridge sites: every river crossing (up to 7). Where to bridge is the
player's decision; the generator doesn't pre-pick. -/
def chooseBridgeSites (r : Rng) (m : RoadMap) (_routes : List Route) (_most : Nat) : List Nat × Rng :=
  ((riverSegments m).take 7 |>.mergeSort (· ≤ ·), r)

/-- A random level on a map (budget not set yet): random groups, allowed
buildings, bridge sites, metro line and simulation seed. No block is
already built. -/
def randomPuzzle (r : Rng) (m : RoadMap) (routes : List Route) (name : String) :
    Puzzle × Rng :=
  let sz := Size.ofBlocks m.blockCount
  -- Homes, offices and shops come in every height their size offers.
  let extras : List (List Building) :=
    [[.food], [.shop .one, .shop .two, .shop .three], [.bar], [.park]]
  let (kept, r) := r.choose extras (4 - sz.dropExtras)
  let allowed := sz.homes ++ sz.offices ++ kept.flatten
  let (count, r) := r.below 2
  let (groups, r) := randomGroups r (count + 2)
  let (bridgeSites, r) := chooseBridgeSites r m routes sz.bridgeSites
  let ((metroSites, metroEntry), r) := metroLine r m sz.metroLength
  let (simSeed, r) := r.below 1000000
  ({ name, map := m, allowed, fixed := [], routes, metroSites, metroEntry, bridgeSites, groups,
     budget := 0, simSeed }, r)

/-- A random layout that fits the puzzle. -/
def randomSolution (r : Rng) (p : Puzzle) : Solution × Rng :=
  let (build, r) := p.choices.foldl (fun (acc, r) opts =>
    let (b, r) := r.pick opts; (acc ++ [b], r)) ([], r)
  let (routesOn, r) := p.routes.foldl (fun (acc, r) _ =>
    let (v, r) := r.below 2; (acc ++ [v == 1], r)) ([], r)
  let (k, r) := r.below (p.metroSites.length + 1)
  let (bridges, r) := p.bridgeSites.foldl (fun (acc, r) _ =>
    let (v, r) := r.below 2; (acc ++ [v == 1], r)) ([], r)
  ({ build, routesOn, station := if k = 0 then none else p.metroSites[k - 1]?, bridges }, r)

/-- Random play: a random layout, cut down to the budget; if its transit
breaks a rule, no transit. -/
def randomPlay (c : Context) (r : Rng) (p : Puzzle) : Solution × Rng :=
  let (s, r) := randomSolution r p
  let s := trimToBudget p s
  let s := if decide (ValidWith c s) then s
    else trimToBudget p { s with routesOn := s.routesOn.map fun _ => false, station := none }
  (s, r)

/-! ## Checks on a solved level -/

/-- Random layouts tried when checking that random play does badly. -/
def randomTries : Nat := 800
/-- Most valid random layouts rated. -/
def randomRated : Nat := 500

/-- The rating at percent `q` of a sorted list of ratings. -/
def percentile (sorted : Array Nat) (q : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted.getD (min (sorted.size - 1) (sorted.size * q / 100)) 0

/-- Ratings of random valid layouts: up to `randomRated` of them, from at
most `randomTries` random layouts, sorted. -/
def randomRatings (p : Puzzle) (bestScore : Int) (seed : Nat) : Array Nat :=
  let c := prepare p
  let (ratings, _) := (List.range randomTries).foldl (fun (acc, r) _ =>
    if acc.size ≥ randomRated then (acc, r) else
    let (s, r) := randomPlay c r p
    if decide (ValidWith c s) then (acc.push (ratingWith c bestScore s), r) else (acc, r))
    ((#[] : Array Nat), (⟨seed⟩ : Rng))
  ratings.qsort (· < ·)

/-- The verdict on one solved level. -/
structure Verdict where
  best : Solution
  bestScore : Int
  emptyScore : Int
  /-- Median and 95th percentile rating of random valid layouts. -/
  median : Nat
  p95 : Nat
  rated : Nat
  /-- Happiness and productivity (with sales) of the best plan. -/
  happiness : Int
  productivity : Nat
deriving Repr

/-- Solve a level with `fuel` steps and judge it. Returns the verdict (`none`
if the solver ran out of steps) and the steps taken. -/
def judge (p : Puzzle) (fuel : Nat) : Option Verdict × Nat :=
  let r := solveWithFuel p fuel
  if r.fuel = 0 then (none, r.steps) else
  let sorted := randomRatings p r.bestScore (p.simSeed + 17)
  let rep := report p r.best
  (some { best := r.best, bestScore := r.bestScore, emptyScore := score p (emptyLayout p)
          median := percentile sorted 50, p95 := percentile sorted 95, rated := sorted.size
          happiness := rep.happiness, productivity := rep.productivity + rep.sales },
   r.steps)

theorem judge_steps_le (p : Puzzle) (fuel : Nat) : (judge p fuel).2 ≤ fuel := by
  have h1 := solveWithFuel_steps_fuel_le p fuel
  unfold judge
  simp only
  split <;> simp only <;> omega

/-- Keep a level whose best plan has homes and beats the empty town, gets
both happiness and productivity, and where random play does badly: the median random valid layout rates at most 50, and
95% of them rate at most 85. -/
def Verdict.accepted (v : Verdict) : Bool :=
  v.best.build.any (·.isHousing) && decide (v.bestScore > v.emptyScore)
    && decide (v.rated ≥ 20) && decide (v.median ≤ 50) && decide (v.p95 ≤ 85)
    -- Both numbers matter: happiness and productivity are each at least a
    -- tenth of the best plan's score.
    && decide (10 * v.happiness ≥ v.bestScore) && decide (10 * (v.productivity : Int) ≥ v.bestScore)

/-! ## The generator, with a step budget -/

/-- Most steps one attempt may take. -/
def attemptFuel : Nat := 1000000
/-- Most steps the whole generator may take. -/
def generatorStepBudget : Nat := 2500000
/-- Most attempts. -/
def maxAttempts : Nat := 40
/-- Work counted for checking one level besides the search: each random
layout tried counts as one step. -/
def checkCost : Nat := randomTries

/-- The result of generating. -/
structure Result where
  puzzle : Option Puzzle
  verdict : Option Verdict
  attempts : Nat
  /-- Steps taken (search steps plus random layouts tried), in total. -/
  work : Nat

/-- A random level with its budget set from a random layout. -/
def attemptPuzzle (r : Rng) (m : RoadMap) (routes : List Route) (name : String) : Puzzle × Rng :=
  let pr := randomPuzzle r m routes name
  let sr := randomSolution pr.2 pr.1
  let mr := sr.2.below 6
  -- No block is already built.
  ({ pr.1 with fixed := [], budget := costOf pr.1 sr.1 + 60 + 20 * mr.1 }, mr.2)

/-- Try up to `fuel` more attempts, with `left` steps of work left. Each attempt
makes a level with `attempt`. -/
def loop (attempt : Rng → Puzzle × Rng) :
    Nat → Rng → Nat → Nat → Nat → Result
  | 0, _, _, attempts, work => { puzzle := none, verdict := none, attempts, work }
  | fuel + 1, r, left, attempts, work =>
    let (p, r) := attempt r
    let g := checkCost
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

/-- Generate a level on map `m` with bus routes `routes`, from a seed. -/
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
    by_cases hg : checkCost + 1 > left
    · simp [hg]
    · simp only [hg, if_false]
      have hu := judge_steps_le p (min attemptFuel (left - checkCost))
      cases hres : (judge p (min attemptFuel (left - checkCost))).1 with
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

/-! ## Generated levels have no starting blocks -/

/-- Every level the loop returns was made by `attempt`. -/
theorem loop_puzzle_made (attempt : Rng → Puzzle × Rng) :
    ∀ (fuel : Nat) (r : Rng) (left attempts work : Nat) (q : Puzzle),
      (loop attempt fuel r left attempts work).puzzle = some q → ∃ r', (attempt r').1 = q := by
  intro fuel
  induction fuel with
  | zero => intro r left attempts work q h; simp [loop] at h
  | succ fuel ih =>
    intro r left attempts work q h
    simp only [loop] at h
    generalize hx : attempt r = x at h
    obtain ⟨p, r'⟩ := x
    simp only at h
    split at h
    · simp at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          exact ⟨r, by rw [hx]; exact h⟩
        · exact ih _ _ _ _ q h
      · exact ih _ _ _ _ q h

/-- **Generated levels have no starting blocks**: every block of a generated
level is open. -/
theorem generate_no_fixed (m : RoadMap) (routes : List Route) (name : String) (seed : Nat)
    (q : Puzzle) (h : (generate m routes name seed).puzzle = some q) : q.fixed = [] := by
  obtain ⟨r, hr⟩ := loop_puzzle_made _ _ _ _ _ _ q h
  rw [← hr]
  rfl

end Generator
end SevenBridges
