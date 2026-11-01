import SevenBridges.Rules.Valid

/-!
# The solver (DESIGN.md §8.4, step 1)

Plain search: try every solution that fits the puzzle, keep the valid ones, and
return the one with the highest score. If there are too many solutions to try,
return `none` instead.

The proof that this is right is in `SevenBridges/Proofs.lean`.
-/

namespace SevenBridges

/-- Every way to pick one item from each list, in order. -/
def allPicks {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap fun x => (allPicks rest).map (x :: ·)

/-- Every list of `n` on/off switches. -/
def allSwitches : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [false, true].flatMap fun b => (allSwitches n).map (b :: ·)

/-- Every solution that fits the puzzle's shape. -/
def candidates (p : Puzzle) : List Solution :=
  (allPicks p.choices).flatMap fun build =>
    (allSwitches p.routes.length).flatMap fun routesOn =>
      (none :: p.metroSites.map some).flatMap fun station =>
        (allSwitches p.bridgeSites.length).map fun bridges =>
          { build, routesOn, station, bridges }

/-- The product of the lengths of some lists. -/
def productOfLengths {α : Type} : List (List α) → Nat
  | [] => 1
  | xs :: rest => xs.length * productOfLengths rest

/-- How many candidates there are, without listing them. -/
def candidateCount (p : Puzzle) : Nat :=
  productOfLengths p.choices * 2 ^ p.routes.length * (p.metroSites.length + 1)
    * 2 ^ p.bridgeSites.length

/-- The first item with the highest value of `f`, or `none` for an empty list. -/
def bestOf {α : Type} (f : α → Int) : List α → Option α
  | [] => none
  | x :: xs =>
    match bestOf f xs with
    | none => some x
    | some y => if f x < f y then some y else some x

/-- Most candidates the solver will try. -/
def stepLimit : Nat := 3000000

/-- The valid candidates, each with its score. -/
def scoredValid (p : Puzzle) : List (Solution × Int) :=
  let c := prepare p
  (candidates p).filterMap fun s =>
    -- Cheap check first: over budget means not valid.
    if costOf p s > p.budget then none else
    if ValidWith c s then some (s, scoreWith c s) else none

/-- The best valid solution, or `none` if there are more than `stepLimit`
candidates. -/
def solvePlain (p : Puzzle) : Option Solution :=
  if candidateCount p > stepLimit then none
  else (bestOf (·.2) (scoredValid p)).map (·.1)

end SevenBridges
