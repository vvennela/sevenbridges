import SevenBridges.Rules.Score

/-!
# Valid solutions (DESIGN.md §7)

A solution is valid if it fits the puzzle, stays within budget, and every
transit line it uses passes its rules.
-/

namespace SevenBridges
open Numbers

/-- The solution has the shape the puzzle asks for: one building per block,
each one of that block's choices; one on/off switch per route; the metro
station, if any, on a block along the line; and one built/not built switch per
bridge site. -/
def FitsPuzzle (p : Puzzle) (s : Solution) : Prop :=
  s.build.length = p.blockCount
  ∧ (∀ pair ∈ s.build.zip p.choices, pair.1 ∈ pair.2)
  ∧ s.routesOn.length = p.routes.length
  ∧ (∀ k ∈ s.station.toList, k ∈ p.metroSites)
  ∧ s.bridges.length = p.bridgeSites.length

/-- The transit rules on simulated day `d`: every route that is on has the
bridges it crosses built and enough riders to pay for itself, and the metro
station (if built) has enough riders. -/
def TransitPays (c : Context) (s : Solution) (d : List CatDay) : Prop :=
  (∀ r ∈ List.range c.puzzle.routes.length, s.routesOn.getD r false = true →
      s.transit.bridgesReady c r = true ∧ routeRiders c s.transit d s.look r ≥ minRouteRiders)
  ∧ (s.station.isSome = true → stationRiders c s.transit d s.look ≥ minStationRiders)

/-- The rules a solution must pass, with the things computed once per puzzle
in `c`. -/
def ValidWith (c : Context) (s : Solution) : Prop :=
  FitsPuzzle c.puzzle s
  ∧ costOf c.puzzle s ≤ c.puzzle.budget
  ∧ TransitPays c s (simulate c s.transit s.look)

/-- **A valid solution**: it fits the puzzle, stays within budget, every route
that is on has the bridges it crosses built and enough riders to pay for
itself, and the metro station (if built) has enough riders. -/
def Valid (p : Puzzle) (s : Solution) : Prop := ValidWith (prepare p) s

instance (p : Puzzle) (s : Solution) : Decidable (FitsPuzzle p s) := by
  unfold FitsPuzzle; infer_instance

instance (c : Context) (s : Solution) (d : List CatDay) : Decidable (TransitPays c s d) := by
  unfold TransitPays; infer_instance

instance (c : Context) (s : Solution) : Decidable (ValidWith c s) := by
  unfold ValidWith; infer_instance

instance (p : Puzzle) (s : Solution) : Decidable (Valid p s) := by
  unfold Valid; infer_instance

/-- The empty layout: nothing built on open blocks, no routes, no station, no
bridges. -/
def emptyLayout (p : Puzzle) : Solution :=
  { build := (List.range p.blockCount).map fun i => (p.fixedAt i).getD .empty
    routesOn := p.routes.map fun _ => false
    station := none
    bridges := p.bridgeSites.map fun _ => false }

/-- **The score of a layout.** -/
def score (p : Puzzle) (s : Solution) : Int := scoreWith (prepare p) s

/-- **Rating out of 100**: how much of the way from the empty layout's score to
the best score this layout gets, in percent, rounded down (0 if it scores
less than the empty layout). Invalid layouts get 0. (If the best is no better
than the empty layout, a layout scoring at least the best gets 100.) -/
def ratingWith (c : Context) (bestScore : Int) (s : Solution) : Nat :=
  if ValidWith c s then
    let base := scoreWith c (emptyLayout c.puzzle)
    if base < bestScore then ((scoreWith c s - base) * 100 / (bestScore - base)).toNat
    else if bestScore ≤ scoreWith c s then 100 else 0
  else 0

/-- The rating, for a puzzle. -/
def rating (p : Puzzle) (bestScore : Int) (s : Solution) : Nat := ratingWith (prepare p) bestScore s

end SevenBridges
