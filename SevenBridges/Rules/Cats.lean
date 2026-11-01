import SevenBridges.Rules.Puzzle

/-!
# The cats and their traits (DESIGN.md §15.2)

Every housing block has one resident cat per 5 residents (`Building.cats`).
Cat number `i` on block `h` gets its traits from the puzzle's simulation seed
(`Puzzle.simSeed`), with `catTraits`. The traits never depend on the layout:
building more floors adds cats `8, 9, …` to a block, and cats `0 … 7` stay
the same cats.
-/

namespace SevenBridges

/-- One personality type of one resident group. -/
structure ResidentType where
  /-- The group's number in the puzzle. -/
  group : Nat
  /-- The personality's number in its group. -/
  type : Nat
  /-- Share of all cats with this type, in hundredths of a percent: the
  group's percent times the personality's percent. -/
  share : Nat
  personality : Personality
deriving Repr, Inhabited

/-- Every personality type of every group of a puzzle, numbered in order. -/
def residentTypesOf (p : Puzzle) : List ResidentType :=
  (List.range p.groups.length).flatMap fun gi =>
    let g := p.groups.getD gi default
    (List.range g.types.length).map fun ti =>
      let t := g.types.getD ti default
      { group := gi, type := ti, share := g.share * t.share, personality := t }

/-- How a cat gets around. -/
inductive Mobility
  /-- Walks; takes the metro downtown, or drives if it must. -/
  | walker
  /-- Walks next door, else takes the bus; then the metro; drives if it must. -/
  | bus
  /-- Always drives to work. -/
  | driver
deriving Repr, DecidableEq, Inhabited

/-- What a cat does during the day. -/
inductive DayKind
  | works
  | studies
  | retired
deriving Repr, DecidableEq, Inhabited

/-- A cat's traits. -/
structure Traits where
  /-- Its resident type: a number into `residentTypesOf`. It decides the cat's
  group and personality. -/
  kind : Nat
  group : Nat
  type : Nat
  mobility : Mobility
  day : DayKind
  /-- Eats lunch at a café or restaurant next to its office, if there is one. -/
  eatsOut : Bool
  /-- Goes to a bar (or else a café or restaurant) next to home in the evening. -/
  goesOut : Bool
deriving Repr, DecidableEq, Inhabited

/-- A number from the seed for roll `k` of cat `i` on block `h`. The same
inputs always give the same number. -/
def roll (seed h i k : Nat) : Nat :=
  let step (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  step (step (step (step (step seed + h + 1) + i + 1) + k + 1)) / 2 ^ 33

/-- Pick an item by shares: the first item whose running total of shares is
above `r` (the last item if none is). -/
def pickByShare : List Nat → Nat → Nat
  | [], _ => 0
  | [_], _ => 0
  | s :: rest, r => if r < s then 0 else pickByShare rest (r - s) + 1

#guard pickByShare [60, 40] 59 == 0
#guard pickByShare [60, 40] 60 == 1

/-- **The traits of cat `i` on block `h`**, from the simulation seed:
- its resident type, by the types' shares;
- whether it works, studies or is retired, by its group's percents;
- how it gets around, by its group's percents (a cat that hates transit
  always drives);
- whether it eats out at lunch and goes out in the evening, by its group's
  percents. -/
def catTraits (p : Puzzle) (h i : Nat) : Traits :=
  let types := residentTypesOf p
  let kind := pickByShare (types.map (·.share)) (roll p.simSeed h i 0 % 10000)
  let rt := types.getD kind default
  let g := p.groups.getD rt.group default
  let r1 := roll p.simSeed h i 1 % 100
  let r2 := roll p.simSeed h i 2 % 100
  let day : DayKind :=
    if r1 < g.works then .works else if r1 < g.works + g.studies then .studies else .retired
  let mobility : Mobility :=
    if rt.personality.feeling .transit == .hates then .driver
    else if r2 < g.drives then .driver else if r2 < g.drives + g.buses then .bus else .walker
  { kind, group := rt.group, type := rt.type, mobility, day
    eatsOut := decide (roll p.simSeed h i 3 % 100 < g.eatsOut)
    goesOut := decide (roll p.simSeed h i 4 % 100 < g.goesOut) }

/-- The most cats a block can hold: 5 floors of homes. -/
def maxCatsPerBlock : Nat := (Building.housing .five).cats

end SevenBridges
