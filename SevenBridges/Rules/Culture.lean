/-!
# Residents and culture (DESIGN.md §5, §15.2)
-/

namespace SevenBridges

/-- Things residents can care about. -/
inductive Factor
  /-- A park is next to their block. -/
  | parks
  /-- A bar is next to their block. -/
  | nightlife
  /-- Nothing loud next to their block (a building of 3 or more floors, or a
  bar), no car traffic, and no metro station on or next to it. -/
  | quiet
  /-- A bus route stops at their block, or the metro station is on or next to it. -/
  | transit
  /-- A shop is next to their block. -/
  | shops
  /-- At least 3 different kinds of building (housing, office, shop, park,
  bar, food) are next to their block. -/
  | variety
  /-- A café or restaurant is next to their block. -/
  | food
  /-- No car traffic on their block, or a park next to it to clean the air. -/
  | cleanAir
deriving Repr, DecidableEq, Inhabited

/-- Every factor, in a fixed order. -/
def Factor.all : List Factor :=
  [.parks, .nightlife, .quiet, .transit, .shops, .variety, .food, .cleanAir]

/-- How a group feels about a factor. -/
inductive Feeling
  | cares
  | neutral
  | hates
deriving Repr, DecidableEq, Inhabited

/-- Happiness each resident gets from a factor they have. -/
def Feeling.value : Feeling → Int
  | .cares => 2
  | .neutral => 0
  | .hates => -1

/-- A personality type within a group: what these residents care about and
hate. `share` is the percent of the group with this personality. -/
structure Personality where
  name : String
  share : Nat
  cares : List Factor
  hates : List Factor
deriving Repr, DecidableEq, Inhabited

/-- A group of residents. `share` is the percent of the town's cats who belong
to this group. `types` are its personality types; the first one is the usual
one, and most of the group has it.

The other numbers say how the group's cats spend their day, in percent: how
many work and how many study (the rest are retired), how many drive and how
many ride the bus (the rest walk), and how many eat out at lunch and go out in
the evening. -/
structure Group where
  name : String
  share : Nat
  types : List Personality
  works : Nat := 60
  studies : Nat := 10
  drives : Nat := 30
  buses : Nat := 30
  eatsOut : Nat := 40
  goesOut : Nat := 30
deriving Repr, DecidableEq, Inhabited

/-- How residents with this personality feel about a factor. "Cares" wins if a
factor is listed twice. -/
def Personality.feeling (t : Personality) (f : Factor) : Feeling :=
  if f ∈ t.cares then .cares else if f ∈ t.hates then .hates else .neutral

/-- A factor's name, in plain words, for the culture text. -/
def Factor.words : Factor → String
  | .parks => "parks"
  | .nightlife => "nightlife"
  | .quiet => "quiet streets"
  | .transit => "transit"
  | .shops => "shops nearby"
  | .variety => "a mix of buildings nearby"
  | .food => "cafés and restaurants"
  | .cleanAir => "clean air"

private def joinWords : List String → String
  | [] => ""
  | [a] => a
  | [a, b] => s!"{a} and {b}"
  | a :: rest => s!"{a}, {joinWords rest}"

/-- What a personality cares about and hates, in words: "care about …, but
hate …". -/
def Personality.likes (t : Personality) : String :=
  let cares := joinWords (t.cares.map Factor.words)
  let hates := joinWords (t.hates.map Factor.words)
  match t.cares, t.hates with
  | [], [] => "don't mind much either way"
  | _, [] => s!"care about {cares}"
  | [], _ => s!"hate {hates}"
  | _, _ => s!"care about {cares}, but hate {hates}"

/-- The culture text for one group, made from its personality types. -/
def Group.describe (g : Group) : String :=
  match g.types with
  | [] => s!"{g.name} ({g.share}%) don't mind much either way."
  | usual :: others =>
    s!"{g.name} ({g.share}%) {usual.likes}."
      ++ String.join (others.map fun t => s!" {t.share}% of them are {t.name}, who {t.likes}.")

#guard ({ name := "Families", share := 60,
          types := [{ name := "Families", share := 80, cares := [.parks, .quiet], hates := [.nightlife] },
                    { name := "Night owls", share := 20, cares := [.parks, .nightlife], hates := [] }] }
        : Group).describe
    == "Families (60%) care about parks and quiet streets, but hate nightlife. 20% of them are Night owls, who care about parks and nightlife."

end SevenBridges
