/-!
# What the player builds (DESIGN.md §3)
-/

namespace SevenBridges

/-- Number of stories: 1, 2 or 3. -/
inductive Height
  | one
  | two
  | three
deriving Repr, DecidableEq, Inhabited

/-- The number of stories, as a number. -/
def Height.stories : Height → Nat
  | .one => 1
  | .two => 2
  | .three => 3

/-- What can stand on a block. -/
inductive Building
  | empty
  | housing (h : Height)
  | office (h : Height)
  | shop (h : Height)
  | park
  | bar
deriving Repr, DecidableEq, Inhabited

namespace Building

/-- Every building in the game: 12 choices. -/
def catalog : List Building :=
  [empty, park, bar,
   housing .one, housing .two, housing .three,
   office .one, office .two, office .three,
   shop .one, shop .two, shop .three]

/-- Stories of a building. Parks and bars count as 1 story. -/
def stories : Building → Nat
  | empty => 0
  | housing h | office h | shop h => h.stories
  | park | bar => 1

/-- People who live here: 20 per story of housing. -/
def residents : Building → Nat
  | housing h => 20 * h.stories
  | _ => 0

/-- People who work here: 20 per office story. Only offices have jobs. -/
def jobs : Building → Nat
  | office h => 20 * h.stories
  | _ => 0

/-- Build cost in thousands of dollars. Each story costs the base price, and
each story above the first costs 30 more. -/
def cost : Building → Nat
  | empty => 0
  | housing h => 100 * h.stories + 30 * (h.stories - 1)
  | office h => 120 * h.stories + 30 * (h.stories - 1)
  | shop h => 80 * h.stories + 30 * (h.stories - 1)
  | park => 40
  | bar => 60

def isPark (b : Building) : Bool := b == park
def isBar (b : Building) : Bool := b == bar
def isShop : Building → Bool
  | shop _ => true
  | _ => false
def isHousing : Building → Bool
  | housing _ => true
  | _ => false
def isOffice : Building → Bool
  | office _ => true
  | _ => false

end Building

example : Building.catalog.length = 12 := rfl
example : (Building.housing .three).cost = 360 := rfl
example : (Building.office .two).jobs = 40 := rfl

end SevenBridges
