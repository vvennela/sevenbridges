/-!
# What the player builds (DESIGN.md §3, §15.3)
-/

namespace SevenBridges

/-- Number of floors: 1 to 5. Homes go up to 3, offices up to 5, shops up
to 2 (`Building.catalog`). -/
inductive Height
  | one
  | two
  | three
  | four
  | five
deriving Repr, DecidableEq, Inhabited

/-- The number of floors, as a number. -/
def Height.stories : Height → Nat
  | .one => 1
  | .two => 2
  | .three => 3
  | .four => 4
  | .five => 5

/-- What can stand on a block. -/
inductive Building
  | empty
  | housing (h : Height)
  | office (h : Height)
  | shop (h : Height)
  /-- A café or restaurant: lunch for offices next door, dinner for neighbors. -/
  | food
  | park
  | bar
deriving Repr, DecidableEq, Inhabited

namespace Building

/-- Every building in the game: 14 choices. Homes have 1–3 floors, offices
1–5, shops 1–2. -/
def catalog : List Building :=
  [empty, park, bar, food,
   housing .one, housing .two, housing .three,
   office .one, office .two, office .three, office .four, office .five,
   shop .one, shop .two]

/-- Floors of a building. Parks, bars and food places count as 1 floor. -/
def stories : Building → Nat
  | empty => 0
  | housing h | office h | shop h => h.stories
  | food | park | bar => 1

/-- People who live here: 20 per floor of housing. -/
def residents : Building → Nat
  | housing h => 20 * h.stories
  | _ => 0

/-- Resident cats who live here: one cat stands for 5 residents. -/
def cats (b : Building) : Nat := b.residents / 5

/-- People who work here: 20 per office floor. Only offices have jobs. -/
def jobs : Building → Nat
  | office h => 20 * h.stories
  | _ => 0

/-- Build cost in thousands of dollars. Each floor costs the base price, and
each floor above the first costs 30 more. -/
def cost : Building → Nat
  | empty => 0
  | housing h => 100 * h.stories + 30 * (h.stories - 1)
  | office h => 120 * h.stories + 30 * (h.stories - 1)
  | shop h => 80 * h.stories + 30 * (h.stories - 1)
  | food => 70
  | park => 40
  | bar => 60

def isPark (b : Building) : Bool := b == park
def isBar (b : Building) : Bool := b == bar
def isFood (b : Building) : Bool := b == food
def isShop : Building → Bool
  | shop _ => true
  | _ => false
def isHousing : Building → Bool
  | housing _ => true
  | _ => false
def isOffice : Building → Bool
  | office _ => true
  | _ => false

/-- A building of 3 or more floors, or a bar: it breaks "quiet" next door. -/
def isLoud (b : Building) : Bool := decide (b.stories ≥ 3) || b.isBar

end Building

example : Building.catalog.length = 14 := rfl
example : (Building.housing .three).cost = 360 := rfl
example : (Building.office .five).jobs = 100 := rfl
example : (Building.housing .two).cats = 8 := rfl

end SevenBridges
