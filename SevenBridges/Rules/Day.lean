import SevenBridges.Rules.Context

/-!
# One simulated day of the cats (DESIGN.md §15.2)

The same every time for a given layout and simulation seed:

1. **Morning commute.** Cats go one at a time, block by block, in order. A cat
   that works takes a free job in an office it can reach (next door first,
   then one bus ride away), else commutes downtown: by metro if its block is
   in metro reach, else by car. Drivers always drive. Walkers don't take the
   bus. Students ride the metro downtown if they can, else study at home.
   Retired cats stay home.
2. **Lunch.** A cat at an office that eats out walks to a café or restaurant
   next to the office, and back.
3. **Back home** the same way it came.
4. **Evening.** A cat that goes out walks to a bar next to home (or else a
   café or restaurant), and back home.

Each cat stands for 5 residents. The proofs that every cat ends the day at
home and that each cat is counted once are in `SevenBridges/DayProofs.lean`.
-/

namespace SevenBridges
open Numbers

/-- Where a cat can be. -/
inductive Place
  | block (j : Nat)
  | downtown
deriving Repr, DecidableEq, Inhabited

/-- How a trip is made. -/
inductive Mode
  | walk
  | bus
  | car
  | metro
deriving Repr, DecidableEq, Inhabited

/-- One cat: the block it lives on, its number there, and its traits. -/
structure Resident where
  home : Nat
  index : Nat
  traits : Traits
deriving Repr, DecidableEq, Inhabited

/-- The cats who live on block `h` when it holds building `b`: one per 5
residents, numbered from 0. -/
def residentsOn (c : Context) (h : Nat) (b : Building) : List Resident :=
  (List.range b.cats).map fun i => ⟨h, i, c.traitsAt h i⟩

/-- Every cat in town, block by block. -/
def population (c : Context) (look : Nat → Building) : List Resident :=
  c.blocks.flatMap fun h => residentsOn c h (look h)

/-- How one cat spends its day. -/
structure CatDay where
  who : Resident
  /-- Where it goes in the morning: an office block, downtown, or nowhere
  (`none`: it stays home). -/
  work : Option Place
  /-- How it gets there and back. -/
  mode : Mode
  /-- The bus route it rides, if it rides one. -/
  route : Option Nat
  /-- The café or restaurant where it has lunch, if any. -/
  lunch : Option Nat
  /-- The bar, café or restaurant it goes to in the evening, if any. -/
  evening : Option Nat
deriving Repr, Inhabited

/-- Free jobs before the commute: on each block, one per 5 jobs (each cat
stands for 5 workers). -/
def startSeats (c : Context) (look : Nat → Building) : List Nat :=
  c.blocks.map fun j => (look j).jobs / residentsPerCat

/-- **Where a cat goes in the morning, and how**, when `seats` are the free
jobs on each block. -/
def chooseWork (c : Context) (T : Transit) (seats : List Nat) (r : Resident) :
    Option Place × Mode :=
  let h := r.home
  let free (j : Nat) : Bool := seats.getD j 0 > 0
  let nextDoor := c.blocks.find? fun j => T.isNeighbor c j h && free j
  let byBus := c.blocks.find? fun j => T.busLinked c j h && free j
  let metro := T.stationReaches c h
  let downtown : Option Place × Mode := if metro then (some .downtown, .metro) else (some .downtown, .car)
  match r.traits.day, r.traits.mobility with
  | .retired, _ => (none, .walk)
  | .studies, _ => if metro then (some .downtown, .metro) else (none, .walk)
  | .works, .driver =>
    match nextDoor.or byBus with
    | some j => (some (.block j), .car)
    | none => (some .downtown, .car)
  | .works, .walker =>
    match nextDoor with
    | some j => (some (.block j), .walk)
    | none => downtown
  | .works, .bus =>
    match nextDoor, byBus with
    | some j, _ => (some (.block j), .walk)
    | none, some j => (some (.block j), .bus)
    | none, none => downtown

/-- Take a seat on block `j` if the cat works there. -/
def takeSeat (seats : List Nat) : Option Place → List Nat
  | some (.block j) => seats.set j (seats.getD j 0 - 1)
  | _ => seats

/-- The bus route a cat rides from home to block `j`: the first route that
runs and stops at both. -/
def busRoute (c : Context) (T : Transit) (r : Resident) (work : Option Place) (mode : Mode) :
    Option Nat :=
  match mode, work with
  | .bus, some (.block j) => (T.routesOn c).find? fun q => c.stopsAt q r.home && c.stopsAt q j
  | _, _ => none

/-- Where a cat has lunch: a café or restaurant next to its office, if it eats out. -/
def lunchSpot (c : Context) (T : Transit) (look : Nat → Building) (r : Resident)
    (work : Option Place) : Option Nat :=
  match work with
  | some (.block j) =>
    if r.traits.eatsOut then c.blocks.find? fun f => T.isNeighbor c j f && (look f).isFood else none
  | _ => none

/-- Where a cat goes in the evening, if it goes out: a bar next to home, or
else a café or restaurant next to home. -/
def eveningSpot (c : Context) (T : Transit) (look : Nat → Building) (r : Resident) : Option Nat :=
  if r.traits.goesOut then
    (c.blocks.find? fun v => T.isNeighbor c r.home v && (look v).isBar).or
      (c.blocks.find? fun v => T.isNeighbor c r.home v && (look v).isFood)
  else none

/-- A cat's whole day, once its morning choice is made. -/
def dayOf (c : Context) (T : Transit) (look : Nat → Building) (r : Resident)
    (choice : Option Place × Mode) : CatDay :=
  { who := r, work := choice.1, mode := choice.2, route := busRoute c T r choice.1 choice.2
    lunch := lunchSpot c T look r choice.1, evening := eveningSpot c T look r }

/-- One cat's turn: choose, take a seat, note its day. -/
def commuteStep (c : Context) (T : Transit) (look : Nat → Building)
    (acc : List Nat × List CatDay) (r : Resident) : List Nat × List CatDay :=
  let choice := chooseWork c T acc.1 r
  (takeSeat acc.1 choice.1, dayOf c T look r choice :: acc.2)

/-- **The simulated day**: every cat's day, in population order. -/
def simulate (c : Context) (T : Transit) (look : Nat → Building) : List CatDay :=
  ((population c look).foldl (commuteStep c T look) (startSeats c look, [])).2.reverse

/-! ## What the day produces -/

/-- Some cat of block `x` drives. -/
def carFrom (d : List CatDay) (x : Nat) : Bool :=
  d.any fun cd => cd.who.home == x && cd.mode == .car

/-- **Traffic** on block `h`: cats of `h` or of a block next to it drive. -/
def traffic (c : Context) (T : Transit) (d : List CatDay) (h : Nat) : Bool :=
  carFrom d h || (T.neighborsOf c h).any (carFrom d)

/-- Workers who came to block `j` from town: 5 per cat working there. -/
def localWorkers (d : List CatDay) (j : Nat) : Nat :=
  residentsPerCat * (d.filter fun cd => cd.work == some (.block j)).length

/-- Points for a downtown job, by how the cat gets there. -/
def downtownWorth : Mode → Nat
  | .metro => metroJobWorth
  | .car => carJobWorth
  | _ => 0

/-- Points from cats of block `h` who work downtown: 5 residents each, at the
metro or car rate. -/
def downtownOutput (d : List CatDay) (h : Nat) : Nat :=
  d.foldl (fun t cd =>
    if cd.who.home == h && cd.who.traits.day == .works && cd.work == some .downtown then
      t + residentsPerCat * downtownWorth cd.mode
    else t) 0

/-! ## The day as trips -/

/-- Parts of the day. -/
inductive Phase
  | commute
  | lunch
  | evening
  | home
deriving Repr, DecidableEq, Inhabited

/-- One trip of one cat. -/
structure Leg where
  start : Place
  stop : Place
  mode : Mode
  phase : Phase
  /-- The bus route, on a bus trip. -/
  route : Option Nat := none
deriving Repr, DecidableEq, Inhabited

/-- A cat's trips, in order: to work, to lunch and back, home, out in the
evening and back home. -/
def CatDay.legs (d : CatDay) : List Leg :=
  let home := Place.block d.who.home
  let w := d.work.getD home
  (match d.work with | some p => [⟨home, p, d.mode, .commute, d.route⟩] | none => [])
  ++ (match d.lunch with
      | some f => [⟨w, .block f, .walk, .lunch, none⟩, ⟨.block f, w, .walk, .lunch, none⟩]
      | none => [])
  ++ (match d.work with | some p => [⟨p, home, d.mode, .home, d.route⟩] | none => [])
  ++ (match d.evening with
      | some v => [⟨home, .block v, .walk, .evening, none⟩, ⟨.block v, home, .walk, .home, none⟩]
      | none => [])

/-- Follow trips from place `here`: where the cat ends up, or `none` if a trip
starts somewhere the cat is not. -/
def follow : Place → List Leg → Option Place
  | here, [] => some here
  | here, l :: rest => if l.start = here then follow l.stop rest else none

/-- Moments of the day. -/
inductive Moment
  | dawn
  | morning
  | noon
  | afternoon
  | evening
  | night
deriving Repr, DecidableEq, Inhabited

def Moment.all : List Moment := [.dawn, .morning, .noon, .afternoon, .evening, .night]

/-- Where a cat is at each moment of its day. -/
def CatDay.place (d : CatDay) : Moment → Place
  | .dawn => .block d.who.home
  | .morning => d.work.getD (.block d.who.home)
  | .noon => match d.lunch with
    | some f => .block f
    | none => d.work.getD (.block d.who.home)
  | .afternoon => d.work.getD (.block d.who.home)
  | .evening => match d.evening with
    | some v => .block v
    | none => .block d.who.home
  | .night => .block d.who.home

/-- Every place a cat can be: downtown and each block. -/
def places (c : Context) : List Place := .downtown :: c.blocks.map .block

/-- How many cats are at place `pl` at moment `m`. -/
def countAt (d : List CatDay) (m : Moment) (pl : Place) : Nat :=
  (d.filter fun cd => cd.place m == pl).length

end SevenBridges
