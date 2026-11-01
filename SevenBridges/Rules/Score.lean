import SevenBridges.Rules.Puzzle
import SevenBridges.Rules.Bus

/-!
# How a layout is scored: local rules, like Civilization (DESIGN.md §6)

**A block's value depends only on the blocks it watches**: itself, its
neighbors, and blocks linked to it by a bus route that is on. Two blocks are
neighbors if they share a road on land, or a river segment with a bridge
built on it. This is what makes
the best layout fast to find and to prove (`SevenBridges/Branch.lean`).

For each block:

- **Happiness** (housing): each personality type of each resident group adds
  up its feelings about the factors its residents have (parks next door, a bar next door, quiet, …).
- **Productivity** (offices): jobs filled by workers who live next door or one
  bus ride away. If the subway station reaches the block, outside workers fill
  all its jobs. Offices do more next to other offices.
- **Sales** (shops): customers who live next door or one bus ride away, up to
  what the shop can serve.
- **Crime**: each unhappy resident costs points, more the further below the
  unhappy line they are.

The **score** is the sum of block values, minus one neighborhood-wide penalty:
each home missing in a housing shortage (more jobs than homes and subway
workers) costs points.
-/

namespace SevenBridges
open Numbers

/-! ## Things computed once per puzzle -/

/-- One personality type of one resident group: the residents whose happiness
is counted together. -/
structure ResidentType where
  /-- The group's number in the puzzle. -/
  group : Nat
  /-- The personality's number in its group. -/
  type : Nat
  /-- Share of each housing block's residents with this type, in hundredths of
  a percent: the group's percent times the personality's percent. -/
  share : Nat
  personality : Personality
deriving Repr, Inhabited

/-- Every personality type of every group of a puzzle. -/
def residentTypesOf (p : Puzzle) : List ResidentType :=
  (List.range p.groups.length).flatMap fun gi =>
    let g := p.groups.getD gi default
    (List.range g.types.length).map fun ti =>
      let t := g.types.getD ti default
      { group := gi, type := ti, share := g.share * t.share, personality := t }

/-- Things computed once per puzzle, before trying any layout. -/
structure Context where
  puzzle : Puzzle
  /-- Shortest road distance between blocks (used only for the animation). -/
  distances : Array (Array Nat)
  /-- Neighbors over land of each block. -/
  landNeighbors : Array (List Nat)
  /-- For each block: the blocks across the river from it, each with the
  number of the bridge site between them. -/
  bridgeLinks : Array (List (Nat × Nat))
  /-- Blocks each route stops at. -/
  routeStops : Array (List Nat)
  /-- Blocks each route stops at, in the order the bus reaches them. -/
  routeStopOrder : Array (List Nat)
  /-- The bridges each route needs: the bridge sites on its path. -/
  routeBridges : Array (List Nat)
  /-- The route crosses the river where no bridge can be built, so it can never run. -/
  routeBlocked : Array Bool
  /-- Every personality type of every group. -/
  residentTypes : Array ResidentType
deriving Inhabited

/-- Work out the things that don't depend on the layout. -/
def prepare (p : Puzzle) : Context :=
  let n := p.blockCount
  let stops (r : Route) : List Nat :=
    (List.range n).filter fun b => (p.map.block b).corners.any (r.path.contains ·)
  let bridgeSide (k : Nat) : Nat × Nat := (p.map.segments.getD (p.bridgeSites.getD k 0) default).side
  let bridges := List.range p.bridgeSites.length
  { puzzle := p
    distances := p.map.blockDistances
    landNeighbors := Array.ofFn (n := n) fun i =>
      (List.range n).filter fun j => decide (p.map.LandNeighbors i j)
    bridgeLinks := Array.ofFn (n := n) fun i =>
      (List.range n).flatMap fun j => (bridges.filter fun k =>
        i.val != j && (p.map.block i).sides.contains (bridgeSide k)
          && (p.map.block j).sides.contains (bridgeSide k)).map fun k => (j, k)
    routeStops := (p.routes.map stops).toArray
    routeStopOrder := (p.routes.map fun r =>
      let first (b : Nat) : Nat := (p.map.block b).corners.foldl (fun m x => min m (r.path.idxOf x)) r.path.length
      (stops r).mergeSort fun a b => first a ≤ first b).toArray
    routeBridges := (p.routes.map fun r => bridges.filter fun k => r.sides.contains (bridgeSide k)).toArray
    routeBlocked := (p.routes.map fun r => r.sides.any fun side =>
      p.map.isRiver side && !bridges.any fun k => bridgeSide k == side).toArray
    residentTypes := (residentTypesOf p).toArray }

namespace Context

def dist (c : Context) (i j : Nat) : Nat := (c.distances.getD i #[]).getD j noPath
def landNeighborsOf (c : Context) (i : Nat) : List Nat := c.landNeighbors.getD i []
def bridgeLinksOf (c : Context) (i : Nat) : List (Nat × Nat) := c.bridgeLinks.getD i []
def bridgesFor (c : Context) (r : Nat) : List Nat := c.routeBridges.getD r []
def blocked (c : Context) (r : Nat) : Bool := c.routeBlocked.getD r false
def stopsAt (c : Context) (r b : Nat) : Bool := (c.routeStops.getD r []).contains b
def blocks (c : Context) : List Nat := List.range c.puzzle.blockCount
def groupCount (c : Context) : Nat := c.puzzle.groups.length
def typeCount (c : Context) : Nat := c.residentTypes.size
def residentType (c : Context) (k : Nat) : ResidentType := c.residentTypes.getD k default

end Context

/-! ## Transit choices -/

/-- The transit part of a solution: which routes are on, the station, and which
bridges are built. -/
structure Transit where
  on : List Bool
  station : Option Nat
  bridges : List Bool
deriving Repr, DecidableEq, Inhabited

def Solution.transit (s : Solution) : Transit := ⟨s.routesOn, s.station, s.bridges⟩

/-- The building on each block of a solution (empty past the end). -/
def Solution.look (s : Solution) (i : Nat) : Building := s.build.getD i .empty

namespace Transit
variable (c : Context) (T : Transit)

/-- Bridge `k` is built. -/
def bridged (k : Nat) : Bool := T.bridges.getD k false

/-- Every bridge route `r` needs is built (and it doesn't cross the river where
no bridge can be built). -/
def bridgesReady (r : Nat) : Bool := !c.blocked r && (c.bridgesFor r).all T.bridged

/-- Routes that run: they are on, and their bridges are built. -/
def routesOn : List Nat :=
  (List.range c.puzzle.routes.length).filter fun r => T.on.getD r false && T.bridgesReady c r

/-- **Blocks `i` and `j` are neighbors**: they share a road on land, or a river
segment with a bridge built on it. -/
def isNeighbor (i j : Nat) : Bool :=
  (c.landNeighborsOf i).contains j || (c.bridgeLinksOf i).any fun x => x.1 == j && T.bridged x.2

/-- The neighbors of block `i`. -/
def neighborsOf (i : Nat) : List Nat := c.blocks.filter (T.isNeighbor c i)

/-- A bus route that is on stops at block `i`. -/
def served (i : Nat) : Bool := (T.routesOn c).any (c.stopsAt · i)

/-- Blocks `i` and `j` are different and one bus route that is on stops at both. -/
def busLinked (i j : Nat) : Bool :=
  i != j && (T.routesOn c).any fun r => c.stopsAt r i && c.stopsAt r j

/-- Residents of block `h` can get to block `j` (to work or to shop): `h` is
next to `j`, or one bus ride away. -/
def canReach (j h : Nat) : Bool := T.isNeighbor c j h || T.busLinked c j h

/-- The station is on block `i` or next to it. -/
def nearStation (i : Nat) : Bool :=
  T.station.any fun k => k == i || T.isNeighbor c i k

/-- Outside visitors from the station can reach block `j`: it is the station's
block, next to it, or one bus ride away. -/
def stationReaches (j : Nat) : Bool :=
  T.station.any fun k => k == j || T.canReach c k j

/-- **The blocks block `i` watches**: itself, its neighbors, and blocks linked
to it by bus. Its value depends on nothing else. -/
def watched (i : Nat) : List Nat :=
  i :: (T.neighborsOf c i ++ c.blocks.filter (busLinked c T i))

end Transit

/-- The layout as block `i` sees it: the buildings on the blocks it watches,
and empty everywhere else. -/
def seenFrom (c : Context) (T : Transit) (i : Nat) (look : Nat → Building) :
    Nat → Building :=
  let w := T.watched c i
  fun j => if j ∈ w then look j else .empty

/-! ## One block's value -/

/-- Residents of building `b` who have the resident type `rt`. -/
def typeResidents (b : Building) (rt : ResidentType) : Nat := b.residents * rt.share / 10000

/-- The kinds of building that count for variety: housing, office, shop,
park, bar. -/
def kindTests : List (Building → Bool) :=
  [Building.isHousing, Building.isOffice, Building.isShop, Building.isPark, Building.isBar]

/-- Factors that residents of block `h` have. -/
def factorsHad (c : Context) (T : Transit) (look : Nat → Building) (h : Nat) :
    List Factor :=
  let nextTo (test : Building → Bool) : Bool := (T.neighborsOf c h).any fun j => test (look j)
  Factor.all.filter fun
    | .parks => nextTo Building.isPark
    | .nightlife => nextTo Building.isBar
    | .quiet => !nextTo (fun b => b.stories == 3 || b.isBar)
    | .transit => T.served c h || T.nearStation c h
    | .shops => nextTo Building.isShop
    | .variety => decide ((kindTests.filter nextTo).length ≥ 3)

/-- Happiness per person for residents with personality `t` and the factors
`had`. -/
def happinessPerPerson (t : Personality) (had : List Factor) : Int :=
  had.foldl (fun s f => s + (t.feeling f).value) 0

/-- Happiness on block `i`: the residents of each type times their happiness
per person. -/
def blockHappiness (c : Context) (T : Transit) (look : Nat → Building) (i : Nat) : Int :=
  (List.range c.typeCount).foldl (fun t k =>
    let rt := c.residentType k
    t + (typeResidents (look i) rt : Int) * happinessPerPerson rt.personality (factorsHad c T look i)) 0

/-- Crime on block `i`: for each resident type below the unhappy line,
`unhappyCost` times how far below the line it is, times its residents there. -/
def blockCrime (c : Context) (T : Transit) (look : Nat → Building) (i : Nat) : Nat :=
  (List.range c.typeCount).foldl (fun t k =>
    let rt := c.residentType k
    t + unhappyCost * (unhappyLine - happinessPerPerson rt.personality (factorsHad c T look i)).toNat
          * typeResidents (look i) rt) 0

/-- Workers who can reach block `j`: residents next door or one bus ride away.
They are also the shop's customers. -/
def workersFor (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  (c.blocks.filter (T.canReach c j)).foldl (fun t h => t + (look h).residents) 0

/-- Outside workers the station brings to block `j`, if it reaches it: the jobs
local workers leave open, but at most `stationWorkersPerBlock`. -/
def stationWorkersAt (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  if T.stationReaches c j then min stationWorkersPerBlock ((look j).jobs - workersFor c T look j)
  else 0

/-- Jobs filled on block `j`: by workers who can reach it, as many as there are
jobs, plus outside workers from the station. -/
def jobsFilled (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  min (look j).jobs (workersFor c T look j) + stationWorkersAt c T look j

/-- Extra output of the office on block `j`, in percent: `officeBonusPerOffice`
for each office next to it, at most `officeBonusMax`. Other buildings get
none. -/
def officeBonus (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  if (look j).isOffice then
    min officeBonusMax (officeBonusPerOffice * ((T.neighborsOf c j).filter fun k => (look k).isOffice).length)
  else 0

/-- Productivity on block `j`: `jobWorth` per filled job, plus the office bonus. -/
def blockProductivity (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  jobWorth * jobsFilled c T look j * (100 + officeBonus c T look j) / 100

/-- Sales on block `j`: for a shop, `saleWorth` per customer, up to
`customersPerShopStory` per story. Customers are residents next door or one
bus ride away, plus, if the station reaches the shop, `shoppersPerShopStory`
outside shoppers per story. -/
def blockSales (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  match look j with
  | .shop h => saleWorth * min (customersPerShopStory * h.stories)
      (workersFor c T look j + if T.stationReaches c j then shoppersPerShopStory * h.stories else 0)
  | _ => 0

/-- **The value of block `i`**: happiness + productivity + sales − crime. -/
def blockValue (c : Context) (T : Transit) (look : Nat → Building) (i : Nat) : Int :=
  blockHappiness c T look i + blockProductivity c T look i + blockSales c T look i
    - blockCrime c T look i

/-! ## The neighborhood-wide penalty -/

/-- More jobs than homes and subway workers: the size of the housing shortage. -/
def shortage (c : Context) (T : Transit) (look : Nat → Building) : Nat :=
  c.blocks.foldl (fun t j => t + (look j).jobs) 0
    - c.blocks.foldl (fun t h => t + (look h).residents) 0
    - c.blocks.foldl (fun t j => t + stationWorkersAt c T look j) 0

/-- Each missing home in a housing shortage costs `shortageCost`. -/
def shortagePenalty (c : Context) (T : Transit) (look : Nat → Building) : Nat :=
  shortageCost * shortage c T look

/-- **The score of a layout**: the sum of every block's value (each block seeing
only the blocks it watches), minus the shortage penalty. -/
def scoreWith (c : Context) (s : Solution) : Int :=
  c.blocks.foldl (fun t i => t + blockValue c s.transit (seenFrom c s.transit i s.look) i) 0
    - shortagePenalty c s.transit s.look

/-! ## Riders (for the transit rules) -/

/-- The bus route a commuter from block `h` would ride to work: the lowest
route that is on, stops at `h`, and stops at some block with jobs. `none` if
they have a job next door, hate transit, or no route helps. -/
def commuteRoute (c : Context) (T : Transit) (look : Nat → Building) (t : Personality) (h : Nat) :
    Option Nat :=
  if (T.neighborsOf c h).any (fun j => (look j).jobs > 0) || t.feeling .transit == .hates then none
  else (T.routesOn c).find? fun r =>
    c.stopsAt r h && c.blocks.any fun j => j != h && c.stopsAt r j && (look j).jobs > 0

/-- Outside shoppers the station brings to building `b`, if it reaches it:
`shoppersPerShopStory` per shop story. -/
def shoppersAt (b : Building) : Nat :=
  match b with
  | .shop h => shoppersPerShopStory * h.stories
  | _ => 0

/-- Daily riders at the station: outside workers plus outside shoppers on the
blocks it reaches. -/
def stationRiders (c : Context) (T : Transit) (look : Nat → Building) : Nat :=
  if T.station.isNone then 0 else
  c.blocks.foldl (fun t j =>
    if T.stationReaches c j then t + stationWorkersAt c T look j + shoppersAt (look j)
    else t) 0

/-- The block a commuter from block `h` rides route `r` to: the first block
with jobs that `r` stops at. -/
def jobStop (c : Context) (look : Nat → Building) (r h : Nat) : Nat :=
  (c.blocks.find? fun j => j != h && c.stopsAt r j && (look j).jobs > 0).getD h

/-- Who wants a bus in the morning rush, as (route, from block, to block,
people): residents who ride to work (`commuteRoute`), and outside workers the
station sends on to a block one bus ride away (on the first route that links
them). -/
def busTrips (c : Context) (T : Transit) (look : Nat → Building) : List (Nat × Nat × Nat × Nat) :=
  let residents := c.blocks.flatMap fun h => (List.range c.typeCount).filterMap fun k =>
    let rt := c.residentType k
    let people := typeResidents (look h) rt
    if people = 0 then none else
    (commuteRoute c T look rt.personality h).map fun r => (r, h, jobStop c look r h, people)
  let outside := match T.station with
    | none => []
    | some k => c.blocks.filterMap fun j =>
      if j != k && !T.isNeighbor c k j && stationWorkersAt c T look j > 0 then
        ((T.routesOn c).find? fun r => c.stopsAt r k && c.stopsAt r j).map fun r =>
          (r, k, j, stationWorkersAt c T look j)
      else none
  residents ++ outside

/-- The stops of route `r` in the order a bus meets them: direction 0 runs
along the route's path, direction 1 runs back. -/
def Context.stopsInOrder (c : Context) (r dir : Nat) : List Nat :=
  let order := c.routeStopOrder.getD r []
  if dir = 0 then order else order.reverse

/-- The riders who wait for route `r` in direction `dir`: each bus trip on `r`
whose job stop comes after its home stop in that direction. Stops are numbered
along the way. -/
def rushParties (c : Context) (T : Transit) (look : Nat → Building) (r dir : Nat) : List Rush.Party :=
  let order := c.stopsInOrder r dir
  (busTrips c T look).filterMap fun x =>
    let (r', h, j, people) := x
    let a := order.idxOf h
    let b := order.idxOf j
    if r' == r && a < b && b < order.length then some ⟨a, b, people⟩ else none

/-- **The morning rush on route `r` in direction `dir`** (`Rules/Bus.lean`):
`busesPerRush` buses of `busCapacity` seats each. -/
def routeRush (c : Context) (T : Transit) (look : Nat → Building) (r dir : Nat) : Rush.State :=
  Rush.run busCapacity busesPerRush (c.stopsInOrder r dir).length (rushParties c T look r dir)

/-- Riders on route `r`: everyone who got on one of its buses in the morning
rush, in both directions. Riders left behind don't count. -/
def routeRiders (c : Context) (T : Transit) (look : Nat → Building) (r : Nat) : Nat :=
  (routeRush c T look r 0).boarded + (routeRush c T look r 1).boarded

/-! ## Costs -/

/-- Total cost of a layout: buildings on open blocks (fixed blocks are already
paid for), plus each route that is on and the station, built and run for
`years` years, plus each bridge built. -/
def costOf (p : Puzzle) (s : Solution) : Nat :=
  let buildCost := (List.range p.blockCount).foldl (fun t i =>
    if (p.fixedAt i).isSome then t else t + (s.build.getD i .empty).cost) 0
  let routesOnCount := (s.routesOn.filter id).length
  buildCost + routesOnCount * (routeBuildCost + routeYearlyCost * years)
    + (if s.station.isSome then stationBuildCost + stationYearlyCost * years else 0)
    + (s.bridges.filter id).length * bridgeCost

/-! ## The report -/

/-- How a trip is made (for the animation). -/
inductive Mode
  | walk
  | bus
  | car
  | subway
deriving Repr, DecidableEq, Inhabited

/-- A group of people making the same daily trip, for the animation. `group`
is the resident group's number, or `none` for outside visitors. -/
structure Trip where
  group : Option Nat
  fromBlock : Nat
  toBlock : Nat
  mode : Mode
  people : Nat
  /-- Road distance of the trip. -/
  cost : Nat
  /-- Bus routes used, in order. -/
  routes : List Nat
deriving Repr, DecidableEq, Inhabited

/-- Facts about one bus route in a layout. -/
structure RouteReport where
  on : Bool
  riders : Nat
deriving Repr, DecidableEq, Inhabited

/-- Riders getting on and off route `route` at block `block` in the morning
rush (both directions). -/
structure StopReport where
  route : Nat
  block : Nat
  boardings : Nat
  alightings : Nat
deriving Repr, DecidableEq, Inhabited

/-- The fullest load of one bus in the morning rush. `direction` 0 runs along
the route's path, 1 runs back. -/
structure BusReport where
  route : Nat
  direction : Nat
  bus : Nat
  maxLoad : Nat
  capacity : Nat
deriving Repr, DecidableEq, Inhabited

/-- How one personality type of one resident group on one housing block is
doing. -/
structure ResidentReport where
  block : Nat
  /-- The group's number in the puzzle. -/
  group : Nat
  /-- The personality's number in the group's `types`. -/
  type : Nat
  people : Nat
  /-- The factors these residents have (DESIGN.md §5.2). -/
  has : List Factor
  /-- Happiness per person: the group's feelings about the factors it has. -/
  happinessEach : Int
  /-- Below the unhappy line, so this block loses points to crime. -/
  unhappy : Bool
deriving Repr, DecidableEq, Inhabited

/-- How much one group's total happiness changes. -/
structure GroupChange where
  group : Nat
  change : Int
deriving Repr, DecidableEq, Inhabited

/-- Facts about one block in a layout. The impacts compare the layout with the
same layout where this block is left empty. -/
structure BlockReport where
  block : Nat
  happiness : Int
  /-- Productivity plus sales. -/
  productivity : Nat
  jobs : Nat
  /-- Jobs filled. -/
  workers : Nat
  crime : Nat
  /-- Total happiness in the neighborhood, minus that with this block empty. -/
  moodImpact : Int
  /-- Score, minus the score with this block empty. -/
  scoreImpact : Int
  /-- For each group, its total happiness minus that with this block empty. -/
  groupImpact : List GroupChange
deriving Repr, DecidableEq, Inhabited

/-- Everything the rules compute about a layout. -/
structure Report where
  cost : Nat
  happiness : Int
  /-- Productivity on all blocks. -/
  productivity : Nat
  /-- Sales on all blocks. -/
  sales : Nat
  /-- Crime on each block. -/
  crime : List Nat
  /-- Crime on all blocks, plus the shortage penalty. -/
  crimePenalty : Nat
  shortage : Nat
  routes : List RouteReport
  stationRiders : Nat
  /-- Boardings and alightings at each stop of each route that runs. -/
  stops : List StopReport
  /-- The fullest load of each bus of each route that runs. -/
  buses : List BusReport
  /-- Riders still waiting after the last bus, on all routes. -/
  leftBehind : Nat
  trips : List Trip
  /-- How each group on each housing block is doing, and why. -/
  residents : List ResidentReport
  /-- Facts about each block. -/
  blocks : List BlockReport
  score : Int
deriving Repr, Inhabited

/-- Facts about every bus route in a layout, in route order. -/
def routeReports (c : Context) (s : Solution) : List RouteReport :=
  (List.range c.puzzle.routes.length).map fun i =>
    let on := s.routesOn.getD i false
    { on, riders := if on then routeRiders c s.transit s.look i else 0 }

/-- Daily trips, for the animation: each group walks to a job next door, takes
the bus to a job one ride away, or drives to the nearest job. Outside visitors
come from the station. -/
def tripsFor (c : Context) (s : Solution) : List Trip :=
  let T := s.transit
  let look := s.look
  let hasJobs (j : Nat) : Bool := (look j).jobs > 0
  let residentTrips := c.blocks.flatMap fun h => (List.range c.typeCount).filterMap fun k =>
    let rt := c.residentType k
    let gi := rt.group
    let people := typeResidents (look h) rt
    if people = 0 then none else
    match (T.neighborsOf c h).find? hasJobs with
    | some j => some ⟨some gi, h, j, .walk, people, c.dist h j, []⟩
    | none =>
      match commuteRoute c T look rt.personality h with
      | some r =>
        let j := jobStop c look r h
        some ⟨some gi, h, j, .bus, people, c.dist h j, [r]⟩
      | none =>
        let jobs := c.blocks.filter hasJobs
        (jobs.foldl (fun best j => match best with
          | none => some j
          | some b => if c.dist h j < c.dist h b then some j else some b) none).map fun j =>
          ⟨some gi, h, j, .car, people, c.dist h j, []⟩
  let stationTrips := match T.station with
    | none => []
    | some k => c.blocks.filterMap fun j =>
      if !T.stationReaches c j then none else
      let people := stationWorkersAt c T look j + shoppersAt (look j)
      if people = 0 then none else
      let rs := (T.routesOn c).filter fun r =>
        j != k && !T.isNeighbor c k j && c.stopsAt r k && c.stopsAt r j
      some ⟨none, k, j, .subway, people, c.dist k j, rs.take 1⟩
  residentTrips ++ stationTrips

/-- Total happiness of group `gi` in a layout. -/
def groupHappiness (c : Context) (s : Solution) (gi : Nat) : Int :=
  c.blocks.foldl (fun t h =>
    let look := seenFrom c s.transit h s.look
    ((List.range c.typeCount).filter fun k => (c.residentType k).group == gi).foldl (fun t k =>
      let rt := c.residentType k
      t + (typeResidents (look h) rt : Int) * happinessPerPerson rt.personality (factorsHad c s.transit look h)) t) 0

/-- Total happiness in a layout. -/
def totalHappiness (c : Context) (s : Solution) : Int :=
  c.blocks.foldl (fun t i => t + blockHappiness c s.transit (seenFrom c s.transit i s.look) i) 0

/-- Facts about block `i`, compared with the same layout where it is empty. -/
def blockReport (c : Context) (s : Solution) (i : Nat) : BlockReport :=
  let T := s.transit
  let view := seenFrom c T i s.look
  let without : Solution := { s with build := s.build.set i .empty }
  { block := i
    happiness := blockHappiness c T view i
    productivity := blockProductivity c T view i + blockSales c T view i
    jobs := (s.look i).jobs
    workers := jobsFilled c T view i
    crime := blockCrime c T view i
    moodImpact := totalHappiness c s - totalHappiness c without
    scoreImpact := scoreWith c s - scoreWith c without
    groupImpact := (List.range c.groupCount).map fun gi =>
      ⟨gi, groupHappiness c s gi - groupHappiness c without gi⟩ }

/-- Boardings and alightings at each stop of each route that runs. -/
def stopReports (c : Context) (s : Solution) : List StopReport :=
  (s.transit.routesOn c).flatMap fun r =>
    let rush (dir : Nat) := routeRush c s.transit s.look r dir
    let count (dir : Nat) (pick : Rush.State → List Nat) (b : Nat) : Nat :=
      (pick (rush dir)).getD ((c.stopsInOrder r dir).idxOf b) 0
    (c.stopsInOrder r 0).map fun b =>
      { route := r, block := b, boardings := count 0 (·.ons) b + count 1 (·.ons) b
        alightings := count 0 (·.offs) b + count 1 (·.offs) b }

/-- The fullest load of each bus of each route that runs. -/
def busReports (c : Context) (s : Solution) : List BusReport :=
  (s.transit.routesOn c).flatMap fun r => [0, 1].flatMap fun dir =>
    ((routeRush c s.transit s.look r dir).maxLoads.zip (List.range busesPerRush)).map fun (m, b) =>
      { route := r, direction := dir, bus := b, maxLoad := m, capacity := busCapacity }

/-- Riders still waiting after the last bus, on all routes that run. -/
def leftBehindAll (c : Context) (s : Solution) : Nat :=
  ((s.transit.routesOn c).map fun r =>
    (routeRush c s.transit s.look r 0).leftBehind + (routeRush c s.transit s.look r 1).leftBehind).sum

/-- The full report for a layout. -/
def evaluateWith (c : Context) (s : Solution) : Report :=
  let p := c.puzzle
  let T := s.transit
  let look := s.look
  let view (i : Nat) := seenFrom c T i look
  let residents : List ResidentReport := c.blocks.flatMap fun h =>
    (List.range c.typeCount).filterMap fun k =>
      let rt := c.residentType k
      let people := typeResidents (look h) rt
      if people = 0 then none else
      let has := factorsHad c T (view h) h
      let each := happinessPerPerson rt.personality has
      some { block := h, group := rt.group, type := rt.type, people, has, happinessEach := each,
             unhappy := decide (each < unhappyLine) }
  { cost := costOf p s
    happiness := totalHappiness c s
    productivity := c.blocks.foldl (fun t i => t + blockProductivity c T (view i) i) 0
    sales := c.blocks.foldl (fun t i => t + blockSales c T (view i) i) 0
    crime := c.blocks.map fun i => blockCrime c T (view i) i
    crimePenalty := c.blocks.foldl (fun t i => t + blockCrime c T (view i) i) 0
      + shortagePenalty c T look
    shortage := shortage c T look
    routes := routeReports c s
    stationRiders := stationRiders c T look
    stops := stopReports c s
    buses := busReports c s
    leftBehind := leftBehindAll c s
    trips := tripsFor c s
    residents
    blocks := c.blocks.map (blockReport c s)
    score := scoreWith c s }

/-- The full report for a layout. -/
def report (p : Puzzle) (s : Solution) : Report := evaluateWith (prepare p) s

/-- **The score of a layout.** -/
def score (p : Puzzle) (s : Solution) : Int := scoreWith (prepare p) s

end SevenBridges
