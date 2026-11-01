import SevenBridges.Rules.Valid

/-!
# The report sent to the frontend (DESIGN.md §9)

Not part of the rules: everything here is read off the rules for the player
to see. `report.cats` is exactly the simulated day that was scored.
-/

namespace SevenBridges
open Numbers

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

/-- How much a neighbor's value changes when a block is left empty. -/
structure NeighborChange where
  block : Nat
  change : Int
deriving Repr, DecidableEq, Inhabited

/-- Cars on one road segment: the driving cats of the blocks it borders. -/
structure StreetReport where
  segment : Nat
  cars : Nat
deriving Repr, DecidableEq, Inhabited

/-- Facts about one block in a layout. The impacts compare the layout with the
same layout where this block is left empty. -/
structure BlockReport where
  block : Nat
  happiness : Int
  /-- Productivity plus downtown jobs plus sales. -/
  productivity : Nat
  jobs : Nat
  /-- Jobs filled. -/
  workers : Nat
  crime : Nat
  /-- Cats of this block or next door drive. -/
  traffic : Bool
  /-- Traffic, and no park on the block or next door. -/
  polluted : Bool
  /-- Cats of this block and the blocks next to it who drive. -/
  cars : Nat
  /-- For each block next to this one: how much that block's value would
  change if this block were empty (negative: this block helps it). -/
  neighbors : List NeighborChange
  /-- Total happiness in the neighborhood, minus that with this block empty. -/
  moodImpact : Int
  /-- Score, minus the score with this block empty. -/
  scoreImpact : Int
  /-- For each group, its total happiness minus that with this block empty. -/
  groupImpact : List GroupChange
deriving Repr, DecidableEq, Inhabited

/-- One cat's day, for the animation. -/
structure CatReport where
  /-- A number for the cat: its block and its number there. -/
  id : String
  home : Nat
  group : Nat
  type : Nat
  mobility : Mobility
  day : DayKind
  eatsOut : Bool
  goesOut : Bool
  /-- Its happiness per person. -/
  happiness : Int
  legs : List Leg
deriving Repr, DecidableEq, Inhabited

/-- Everything the rules compute about a layout. -/
structure Report where
  cost : Nat
  happiness : Int
  /-- Productivity on all blocks (offices plus downtown jobs). -/
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
  /-- The simulated day of every cat, exactly as scored. -/
  cats : List CatReport
  /-- Car trips in the morning (cats who drive). -/
  carTrips : Nat
  /-- Cars on each road segment that has any. -/
  streets : List StreetReport
  score : Int
deriving Repr, Inhabited

/-- Facts about every bus route in a layout, in route order. -/
def routeReports (c : Context) (s : Solution) (d : List CatDay) : List RouteReport :=
  (List.range c.puzzle.routes.length).map fun i =>
    let on := s.routesOn.getD i false
    { on, riders := if on then routeRiders c s.transit d s.look i else 0 }

/-- Morning trips, for the older animation: one per cat that leaves home,
plus outside visitors from the metro station. -/
def tripsFor (c : Context) (s : Solution) (d : List CatDay) : List Trip :=
  let T := s.transit
  let look := s.look
  let catTrips := d.filterMap fun cd =>
    match cd.work with
    | some (.block j) => some ⟨some cd.who.traits.group, cd.who.home, j, cd.mode, residentsPerCat,
        c.dist cd.who.home j, cd.route.toList⟩
    | _ => none
  let stationTrips := match T.station with
    | none => []
    | some k => c.blocks.filterMap fun j =>
      if !T.stationReaches c j then none else
      let people := stationWorkersAt c T d look j + shoppersAt (look j)
      if people = 0 then none else
      let rs := (T.routesOn c).filter fun r =>
        j != k && !T.isNeighbor c k j && c.stopsAt r k && c.stopsAt r j
      some ⟨none, k, j, .metro, people, c.dist k j, rs.take 1⟩
  catTrips ++ stationTrips

/-- Total happiness of group `gi` in a layout. -/
def groupHappiness (c : Context) (s : Solution) (gi : Nat) : Int :=
  let d := simulate c s.transit s.look
  c.blocks.foldl (fun t h =>
    ((residentsOn c h (s.look h)).filter fun r => r.traits.group == gi).foldl (fun t r =>
      t + (residentsPerCat : Int) * happinessPerPerson (c.personalityOf r) (factorsHad c s.transit d s.look h)) t) 0

/-- Total happiness in a layout. -/
def totalHappiness (c : Context) (s : Solution) : Int :=
  let d := simulate c s.transit s.look
  c.blocks.foldl (fun t i => t + blockHappiness c s.transit d s.look i) 0

/-- Facts about block `i`, compared with the same layout where it is empty. -/
def blockReport (c : Context) (s : Solution) (d : List CatDay) (i : Nat) : BlockReport :=
  let T := s.transit
  let look := s.look
  let without : Solution := { s with build := s.build.set i .empty }
  { block := i
    happiness := blockHappiness c T d look i
    productivity := blockProductivity c T d look i + downtownOutput d i + blockSales c T look i
    jobs := (look i).jobs
    workers := jobsFilled c T d look i
    crime := blockCrime c T d look i
    traffic := traffic c T d i
    polluted := traffic c T d i && !(look i).isPark && !(T.neighborsOf c i).any fun j => (look j).isPark
    cars := (d.filter fun cd => cd.mode == .car
      && (cd.who.home == i || (T.neighborsOf c i).contains cd.who.home)).length
    neighbors :=
      let dw := simulate c without.transit without.look
      (T.neighborsOf c i).map fun j =>
        ⟨j, blockValue c T dw without.look j - blockValue c T d look j⟩
    moodImpact := totalHappiness c s - totalHappiness c without
    scoreImpact := scoreWith c s - scoreWith c without
    groupImpact := (List.range c.groupCount).map fun gi =>
      ⟨gi, groupHappiness c s gi - groupHappiness c without gi⟩ }

/-- Boardings and alightings at each stop of each route that runs. -/
def stopReports (c : Context) (s : Solution) (d : List CatDay) : List StopReport :=
  (s.transit.routesOn c).flatMap fun r =>
    let rush (dir : Nat) := routeRush c s.transit d s.look r dir
    let count (dir : Nat) (pick : Rush.State → List Nat) (b : Nat) : Nat :=
      (pick (rush dir)).getD ((c.stopsInOrder r dir).idxOf b) 0
    (c.stopsInOrder r 0).map fun b =>
      { route := r, block := b, boardings := count 0 (·.ons) b + count 1 (·.ons) b
        alightings := count 0 (·.offs) b + count 1 (·.offs) b }

/-- The fullest load of each bus of each route that runs. -/
def busReports (c : Context) (s : Solution) (d : List CatDay) : List BusReport :=
  (s.transit.routesOn c).flatMap fun r => [0, 1].flatMap fun dir =>
    ((routeRush c s.transit d s.look r dir).maxLoads.zip (List.range busesPerRush)).map fun (m, b) =>
      { route := r, direction := dir, bus := b, maxLoad := m, capacity := busCapacity }

/-- Riders still waiting after the last bus, on all routes that run. -/
def leftBehindAll (c : Context) (s : Solution) (d : List CatDay) : Nat :=
  ((s.transit.routesOn c).map fun r =>
    (routeRush c s.transit d s.look r 0).leftBehind + (routeRush c s.transit d s.look r 1).leftBehind).sum

/-- Each cat's day, for the animation. -/
def catReports (c : Context) (s : Solution) (d : List CatDay) : List CatReport :=
  d.map fun cd =>
    let r := cd.who
    { id := s!"{r.home}-{r.index}", home := r.home, group := r.traits.group, type := r.traits.type
      mobility := r.traits.mobility, day := r.traits.day, eatsOut := r.traits.eatsOut
      goesOut := r.traits.goesOut
      happiness := happinessPerPerson (c.personalityOf r) (factorsHad c s.transit d s.look r.home)
      legs := cd.legs }

/-- The full report for a layout. -/
def evaluateWith (c : Context) (s : Solution) : Report :=
  let p := c.puzzle
  let T := s.transit
  let look := s.look
  let d := simulate c T look
  let residents : List ResidentReport := c.blocks.flatMap fun h =>
    (List.range c.typeCount).filterMap fun k =>
      let rt := c.residentType k
      let people := residentsPerCat * ((residentsOn c h (look h)).filter fun r => r.traits.kind == k).length
      if people = 0 then none else
      let has := factorsHad c T d look h
      let each := happinessPerPerson rt.personality has
      some { block := h, group := rt.group, type := rt.type, people, has, happinessEach := each,
             unhappy := decide (each < unhappyLine) }
  { cost := costOf p s
    happiness := c.blocks.foldl (fun t i => t + blockHappiness c T d look i) 0
    productivity := c.blocks.foldl (fun t i => t + blockProductivity c T d look i + downtownOutput d i) 0
    sales := c.blocks.foldl (fun t i => t + blockSales c T look i) 0
    crime := c.blocks.map fun i => blockCrime c T d look i
    crimePenalty := c.blocks.foldl (fun t i => t + blockCrime c T d look i) 0
      + shortagePenalty c T d look
    shortage := shortage c T d look
    routes := routeReports c s d
    stationRiders := stationRiders c T d look
    stops := stopReports c s d
    buses := busReports c s d
    leftBehind := leftBehindAll c s d
    trips := tripsFor c s d
    residents
    blocks := c.blocks.map (blockReport c s d)
    cats := catReports c s d
    carTrips := (d.filter fun cd => cd.mode == .car).length
    -- Cars around each driver's home block, on land streets only (never on the river).
    streets := (List.range p.map.segments.length).filterMap fun k =>
      let seg := p.map.segments.getD k default
      if seg.terrain == .stream then none else
      let cars := (d.filter fun cd => cd.mode == .car
        && (p.map.block cd.who.home).sides.contains seg.side).length
      if cars = 0 then none else some ⟨k, cars⟩
    score := scoreWith c s }

/-- The full report for a layout. -/
def report (p : Puzzle) (s : Solution) : Report := evaluateWith (prepare p) s

/-- Reasons a solution is not valid, in words, for the player. -/
def problems (p : Puzzle) (s : Solution) : List String :=
  let r := report p s
  let c := prepare p
  (if decide (FitsPuzzle p s) then [] else ["the layout doesn't fit this puzzle"])
  ++ (if r.cost ≤ p.budget then [] else [s!"over budget: costs {r.cost}, budget {p.budget}"])
  ++ (((p.routes.zip r.routes).zip (List.range p.routes.length)).filterMap fun ((route, rr), i) =>
      if rr.on && !s.transit.bridgesReady c i then
        some s!"{route.name} crosses the river where no bridge is built"
      else if rr.on && rr.riders < minRouteRiders then
        some s!"{route.name} has only {rr.riders} riders a day (needs {minRouteRiders})"
      else none)
  ++ (if s.station.isSome && r.stationRiders < minStationRiders then
        [s!"the metro station has only {r.stationRiders} riders a day (needs {minStationRiders})"]
      else [])

end SevenBridges
