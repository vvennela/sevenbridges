import SevenBridges.Rules.Map
import SevenBridges.Rules.Buildings
import SevenBridges.Rules.Culture

/-!
# Puzzles and solutions (DESIGN.md §3.2, §4, §7, §15)
-/

namespace SevenBridges

/-- A possible bus route: a path of intersections along streets. The bus stops
at every intersection on the path. -/
structure Route where
  name : String
  path : List Nat
deriving Repr, DecidableEq, Inhabited

/-- The street segments a route drives along, smaller intersection first. -/
def Route.sides (r : Route) : List (Nat × Nat) :=
  (r.path.zip (r.path.drop 1)).map fun (x, y) => (min x y, max x y)

/-- A puzzle. -/
structure Puzzle where
  name : String
  map : RoadMap
  /-- Buildings the player may choose for an open block. Empty is always allowed. -/
  allowed : List Building
  /-- Already-built blocks: entry `i` is `some b` if block `i` is fixed as `b`.
  Missing entries mean the block is open. Generated levels have none
  (`Generator.generate_no_fixed`); only the test fixture uses them. -/
  fixed : List (Option Building)
  /-- Bus routes the player can turn on. -/
  routes : List Route
  /-- The blocks along the metro line to downtown, from the edge of town
  inward. The metro station may be built on one of them. -/
  metroSites : List Nat
  /-- Where the metro line enters the town (for drawing only). -/
  metroEntry : Point := ⟨0, 0⟩
  /-- River segments where a bridge may be built: numbers of segments in
  `map.segments`. -/
  bridgeSites : List Nat
  groups : List Group
  /-- Budget in thousands of dollars. -/
  budget : Nat
  /-- The seed of the cat simulation: it decides each cat's traits
  (`Rules/Cats.lean`). -/
  simSeed : Nat := 0
deriving Repr, Inhabited

/-- A player's answer: one building per block (in block order), which routes are
on (in route order), where the metro station goes, if anywhere, and which
bridges are built (in `bridgeSites` order). -/
structure Solution where
  build : List Building
  routesOn : List Bool
  station : Option Nat
  bridges : List Bool
deriving Repr, DecidableEq, Inhabited

namespace Puzzle

def blockCount (p : Puzzle) : Nat := p.map.blockCount

/-- The fixed building on block `i`, if the block is fixed. -/
def fixedAt (p : Puzzle) (i : Nat) : Option Building := (p.fixed.getD i none)

/-- The choices for block `i`: only its building if it is fixed; otherwise
empty or any allowed building. -/
def choicesFor (p : Puzzle) (i : Nat) : List Building :=
  match p.fixedAt i with
  | some b => [b]
  | none => .empty :: p.allowed.filter (· != .empty)

/-- The choices for every block, in block order. -/
def choices (p : Puzzle) : List (List Building) :=
  (List.range p.blockCount).map p.choicesFor

end Puzzle

/-! ## Numbers used by the rules

All money is in thousands of dollars. Change these freely; no proof depends
on them. -/

namespace Numbers

/-- Years of transit operation the budget must cover. -/
def years : Nat := 10
/-- Cost to set up a bus route. -/
def routeBuildCost : Nat := 50
/-- Cost to run a bus route for a year. -/
def routeYearlyCost : Nat := 10
/-- Cost to build the metro station. -/
def stationBuildCost : Nat := 100
/-- Cost to run the metro station for a year. -/
def stationYearlyCost : Nat := 15
/-- Cost to build a bridge. -/
def bridgeCost : Nat := 120

/-- Fare per ride, in dollars. -/
def fare : Nat := 2
/-- Cost to run a bus route for a day, in dollars. -/
def routeDailyCost : Nat := 60
/-- Cost to run the metro station for a day, in dollars. -/
def stationDailyCost : Nat := 80

/-- Residents each cat stands for. -/
def residentsPerCat : Nat := 5

/-- Buses each route runs in each direction in the morning rush. -/
def busesPerRush : Nat := 3
/-- Seats on a bus. -/
def busCapacity : Nat := 15
/-- Riders a day a route needs to pay for itself: daily cost ÷ fare, rounded up. -/
def minRouteRiders : Nat := (routeDailyCost + fare - 1) / fare
/-- Riders a day the metro station needs to pay for itself. -/
def minStationRiders : Nat := (stationDailyCost + fare - 1) / fare

/-- Most downtown workers the metro brings to one office block. -/
def stationWorkersPerBlock : Nat := 20
/-- Outside shoppers the metro brings for each shop floor within its reach. -/
def shoppersPerShopStory : Nat := 10

/-- A resident whose happiness is below this is unhappy. -/
def unhappyLine : Int := 1
/-- Crime: points lost for each unhappy resident, for each point of happiness
they are below the line. -/
def unhappyCost : Nat := 2
/-- Points lost for each missing home in a housing shortage. -/
def shortageCost : Nat := 2

/-- Points for each filled job in the neighborhood. -/
def jobWorth : Nat := 5
/-- Points for each resident who rides the metro to a job downtown. -/
def metroJobWorth : Nat := 3
/-- Points for each resident who drives to a job downtown (a long commute). -/
def carJobWorth : Nat := 1
/-- Extra output of an office, in percent, for each office next to it. -/
def officeBonusPerOffice : Nat := 20
/-- Most extra output an office gets from offices next to it, in percent. -/
def officeBonusMax : Nat := 40
/-- Extra output of an office with a café or restaurant next to it (lunch), in percent. -/
def lunchBonus : Nat := 20
/-- Customers a shop can serve a day, per floor. -/
def customersPerShopStory : Nat := 20
/-- Points for each customer a shop serves. -/
def saleWorth : Nat := 2

end Numbers
end SevenBridges
