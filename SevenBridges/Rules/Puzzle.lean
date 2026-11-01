import SevenBridges.Rules.Map
import SevenBridges.Rules.Buildings
import SevenBridges.Rules.Culture

/-!
# Puzzles and solutions (DESIGN.md §3.2, §4, §7)
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
  Missing entries mean the block is open. -/
  fixed : List (Option Building)
  /-- Bus routes the player can turn on. -/
  routes : List Route
  /-- Blocks where a subway station may be built. -/
  stationSites : List Nat
  /-- River segments where a bridge may be built: numbers of segments in
  `map.segments`. -/
  bridgeSites : List Nat
  groups : List Group
  /-- Budget in thousands of dollars. -/
  budget : Nat
deriving Repr, Inhabited

/-- A player's answer: one building per block (in block order), which routes are
on (in route order), where the subway station goes, if anywhere, and which
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

All money is in thousands of dollars, all distances are in map units (the map
is about 200 units across). Change these freely; no proof depends on them. -/

namespace Numbers

/-- Years of transit operation the budget must cover. -/
def years : Nat := 10
/-- Cost to set up a bus route. -/
def routeBuildCost : Nat := 50
/-- Cost to run a bus route for a year. -/
def routeYearlyCost : Nat := 10
/-- Cost to build the subway station. -/
def stationBuildCost : Nat := 250
/-- Cost to run the subway station for a year. -/
def stationYearlyCost : Nat := 15
/-- Cost to build a bridge. -/
def bridgeCost : Nat := 120

/-- Fare per ride, in dollars. -/
def fare : Nat := 2
/-- Cost to run a bus route for a day, in dollars. -/
def routeDailyCost : Nat := 60
/-- Cost to run the station for a day, in dollars. -/
def stationDailyCost : Nat := 120

/-- Riders a day a route needs to pay for itself: daily cost ÷ fare, rounded up. -/
def minRouteRiders : Nat := (routeDailyCost + fare - 1) / fare
/-- Riders a day the station needs to pay for itself. -/
def minStationRiders : Nat := (stationDailyCost + fare - 1) / fare

/-- Outside shoppers a station brings for each shop story within its reach. -/
def shoppersPerShopStory : Nat := 10

/-- A group whose happiness per person is below this is unhappy. -/
def unhappyLine : Int := 2
/-- Crime: points lost for each unhappy resident, for each point of happiness
they are below the line. -/
def unhappyCost : Nat := 2
/-- Points lost for each missing home in a housing shortage. -/
def shortageCost : Nat := 2

/-- Points for each filled job. -/
def jobWorth : Nat := 5
/-- Extra output of an office, in percent, for each office next to it. -/
def officeBonusPerOffice : Nat := 20
/-- Most extra output an office gets from offices next to it, in percent. -/
def officeBonusMax : Nat := 40
/-- Customers a shop can serve a day, per story. -/
def customersPerShopStory : Nat := 20
/-- Points for each customer a shop serves. -/
def saleWorth : Nat := 2

end Numbers
end SevenBridges
