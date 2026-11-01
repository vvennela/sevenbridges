import SevenBridges.Demo.Map
import SevenBridges.Solver
import SevenBridges.Rules.Report

/-!
# A hand-made demo puzzle, with tests (DESIGN.md §8.3)
-/

namespace SevenBridges.Demo

/-- "Old Harbor", a test fixture (players never see it): 7 blocks, two of them
already built. A river cuts blocks 0
and 4 off from the rest; bridges can be built at three places. -/
def oldHarbor : Puzzle where
  name := "Old Harbor"
  map := demoMap
  allowed := [.housing .one, .housing .two, .housing .three,
              .office .one, .office .two, .shop .one, .park, .bar]
  fixed := [none, none, none, some (.office .two), none, none, some .park]
  routes := demoRoutes
  metroSites := [0, 1, 2]
  bridgeSites := demoBridgeSites
  groups := [
    { name := "Families", share := 60, types := [
        { name := "Families", share := 80, cares := [.parks, .quiet], hates := [.nightlife] },
        { name := "Night owls", share := 20, cares := [.parks, .quiet, .nightlife], hates := [] }] },
    { name := "Students", share := 40, types := [
        { name := "Students", share := 70, cares := [.nightlife, .transit], hates := [] },
        { name := "Drivers", share := 30, cares := [.nightlife], hates := [.transit] }] }]
  budget := 900
  simSeed := 7

-- The map passes every map check.
#guard demoMap.problems == []
-- The empty layout is valid and costs nothing.
#guard decide (Valid oldHarbor (emptyLayout oldHarbor))
#guard (report oldHarbor (emptyLayout oldHarbor)).cost == 0

/-- A reasonable-looking layout, used in tests below. -/
def sampleLayout : Solution :=
  { build := [.housing .two, .shop .one, .housing .two, .office .two, .bar,
              .housing .one, .park]
    routesOn := [true, false]
    station := none
    bridges := [true, false, false] }

#guard decide (FitsPuzzle oldHarbor sampleLayout)

/-! ## The river -/

/-- No bridges built, and the first bridge (between blocks 0 and 3) built. -/
def noBridges : Transit := ⟨[false, false], none, [false, false, false]⟩
def firstBridge : Transit := ⟨[false, false], none, [true, false, false]⟩

-- Blocks 0 and 3 share only a river segment: they are neighbors only with the
-- bridge built.
#guard !(noBridges.isNeighbor (prepare oldHarbor) 0 3)
#guard firstBridge.isNeighbor (prepare oldHarbor) 0 3
#guard firstBridge.isNeighbor (prepare oldHarbor) 3 0
-- Blocks 0 and 4 share a road on land: neighbors either way.
#guard noBridges.isNeighbor (prepare oldHarbor) 0 4
-- Every river segment a route drives along is a bridge site, so every route
-- can run once its bridges are built.
#guard (prepare oldHarbor).routeBlocked.all (· == false)
-- Crosstown needs the first bridge, Northside the third.
#guard (prepare oldHarbor).bridgesFor 0 == [0]
#guard (prepare oldHarbor).bridgesFor 1 == [2]



/-! ## The rules reject bad solutions -/

-- Over budget: 3-story housing everywhere open, plus the station and both routes.
def tooExpensive : Solution :=
  { build := [.housing .three, .housing .three, .housing .three, .office .two,
              .housing .three, .housing .three, .park]
    routesOn := [true, true], station := some 1, bridges := [true, true, true] }
#guard !decide (Valid oldHarbor tooExpensive)
#guard (report oldHarbor tooExpensive).cost > oldHarbor.budget

-- A building the puzzle doesn't allow (3-story office).
def notAllowed : Solution := { sampleLayout with build := sampleLayout.build.set 0 (.office .three) }
#guard !decide (Valid oldHarbor notAllowed)

-- Changing a fixed block (block 6 must stay a park).
def changedFixed : Solution := { sampleLayout with build := sampleLayout.build.set 6 .bar }
#guard !decide (Valid oldHarbor changedFixed)

-- A metro station next to nothing: no jobs, shops or bars in reach, so no riders.
def lonelyStation : Solution := { emptyLayout oldHarbor with station := some 1 }
#guard !decide (Valid oldHarbor lonelyStation)
#guard (report oldHarbor lonelyStation).stationRiders < Numbers.minStationRiders

-- Crosstown on, without the bridge it needs.
def noBridgeBus : Solution := { sampleLayout with bridges := [false, false, false] }
#guard !decide (Valid oldHarbor noBridgeBus)
#guard (problems oldHarbor noBridgeBus).contains "Crosstown crosses the river where no bridge is built"

-- A bus route with nobody to carry.
def emptyBus : Solution :=
  { emptyLayout oldHarbor with routesOn := [false, true], bridges := [false, false, true] }
#guard !decide (Valid oldHarbor emptyBus)

end SevenBridges.Demo
