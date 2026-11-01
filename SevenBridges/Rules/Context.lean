import SevenBridges.Rules.Cats

/-!
# Things computed once per puzzle, and the transit choices (DESIGN.md §4, §15)
-/

namespace SevenBridges
open Numbers

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
  /-- The traits of each cat each block can hold (`catTraits`). -/
  traits : Array (Array Traits)
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
    residentTypes := (residentTypesOf p).toArray
    traits := Array.ofFn (n := n) fun h => Array.ofFn (n := maxCatsPerBlock) fun i => catTraits p h i }

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
/-- The traits of cat `i` on block `h` (`catTraits`, read from the table). -/
def traitsAt (c : Context) (h i : Nat) : Traits := (c.traits.getD h #[]).getD i default

end Context

/-! ## Transit choices -/

/-- The transit part of a solution: which routes are on, the metro station,
and which bridges are built. -/
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

/-- Residents of block `h` can get to block `j` without a car or the metro:
`h` is next to `j`, or one bus ride away. -/
def canReach (j h : Nat) : Bool := T.isNeighbor c j h || T.busLinked c j h

/-- The metro station is on block `i` or next to it. -/
def nearStation (i : Nat) : Bool :=
  T.station.any fun k => k == i || T.isNeighbor c i k

/-- **Metro reach**: block `j` is the station's block, next to it, or one bus
ride away. Residents of `j` can ride the metro downtown, and downtown
workers can reach offices on `j`. -/
def stationReaches (j : Nat) : Bool :=
  T.station.any fun k => k == j || T.canReach c k j

end Transit

end SevenBridges
