/-!
# The map: roads and blocks (DESIGN.md §2)

The map is a road network. Intersections have whole-number coordinates.
Road segments join two intersections. A block is the area enclosed by a loop
of intersections.
-/

namespace SevenBridges

/-- A road intersection, in whole-number map coordinates. -/
structure Point where
  x : Int
  y : Int
deriving Repr, DecidableEq, Inhabited

/-- What a segment carries. Only streets exist in the first version. -/
inductive SegmentKind
  | street
deriving Repr, DecidableEq, Inhabited

/-- What a segment is built on. -/
inductive Terrain
  | ground
  /-- The river runs along this segment. The blocks on its two sides are
  neighbors across it only if a bridge is built here (`Puzzle.bridgeSites`). -/
  | stream
deriving Repr, DecidableEq, Inhabited

/-- A road segment between intersections number `a` and `b`. -/
structure Segment where
  a : Nat
  b : Nat
  kind : SegmentKind := .street
  terrain : Terrain := .ground
deriving Repr, DecidableEq, Inhabited

/-- A block: the area enclosed by the loop of intersections `corners`. -/
structure Block where
  corners : List Nat
deriving Repr, DecidableEq, Inhabited

/-- A neighborhood map. -/
structure RoadMap where
  points : List Point
  segments : List Segment
  blocks : List Block
deriving Repr, Inhabited

/-- Stands for "no road path". Larger than any real distance. -/
def noPath : Nat := 1000000000

/-- Whole-number square root, rounded down. -/
def isqrt (n : Nat) : Nat := go (n + 1) 0
where
  go : Nat → Nat → Nat
    | 0, k => k
    | fuel + 1, k => if (k + 1) * (k + 1) ≤ n then go fuel (k + 1) else k

example : isqrt 24 = 4 := by decide
example : isqrt 25 = 5 := by decide

/-- The sides of a block: each pair of corners next to each other in its loop,
smaller number first. -/
def Block.sides (b : Block) : List (Nat × Nat) :=
  match b.corners with
  | [] => []
  | first :: _ =>
    let nexts := b.corners.drop 1 ++ [first]
    (b.corners.zip nexts).map fun (x, y) => (min x y, max x y)

/-- The two ends of a segment, smaller number first. -/
def Segment.side (s : Segment) : Nat × Nat := (min s.a s.b, max s.a s.b)

namespace RoadMap

/-- Position of intersection `i`. -/
def point (m : RoadMap) (i : Nat) : Point := m.points.getD i default

/-- Straight-line length of a segment, rounded down to a whole number. -/
def segmentLength (m : RoadMap) (s : Segment) : Nat :=
  let p := m.point s.a
  let q := m.point s.b
  isqrt ((p.x - q.x).natAbs ^ 2 + (p.y - q.y).natAbs ^ 2)

/-- Number of blocks. -/
def blockCount (m : RoadMap) : Nat := m.blocks.length

/-- Block `i` (an empty block if `i` is out of range). -/
def block (m : RoadMap) (i : Nat) : Block := m.blocks.getD i default

/-- The river runs along `side`. -/
def isRiver (m : RoadMap) (side : Nat × Nat) : Bool :=
  m.segments.any fun s => s.side == side && s.terrain == .stream

/-- Blocks `i` and `j` touch: they are different and share a road segment
(on land or on the river). Used only to check that a map is in one piece. -/
def Touch (m : RoadMap) (i j : Nat) : Prop :=
  i ≠ j ∧ ∃ side ∈ (m.block i).sides, side ∈ (m.block j).sides

instance (m : RoadMap) (i j : Nat) : Decidable (m.Touch i j) := by
  unfold Touch; infer_instance

/-- Blocks `i` and `j` are **neighbors over land**: they are different and
share a road segment that is not on the river. (Across the river, blocks are
neighbors only where a bridge is built: `Transit.isNeighbor`.) -/
def LandNeighbors (m : RoadMap) (i j : Nat) : Prop :=
  i ≠ j ∧ ∃ side ∈ (m.block i).sides, side ∈ (m.block j).sides ∧ m.isRiver side = false

instance (m : RoadMap) (i j : Nat) : Decidable (m.LandNeighbors i j) := by
  unfold LandNeighbors; infer_instance

/-! ## Shortest road distances -/

private def get (d : Array (Array Nat)) (i j : Nat) : Nat :=
  (d.getD i #[]).getD j noPath

private def put (d : Array (Array Nat)) (i j v : Nat) : Array (Array Nat) :=
  d.modify i (·.setIfInBounds j v)

/-- Shortest road distance between every pair of intersections
(Floyd–Warshall). `noPath` if there is no road path. -/
def intersectionDistances (m : RoadMap) : Array (Array Nat) := Id.run do
  let n := m.points.length
  let mut d : Array (Array Nat) :=
    Array.ofFn (n := n) fun i => Array.ofFn (n := n) fun j =>
      if i.val = j.val then 0 else noPath
  for s in m.segments do
    let len := m.segmentLength s
    if len < get d s.a s.b then
      d := put (put d s.a s.b len) s.b s.a len
  for k in [0:n] do
    for i in [0:n] do
      for j in [0:n] do
        let via := get d i k + get d k j
        if via < get d i j then
          d := put d i j via
  return d

/-- The center of a block: the average of its corners, rounded toward zero. -/
def center (m : RoadMap) (i : Nat) : Point :=
  let cs := (m.block i).corners.map m.point
  let n : Int := max 1 cs.length
  ⟨(cs.foldl (· + ·.x) 0) / n, (cs.foldl (· + ·.y) 0) / n⟩

/-- Straight-line distance between two points, rounded down. -/
def straight (p q : Point) : Nat :=
  isqrt ((p.x - q.x).natAbs ^ 2 + (p.y - q.y).natAbs ^ 2)

/-- Travel distance between every pair of blocks: from the center of one block
to one of its corners, along roads to a corner of the other block, then to its
center. The shortest such trip counts. 0 from a block to itself. -/
def blockDistances (m : RoadMap) : Array (Array Nat) :=
  let d := m.intersectionDistances
  Array.ofFn (n := m.blockCount) fun i => Array.ofFn (n := m.blockCount) fun j =>
    if i.val = j.val then 0 else
    (m.block i).corners.foldl (fun best a =>
      (m.block j).corners.foldl (fun best b =>
        min best (straight (m.center i) (m.point a) + get d a b
                  + straight (m.point b) (m.center j))) best) noPath

/-! ## Map checks (DESIGN.md §2.1)

These only make sure a map makes sense. The main theorem holds for every map,
checked or not. -/

/-- Blocks reachable from block 0 by moving between neighbors. -/
def reachableFromFirst (m : RoadMap) : List Nat := go m.blockCount [0] [0]
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, _, seen => seen
    | _, [], seen => seen
    | fuel + 1, i :: rest, seen =>
      let next := (List.range m.blockCount).filter fun j =>
        decide (m.Touch i j) && !seen.contains j
      go fuel (rest ++ next) (seen ++ next)

/-- Problems with a map, in words. An empty list means the map is fine. -/
def problems (m : RoadMap) : List String :=
  let segs := m.segments.map fun s => (min s.a s.b, max s.a s.b)
  let tooSmall := (List.range m.blockCount).filter fun i =>
    (m.block i).corners.length < 3
  let notRoad := (List.range m.blockCount).filter fun i =>
    (m.block i).sides.any fun side => !segs.contains side
  let badSegments := segs.filter fun side =>
    let count := (m.blocks.filter fun b => b.sides.contains side).length
    count != 1 && count != 2
  let badCorner := m.blocks.any fun b => b.corners.any (· ≥ m.points.length)
  let borderOf (side : Nat × Nat) := (m.blocks.filter fun b => b.sides.contains side).length
  let riverOnEdge := m.segments.filter fun s => s.terrain == .stream && borderOf s.side != 2
  (if m.blockCount < 5 || m.blockCount > 9 then ["the map must have 5 to 9 blocks"] else [])
  ++ tooSmall.map (fun i => s!"block {i} has fewer than 3 corners")
  ++ notRoad.map (fun i => s!"block {i} has a side that is not a road segment")
  ++ badSegments.map (fun (a, b) => s!"segment {a}-{b} does not border 1 or 2 blocks")
  ++ (if badCorner then ["a block uses an intersection that does not exist"] else [])
  ++ riverOnEdge.map (fun s => s!"river segment {s.a}-{s.b} is not between two blocks")
  ++ (if m.blockCount > 0 && m.reachableFromFirst.length != m.blockCount then
        ["the blocks are not all connected"] else [])

end RoadMap
end SevenBridges
