/-!
# The morning rush on one bus route, in one direction (DESIGN.md §14.2)

A fixed, step-by-step process. Nothing in it is random.

- **Who waits where.** Riders come in parties. A party waits at stop `board`
  for stop `alight`. Stops are numbered along the bus's way: 0, 1, 2, …
- **Buses run on a schedule.** `buses` buses run one after another. Each
  party's riders arrive evenly over the rush: before bus `b`, a party of
  `people` gets `people × (b + 1) ÷ buses − people × b ÷ buses` more waiting
  riders, so over all buses exactly `people` arrive.
- **At each stop** the bus first lets off the riders for this stop (at the last
  stop, everyone), then lets on waiting riders who are going further, party by
  party, until it is full (`cap`).
- **Left behind.** Riders who don't fit wait for the next bus. Riders still
  waiting after the last bus are left behind.

The proofs are in `SevenBridges/BusProofs.lean`.
-/

namespace SevenBridges
namespace Rush

/-- Riders who wait at stop `board` for stop `alight`. -/
structure Party where
  board : Nat
  alight : Nat
  people : Nat
deriving Repr, Inhabited

/-- Riders of a party with `people` riders who arrive for bus `b` of `buses`. -/
def share (people buses b : Nat) : Nat := people * (b + 1) / buses - people * b / buses

/-- Add `v` to entry `i` of a list of counts. -/
def addAt (l : List Nat) (i v : Nat) : List Nat := l.set i (l.getD i 0 + v)

/-- The state of the rush. -/
structure State where
  /-- Riders of each party who are waiting. -/
  wait : List Nat
  /-- Riders of each party on the bus. -/
  aboard : List Nat
  /-- Riders on the bus. -/
  load : Nat
  /-- Riders who have got on so far. -/
  boarded : Nat
  /-- Riders who have got off so far. -/
  alighted : Nat
  /-- Riders who have arrived at their stop so far. -/
  arrived : Nat
  /-- Riders who got on at each stop. -/
  ons : List Nat
  /-- Riders who got off at each stop. -/
  offs : List Nat
  /-- The fullest load of each bus that has run. -/
  maxLoads : List Nat
  /-- The fullest load of the bus that is running. -/
  peak : Nat
deriving Repr, Inhabited

variable (cap buses n : Nat) (ps : List Party)

/-- Before anyone arrives: nobody waiting, an empty bus. -/
def start : State :=
  { wait := ps.map fun _ => 0, aboard := ps.map fun _ => 0, load := 0, boarded := 0,
    alighted := 0, arrived := 0, ons := List.replicate n 0, offs := List.replicate n 0,
    maxLoads := [], peak := 0 }

/-- At stop `s`, party `i` gets off if this is its stop or the last stop. -/
def getOff (s : Nat) (st : State) (i : Nat) : State :=
  if (ps.getD i default).alight = s ∨ s + 1 = n then
    let a := st.aboard.getD i 0
    { st with aboard := st.aboard.set i 0, load := st.load - a, alighted := st.alighted + a,
              offs := addAt st.offs s a }
  else st

/-- At stop `s`, waiting riders of party `i` get on if they wait here, are
going further, and this is not the last stop: as many as fit. -/
def getOn (s : Nat) (st : State) (i : Nat) : State :=
  let q := ps.getD i default
  if q.board = s ∧ s < q.alight ∧ s + 1 < n then
    let w := st.wait.getD i 0
    let take := min w (cap - st.load)
    { st with wait := st.wait.set i (w - take), aboard := st.aboard.set i (st.aboard.getD i 0 + take),
              load := st.load + take, boarded := st.boarded + take, peak := max st.peak (st.load + take),
              ons := addAt st.ons s take }
  else st

/-- The bus at stop `s`: riders get off, then riders get on. -/
def atStop (st : State) (s : Nat) : State :=
  let st := (List.range ps.length).foldl (getOff n ps s) st
  (List.range ps.length).foldl (getOn cap n ps s) st

/-- Riders of party `i` who arrive for bus `b` start waiting. -/
def arriveOne (b : Nat) (st : State) (i : Nat) : State :=
  let sh := share (ps.getD i default).people buses b
  { st with wait := st.wait.set i (st.wait.getD i 0 + sh), arrived := st.arrived + sh }

/-- Riders who arrive for bus `b`. -/
def arrive (b : Nat) (st : State) : State := (List.range ps.length).foldl (arriveOne buses ps b) st

/-- Bus `b` runs: riders arrive, then the bus stops at every stop in order. -/
def runBus (st : State) (b : Nat) : State :=
  let st := { arrive buses ps b st with peak := 0 }
  let st := (List.range n).foldl (atStop cap n ps) st
  { st with maxLoads := st.maxLoads ++ [st.peak] }

/-- **The rush**: every bus, one after another, along `n` stops. -/
def run : State := (List.range buses).foldl (runBus cap buses n ps) (start n ps)

/-- Riders still waiting after the last bus. -/
def State.leftBehind (st : State) : Nat := st.wait.sum

end Rush

#guard (Rush.run 10 2 3 [⟨0, 2, 30⟩]).boarded == 20
#guard (Rush.run 10 2 3 [⟨0, 2, 30⟩]).leftBehind == 10
#guard (Rush.run 10 2 3 [⟨0, 2, 30⟩]).maxLoads == [10, 10]

end SevenBridges
