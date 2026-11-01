import SevenBridges.Rules.Day
import SevenBridges.Rules.Bus

/-!
# How a layout is scored (DESIGN.md §6, §15.3)

The layout and the simulation seed decide the cats' day (`Rules/Day.lean`).
Then, for each block:

- **Happiness** (homes): each cat adds 5 × its happiness per person: the sum
  of its personality's feelings about the factors its block has (a park next
  door, quiet, clean air, …).
- **Crime** (homes): each unhappy cat costs points, more the further below the
  unhappy line it is.
- **Productivity** (offices): filled jobs, filled by the cats who came to work
  there, plus downtown workers by metro. Offices do more next to other
  offices and next to a café or restaurant (lunch).
- **Downtown jobs** (homes): cats who commute downtown, by metro or by car.
- **Sales** (shops): customers who live next door or one bus ride away, up to
  what the shop can serve.

The **score** is the sum of block values, minus one neighborhood-wide penalty:
each home missing in a housing shortage (more jobs than homes and metro
workers) costs points.

The fast solver needs an upper bound on a block's value that it can compute
from what is still possible next to it: `SevenBridges/Bound.lean`.
-/

namespace SevenBridges
open Numbers

/-! ## Happiness -/

/-- The kinds of building that count for variety: housing, office, shop,
park, bar, food. -/
def kindTests : List (Building → Bool) :=
  [Building.isHousing, Building.isOffice, Building.isShop, Building.isPark, Building.isBar,
   Building.isFood]

/-- Factors that residents of block `h` have, on simulated day `d`. -/
def factorsHad (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (h : Nat) :
    List Factor :=
  let nextTo (test : Building → Bool) : Bool := (T.neighborsOf c h).any fun j => test (look j)
  Factor.all.filter fun
    | .parks => nextTo Building.isPark
    | .nightlife => nextTo Building.isBar
    | .quiet => !(nextTo Building.isLoud || traffic c T d h || T.nearStation c h)
    | .transit => T.served c h || T.nearStation c h
    | .shops => nextTo Building.isShop
    | .variety => decide ((kindTests.filter nextTo).length ≥ 3)
    | .food => nextTo Building.isFood
    | .cleanAir => !traffic c T d h || nextTo Building.isPark

/-- Happiness per person for residents with personality `t` and the factors
`had`. -/
def happinessPerPerson (t : Personality) (had : List Factor) : Int :=
  had.foldl (fun s f => s + (t.feeling f).value) 0

/-- The personality of a cat. -/
def Context.personalityOf (c : Context) (r : Resident) : Personality :=
  (c.residentType r.traits.kind).personality

/-- Happiness on block `i`: for each cat living there, 5 residents times its
happiness per person. -/
def blockHappiness (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (i : Nat) : Int :=
  (residentsOn c i (look i)).foldl (fun t r =>
    t + (residentsPerCat : Int) * happinessPerPerson (c.personalityOf r) (factorsHad c T d look i)) 0

/-- Crime on block `i`: for each cat below the unhappy line, `unhappyCost`
times how far below the line it is, times 5 residents. -/
def blockCrime (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (i : Nat) : Nat :=
  (residentsOn c i (look i)).foldl (fun t r =>
    t + unhappyCost * (unhappyLine - happinessPerPerson (c.personalityOf r) (factorsHad c T d look i)).toNat
          * residentsPerCat) 0

/-! ## Jobs and sales -/

/-- Residents who live next door to block `j` or one bus ride away: a shop's
customers. -/
def workersFor (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  (c.blocks.filter (T.canReach c j)).foldl (fun t h => t + (look h).residents) 0

/-- Downtown workers the metro brings to block `j`, if it is in metro reach:
the jobs the cats from town leave open, but at most `stationWorkersPerBlock`. -/
def stationWorkersAt (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (j : Nat) : Nat :=
  if T.stationReaches c j then min stationWorkersPerBlock ((look j).jobs - localWorkers d j)
  else 0

/-- Jobs filled on block `j`: by the cats who came to work there, as many as
there are jobs, plus downtown workers from the metro. -/
def jobsFilled (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (j : Nat) : Nat :=
  min (look j).jobs (localWorkers d j) + stationWorkersAt c T d look j

/-- Extra output of the office on block `j`, in percent: `officeBonusPerOffice`
for each office next to it, at most `officeBonusMax`, plus `lunchBonus` if a
café or restaurant is next to it. Other buildings get none. -/
def officeBonus (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  if (look j).isOffice then
    min officeBonusMax (officeBonusPerOffice * ((T.neighborsOf c j).filter fun k => (look k).isOffice).length)
      + (if (T.neighborsOf c j).any (fun k => (look k).isFood) then lunchBonus else 0)
  else 0

/-- Productivity on block `j`: `jobWorth` per filled job, plus the office bonus. -/
def blockProductivity (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (j : Nat) : Nat :=
  jobWorth * jobsFilled c T d look j * (100 + officeBonus c T look j) / 100

/-- Sales on block `j`: for a shop, `saleWorth` per customer, up to
`customersPerShopStory` per floor. Customers are residents next door or one
bus ride away, plus, if the shop is in metro reach, `shoppersPerShopStory`
outside shoppers per floor. -/
def blockSales (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) : Nat :=
  match look j with
  | .shop h => saleWorth * min (customersPerShopStory * h.stories)
      (workersFor c T look j + if T.stationReaches c j then shoppersPerShopStory * h.stories else 0)
  | _ => 0

/-- **The value of block `i`** on simulated day `d`: happiness + productivity
+ downtown jobs + sales − crime. -/
def blockValue (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (i : Nat) : Int :=
  blockHappiness c T d look i + blockProductivity c T d look i + downtownOutput d i
    + blockSales c T look i - blockCrime c T d look i

/-! ## The neighborhood-wide penalty -/

/-- More jobs than homes and metro workers: the size of the housing shortage. -/
def shortage (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) : Nat :=
  c.blocks.foldl (fun t j => t + (look j).jobs) 0
    - c.blocks.foldl (fun t h => t + (look h).residents) 0
    - c.blocks.foldl (fun t j => t + stationWorkersAt c T d look j) 0

/-- Each missing home in a housing shortage costs `shortageCost`. -/
def shortagePenalty (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) : Nat :=
  shortageCost * shortage c T d look

/-- **The score of a layout**: simulate the day, add up every block's value,
and take off the shortage penalty. -/
def scoreWith (c : Context) (s : Solution) : Int :=
  let d := simulate c s.transit s.look
  c.blocks.foldl (fun t i => t + blockValue c s.transit d s.look i) 0
    - shortagePenalty c s.transit d s.look

/-! ## Riders (for the transit rules) -/

/-- Outside shoppers the metro brings to building `b`, if it reaches it:
`shoppersPerShopStory` per shop floor. -/
def shoppersAt (b : Building) : Nat :=
  match b with
  | .shop h => shoppersPerShopStory * h.stories
  | _ => 0

/-- Daily riders at the metro station: cats who ride it downtown (5 residents
each), downtown workers, and outside shoppers on the blocks it reaches. -/
def stationRiders (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) : Nat :=
  if T.station.isNone then 0 else
  residentsPerCat * (d.filter fun cd => cd.mode == .metro).length
    + c.blocks.foldl (fun t j =>
      if T.stationReaches c j then t + stationWorkersAt c T d look j + shoppersAt (look j)
      else t) 0

/-- Who wants a bus in the morning rush, as (route, from block, to block,
people): each cat that rides the bus to work (5 residents), and downtown
workers the metro sends on to a block one bus ride away (on the first route
that links them). -/
def busTrips (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) :
    List (Nat × Nat × Nat × Nat) :=
  let residents := d.filterMap fun cd =>
    match cd.route, cd.work with
    | some r, some (.block j) => some (r, cd.who.home, j, residentsPerCat)
    | _, _ => none
  let outside := match T.station with
    | none => []
    | some k => c.blocks.filterMap fun j =>
      if j != k && !T.isNeighbor c k j && stationWorkersAt c T d look j > 0 then
        ((T.routesOn c).find? fun r => c.stopsAt r k && c.stopsAt r j).map fun r =>
          (r, k, j, stationWorkersAt c T d look j)
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
def rushParties (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r dir : Nat) :
    List Rush.Party :=
  let order := c.stopsInOrder r dir
  (busTrips c T d look).filterMap fun x =>
    let (r', h, j, people) := x
    let a := order.idxOf h
    let b := order.idxOf j
    if r' == r && a < b && b < order.length then some ⟨a, b, people⟩ else none

/-- **The morning rush on route `r` in direction `dir`** (`Rules/Bus.lean`):
`busesPerRush` buses of `busCapacity` seats each. -/
def routeRush (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r dir : Nat) :
    Rush.State :=
  Rush.run busCapacity busesPerRush (c.stopsInOrder r dir).length (rushParties c T d look r dir)

/-- Riders on route `r`: everyone who got on one of its buses in the morning
rush, in both directions. Riders left behind don't count. -/
def routeRiders (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r : Nat) : Nat :=
  (routeRush c T d look r 0).boarded + (routeRush c T d look r 1).boarded

/-! ## Costs -/

/-- Total cost of a layout: buildings on open blocks (fixed blocks are already
paid for), plus each route that is on and the metro station, built and run
for `years` years, plus each bridge built. -/
def costOf (p : Puzzle) (s : Solution) : Nat :=
  let buildCost := (List.range p.blockCount).foldl (fun t i =>
    if (p.fixedAt i).isSome then t else t + (s.build.getD i .empty).cost) 0
  let routesOnCount := (s.routesOn.filter id).length
  buildCost + routesOnCount * (routeBuildCost + routeYearlyCost * years)
    + (if s.station.isSome then stationBuildCost + stationYearlyCost * years else 0)
    + (s.bridges.filter id).length * bridgeCost

end SevenBridges
