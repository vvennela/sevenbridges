import SevenBridges.Branch
import SevenBridges.Demo
import SevenBridges.Generator
import SevenBridges.Json
open SevenBridges Lean

/-! How random valid layouts rate against the best (not part of the game).

Usage: `lake exe ratingdist [seed] < maps.jsonl` (maps from `tools/maplines.mjs`).
For Old Harbor and each map: solve, then rate up to 2000 random valid layouts
and print the median, p90, p95 and p99 rating, and the best layout. -/

def say (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

def pct (sorted : Array Nat) (q : Nat) : Nat :=
  if sorted.isEmpty then 0 else sorted[min (sorted.size - 1) (sorted.size * q / 100)]!

def study (label : String) (p : Puzzle) (seed : Nat) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := solveWithFuel p searchFuel
  let ms := (← IO.monoMsNow) - t0
  if r.fuel = 0 then say s!"{label}: solver ran out ({r.steps} steps, {ms} ms)"; return
  let best := r.best
  let c := prepare p
  let mut rng : Generator.Rng := ⟨seed⟩
  let mut ratings : Array Nat := #[]
  let mut tries := 0
  while ratings.size < 2000 && tries < 400000 do
    let (s, rng') := Generator.randomSolution rng p
    rng := rng'
    tries := tries + 1
    if decide (ValidWith c s) then ratings := ratings.push (rating p r.bestScore s)
  let sorted := ratings.qsort (· < ·)
  let rep := report p best
  say s!"{label}: best {r.bestScore} (empty {score p (emptyLayout p)}) steps {r.steps} {ms} ms; {ratings.size} valid of {tries} random"
  say s!"  ratings: median {pct sorted 50} p90 {pct sorted 90} p95 {pct sorted 95} p99 {pct sorted 99} max {sorted.back?.getD 0}"
  say s!"  best: {best.build.map Building.kindName |>.zip (best.build.map Building.stories)} routes {best.routesOn} station {best.station}"
  say s!"  happiness {rep.happiness} productivity {rep.productivity} sales {rep.sales} crime {rep.crime} shortage {rep.shortage} cost {rep.cost}/{p.budget}"
  say s!"  route riders {rep.routes.map (·.riders)} left behind {rep.leftBehind} fullest buses {rep.buses.map (·.maxLoad)} station riders {rep.stationRiders} bridges {best.bridges}"
  say s!"  groups: {p.groups.map Group.describe}"
  say s!"  per block: {rep.blocks.map fun b => (b.happiness, b.productivity, b.crime, b.scoreImpact)}"

def main (args : List String) : IO Unit := do
  let seed := (args.findSome? (·.toNat?)).getD 1
  study "Old Harbor" Demo.oldHarbor 99
  let stdin ← IO.getStdin
  let mut k := seed
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match Json.parse line.trimAscii.toString with
    | .error e => say e
    | .ok j =>
      let m := (j.getObjValAs? RoadMap "map").toOption.get!
      let routes := (j.getObjValAs? (List Route) "routes").toOption.get!
      let (p, r) := Generator.randomPuzzle ⟨k⟩ m routes "test"
      let (planted, _) := Generator.randomSolution r p
      let p := { p with budget := costOf p planted + 40 }
      study s!"map {k} ({p.blockCount} blocks)" p (k * 7 + 1)
    k := k + 1
