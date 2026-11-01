import SevenBridges.Generator
import SevenBridges.Json
open SevenBridges Lean

/-! Generator statistics (not part of the game).

`lake exe genstats [attempts] < maps.jsonl` (maps from `tools/maplines.mjs`):
for each map, a few generator attempts, each solved with a large step budget.
Prints the steps and time the proof took, the random-play ratings and whether
the level would be kept. -/

def say (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

def main (args : List String) : IO Unit := do
  let tries := (args.findSome? (·.toNat?)).getD 3
  let stdin ← IO.getStdin
  let mut k := 1
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match Json.parse line.trimAscii.toString with
    | .error e => say e
    | .ok j =>
      let m := (j.getObjValAs? RoadMap "map").toOption.get!
      let routes := (j.getObjValAs? (List Route) "routes").toOption.get!
      let mut r : Generator.Rng := ⟨k * 1000⟩
      for _ in [0:tries] do
        let (p, r') := Generator.attemptPuzzle r m routes "stats"
        r := r'
        let root := ((rootJobs p).map fun j => j.P.bound j.opts).foldl max 0
        let rootK := ((rootJobs p).map fun j => j.P.knapsackBound j.opts).foldl max 0
        let g := firstGuess (prepare p)
        if args.contains "caps" then
          for j in (rootJobs p).take 1 do
            say s!"  budget {p.budget} allowed {p.allowed.map fun b => s!"{b.kindName}{b.stories}"}"
            for row in j.P.optionValues j.opts do
              say s!"    {row}"
        say s!"  root bound {root} knapsack {rootK} first guess {score p g} transit groups {(rootJobs p).length}"
        let t0 ← IO.monoMsNow
        let (v, steps) := Generator.judge p 20000000
        let ms := (← IO.monoMsNow) - t0
        match v with
        | none => say s!"map {k} ({p.blockCount} blocks, {p.allowed.length + 1} choices): ran out ({steps} steps, {ms} ms)"
        | some v =>
          let t1 ← IO.monoMsNow
          let seeded := searchAll p (fun _ => true) ⟨v.best, v.bestScore, 20000000, 0⟩
          say s!"  seeded with the best: {seeded.steps} steps {(← IO.monoMsNow) - t1} ms"
          let rep := report p v.best
          say s!"map {k} ({p.blockCount} blocks, {p.allowed.length + 1} choices): {steps} steps {ms} ms; best {v.bestScore} empty {v.emptyScore}; random median {v.median} p95 {v.p95} ({v.rated} rated); kept {v.accepted}"
          say s!"  best: {v.best.build.map fun b => s!"{b.kindName}{b.stories}"} routes {v.best.routesOn} station {v.best.station} bridges {v.best.bridges}"
          say s!"  happiness {rep.happiness} productivity {rep.productivity} sales {rep.sales} crimePenalty {rep.crimePenalty} cars {rep.carTrips} cats {rep.cats.length}"
    k := k + 1
