import SevenBridges.Branch
import SevenBridges.Demo
import SevenBridges.Generator
import SevenBridges.Json
open SevenBridges Lean

/-! Timing for the solver (not part of the game).

Usage: `node -e '…' | lake exe bbtime [plain]`, one JSON `{map, routes}` per
line on stdin (see `tools/maplines.mjs`). With `plain`, also runs the plain
solver and checks the scores agree. -/

def say (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

def timeIt (label : String) (p : Puzzle) (fuel : Nat := searchFuel) : IO (Search × Nat) := do
  let t0 ← IO.monoMsNow
  let r := solveWithFuel p fuel
  let ms := (← IO.monoMsNow) - t0
  say s!"{label}: score {r.bestScore} steps {r.steps} done {decide (r.fuel > 0)} time {ms} ms"
  return (r, ms)

/-- Experiment: polish the quick pass's best with local search before the
parallel phase. -/
def searchPolished (p : Puzzle) (qf : Nat) (start : Search) : Search :=
  let js := jobs p
  let quick := runInTurn (fun _ => true) js { start with fuel := min qf start.fuel }
  if quick.fuel > 0 then quick else
  let c := prepare p
  let (b, v) := (List.range 4).foldl (fun sv _ => improveOnce c sv) (quick.best, quick.bestScore)
  runTogether (fun _ => true) p { quick with best := b, bestScore := v, fuel := start.fuel - quick.steps }

def main (args : List String) : IO Unit := do
  let _ ← timeIt "oldHarbor" Demo.oldHarbor
  let stdin ← IO.getStdin
  let mut seed := (args.findSome? (·.toNat?)).getD 1
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match Json.parse line.trimAscii.toString with
    | .error e => say e
    | .ok j =>
      let m := (j.getObjValAs? RoadMap "map").toOption.get!
      let routes := (j.getObjValAs? (List Route) "routes").toOption.get!
      let (p, r) := Generator.randomPuzzle ⟨seed⟩ m routes "test"
      let (planted, _) := Generator.randomSolution r p
      let p := { p with budget := costOf p planted + 40 }
      let lens := p.choices.map List.length
      let (res, _) ← timeIt s!"blocks {p.blockCount} choices {lens.foldl max 0} transits {(transitGroups (prepare p)).flatten.length}" p
        (if args.contains "seeded" || args.contains "polish" then 30000000 else searchFuel)
      if args.contains "polish" then
        for qf in [20000, 200000] do
          let t0 ← IO.monoMsNow
          let r := searchPolished p qf (startSearch p 30000000)
          say s!"  polished (quick {qf}): score {r.bestScore} steps {r.steps} done {decide (r.fuel > 0)} time {(← IO.monoMsNow) - t0} ms"
      if args.contains "seeded" then
        let t0 ← IO.monoMsNow
        let r := searchAll p (fun _ => true) ⟨res.best, res.bestScore, 30000000, 0⟩
        say s!"  seeded with the best: score {r.bestScore} steps {r.steps} done {decide (r.fuel > 0)} time {(← IO.monoMsNow) - t0} ms"
      if args.contains "plain" then
        let t0 ← IO.monoMsNow
        match bestOf (·.2) (scoredValid p) with
        | some (_, v) =>
          say s!"  plain: score {v} time {(← IO.monoMsNow) - t0} ms {if v == res.bestScore then "AGREE" else "DISAGREE"}"
        | none => say "  plain: none"
    seed := seed + 1
