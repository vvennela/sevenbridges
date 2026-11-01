import SevenBridges.BranchProofs
import SevenBridges.Demo
import SevenBridges.Generator
import SevenBridges.Json
open SevenBridges Lean

/-! Differential test: the fast solver (`solve`) and plain search
(`solvePlain`) find the same best score.

`lake exe difftest < maps.jsonl` (maps from `tools/maplines.mjs`): on each map,
several random puzzles small enough for plain search. Exits with code 1 on any
disagreement. The `#guard` below checks a tiny puzzle at build time. -/

/-- Old Harbor with all but blocks 0 and 2 fixed and four building choices. -/
def tinyHarbor : Puzzle :=
  { Demo.oldHarbor with
    fixed := [none, some (.shop .one), none, some (.office .two), some .bar, some (.housing .one), some .park]
    allowed := [.housing .one, .housing .two, .office .one, .park] }

#guard (solve tinyHarbor).map (score tinyHarbor) == (solvePlain tinyHarbor).map (score tinyHarbor)
#guard (solve tinyHarbor).isSome

def say (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush

/-- Compare both solvers on one puzzle. Returns whether they agree. -/
def compare (label : String) (p : Puzzle) : IO Bool := do
  let t0 ← IO.monoMsNow
  let fast := solve p
  let t1 ← IO.monoMsNow
  let plain := solvePlain p
  let t2 ← IO.monoMsNow
  let a := fast.map (score p)
  let b := plain.map (score p)
  let ok := a == b && a.isSome
  say s!"{label}: candidates {candidateCount p} fast {a} ({t1 - t0} ms) plain {b} ({t2 - t1} ms) {if ok then "AGREE" else "DISAGREE"}"
  return ok

def main : IO UInt32 := do
  let mut allOk ← compare "tinyHarbor" tinyHarbor
  let stdin ← IO.getStdin
  let mut seed := 1
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match Json.parse line.trimAscii.toString with
    | .error e => say e
    | .ok j =>
      let m := (j.getObjValAs? RoadMap "map").toOption.get!
      let routes := (j.getObjValAs? (List Route) "routes").toOption.get!
      for k in [3, 4, 5] do
        let (p, r) := Generator.randomPuzzle ⟨seed * 10 + k⟩ m routes "diff"
        -- Keep `k` random building choices so plain search stays small.
        let (allowed, r) := r.choose p.allowed k
        let p := { p with allowed }
        let (planted, _) := Generator.randomSolution r p
        let p := { p with budget := costOf p planted + 40 }
        if candidateCount p ≤ stepLimit then
          let ok ← compare s!"map {seed} ({p.blockCount} blocks, {k} choices)" p
          allOk := allOk && ok
    seed := seed + 1
  say (if allOk then "ALL AGREE" else "SOME DISAGREE")
  return if allOk then 0 else 1
