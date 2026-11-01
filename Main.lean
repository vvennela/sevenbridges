import SevenBridges.Json
import SevenBridges.Demo
import SevenBridges.Generator

/-!
# The game backend: one JSON request per line on stdin, one JSON reply per line
on stdout (DESIGN.md §9).

Requests:
- `{"cmd": "puzzle"}`: the current puzzle, the culture text and building prices.
- `{"cmd": "demo"}`: switch back to the hand-made demo puzzle and return it.
- `{"cmd": "evaluate", "solution": …}`: the full report for a layout.
- `{"cmd": "solve"}`: the proven best layout.
- `{"cmd": "generate", "map": …, "routes": […], "seed": n}`: make a new puzzle
  on a map from `tools/genmap.mjs`, and make it the current puzzle.
-/

open Lean SevenBridges

def numbersJson : Json := Json.mkObj [
  ("minRouteRiders", Numbers.minRouteRiders),
  ("minStationRiders", Numbers.minStationRiders),
  ("routeCost", Numbers.routeBuildCost + Numbers.routeYearlyCost * Numbers.years),
  ("stationCost", Numbers.stationBuildCost + Numbers.stationYearlyCost * Numbers.years),
  ("bridgeCost", Numbers.bridgeCost),
  ("years", Numbers.years)]

def optionJson (b : Building) : Json := Json.mkObj [
  ("building", toJson b), ("cost", b.cost), ("residents", b.residents), ("jobs", b.jobs)]

def puzzleJson (p : Puzzle) : Json := Json.mkObj [
  ("puzzle", toJson p),
  ("culture", toJson (p.groups.map Group.describe)),
  ("options", Json.arr ((Building.empty :: p.allowed).map optionJson).toArray),
  ("fixedOptions", Json.arr ((p.fixed.filterMap id).map optionJson).toArray),
  ("numbers", numbersJson),
  ("candidateCount", p.blockCount |> fun _ => candidateCount p)]

def reportJson (p : Puzzle) (s : Solution) : Json :=
  let r := report p s
  Json.mkObj [
    ("solution", toJson s),
    ("valid", decide (Valid p s)),
    ("problems", toJson (problems p s)),
    ("score", r.score),
    ("report", toJson r)]

/-- The current puzzle and, once known, its proven best layout. -/
structure Game where
  puzzle : Puzzle
  best : Option (Option Solution) := none

/-- The proven best layout, solving only the first time. -/
def Game.solved (g : Game) : Option Solution × Game :=
  match g.best with
  | some b => (b, g)
  | none => let b := solve g.puzzle; (b, { g with best := some b })

def ratingJson (g : Game) (s : Solution) : Json × Game :=
  let (best, g) := g.solved
  match best with
  | none => (Json.null, g)
  | some b =>
    let bestScore := score g.puzzle b
    (Json.mkObj [("rating", rating g.puzzle bestScore s), ("bestScore", bestScore),
      ("theorem", "SevenBridges.rating_le_100")], g)

def handle (g : Game) (req : Json) : Except String (Json × Game) := do
  let p := g.puzzle
  match ← req.getObjValAs? String "cmd" with
  | "puzzle" => return (puzzleJson p, g)
  | "demo" =>
    let g : Game := { puzzle := Demo.oldHarbor }
    return (puzzleJson g.puzzle, g)
  | "evaluate" =>
    let s ← req.getObjValAs? Solution "solution"
    let rate := (req.getObjValAs? Bool "rate").toOption.getD false
    let j := reportJson p s
    if rate then
      let (r, g) := ratingJson g s
      return (j.setObjVal! "rating" r, g)
    else return (j, g)
  | "solve" =>
    let (best, g) := g.solved
    match best with
    | none => return (Json.mkObj [("best", Json.null),
        ("reason", "the solver ran out of steps before it could prove a best layout")], g)
    | some s => return (Json.mkObj [
        ("best", (reportJson p s).setObjVal! "rating" (ratingJson g s).1),
        ("theorem", "SevenBridges.solve_is_best")], g)
  | "generate" =>
    let m ← req.getObjValAs? RoadMap "map"
    let routes ← req.getObjValAs? (List Route) "routes"
    let seed ← req.getObjValAs? Nat "seed"
    let problems := m.problems
    if !problems.isEmpty then throw s!"bad map: {problems}"
    let r := Generator.generate m routes s!"Neighborhood #{seed}" seed
    let info := Json.mkObj [("attempts", r.attempts), ("work", r.work),
      ("workBudget", Generator.generatorStepBudget)]
    match r.puzzle, r.verdict with
    | some q, some v => return (Json.mkObj [("generated", true), ("info", info),
        ("puzzle", puzzleJson q)], { puzzle := q, best := some (some v.best) })
    | _, _ => return (Json.mkObj [("generated", false), ("info", info)], g)
  | c => throw s!"unknown command {c}"

partial def loop (g : Game) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let (reply, g) := match Json.parse line.trimAscii.toString >>= handle g with
    | .ok (j, g') => (Json.mkObj [("ok", true), ("data", j)], g')
    | .error e => (Json.mkObj [("ok", false), ("error", e)], g)
  stdout.putStrLn reply.compress
  stdout.flush
  loop g stdin stdout

def main : IO Unit := do
  loop { puzzle := Demo.oldHarbor } (← IO.getStdin) (← IO.getStdout)
