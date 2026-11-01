import Lean.Data.Json
import Lean.Elab.Deriving.FromToJson
import SevenBridges.Solver

/-!
# JSON for talking to the frontend (DESIGN.md §9)

Not part of the rules. Buildings are sent as `{"kind": "housing", "stories": 2}`.
-/

namespace SevenBridges
open Lean

deriving instance ToJson, FromJson for Point
deriving instance ToJson, FromJson for SegmentKind
deriving instance ToJson, FromJson for Terrain
deriving instance ToJson, FromJson for Segment
deriving instance ToJson, FromJson for Block
deriving instance ToJson, FromJson for RoadMap
deriving instance ToJson, FromJson for Factor
deriving instance ToJson, FromJson for Personality
deriving instance FromJson for Group

/-- A group, with the usual personality's cares and hates repeated at the top
level (the frontend reads them there). -/
instance : ToJson Group where
  toJson g :=
    let usual := g.types.headD default
    Json.mkObj [("name", g.name), ("share", g.share), ("cares", toJson usual.cares),
      ("hates", toJson usual.hates), ("types", toJson g.types)]
deriving instance ToJson, FromJson for Route
deriving instance ToJson, FromJson for Mode

def Building.kindName : Building → String
  | .empty => "empty"
  | .housing _ => "housing"
  | .office _ => "office"
  | .shop _ => "shop"
  | .park => "park"
  | .bar => "bar"

instance : ToJson Building where
  toJson b := Json.mkObj [("kind", b.kindName), ("stories", b.stories)]

def heightOf : Nat → Except String Height
  | 1 => .ok .one
  | 2 => .ok .two
  | 3 => .ok .three
  | n => .error s!"stories must be 1, 2 or 3, not {n}"

instance : FromJson Building where
  fromJson? j := do
    let kind ← j.getObjValAs? String "kind"
    let stories : Nat := (j.getObjValAs? Nat "stories").toOption.getD 1
    match kind with
    | "empty" => pure .empty
    | "housing" => return .housing (← heightOf stories)
    | "office" => return .office (← heightOf stories)
    | "shop" => return .shop (← heightOf stories)
    | "park" => pure .park
    | "bar" => pure .bar
    | k => throw s!"unknown building kind {k}"

deriving instance ToJson, FromJson for Puzzle
deriving instance ToJson for Solution

/-- A solution from the frontend. `bridges` may be left out when the puzzle has
no bridge sites. -/
instance : FromJson Solution where
  fromJson? j := do
    let build ← j.getObjValAs? (List Building) "build"
    let routesOn ← j.getObjValAs? (List Bool) "routesOn"
    let station := (j.getObjValAs? (Option Nat) "station").toOption.join
    let bridges := (j.getObjValAs? (List Bool) "bridges").toOption.getD []
    return { build, routesOn, station, bridges }
deriving instance ToJson for Trip
deriving instance ToJson for RouteReport
deriving instance ToJson for ResidentReport
deriving instance ToJson for GroupChange
deriving instance ToJson for BlockReport
deriving instance ToJson for Report

end SevenBridges
