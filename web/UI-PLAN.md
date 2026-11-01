# Seven Bridges: look and feel plan

Brief from the player: cute, appealing, heartwarming. You should *want* to play.
Clean and readable like Civilization VI: every thing on the map explains itself
with an icon and a hover, never a code like "A" or "B". Little people walking
around. The HUD must feel like a game, not a dashboard.

Skills to follow (in `.claude/skills/`): `threejs-game-ui-designer`
(read `references/ui-patterns.md`), `threejs-aaa-graphics-builder` (read
`references/visual-scorecard.md` and `authoring-recipes.md`),
`threejs-gameplay-systems` (read `references/game-feel.md`).

## Subject

A toy neighborhood on a planning table, full of small residents with opinions.
The player is the friendly planner. The fun is seeing people get happier.

## Color (world and UI share these)

| Name | Hex | Use |
|---|---|---|
| Meadow | `#B7DD98` | ground, verges |
| Lilac road | `#E9E6F1` | roads and sidewalks |
| Butter | `#FFE19A` | housing walls |
| Coral | `#FF8B7B` | housing roofs, hearts |
| Sky | `#9CCAF4` | offices |
| Mint | `#9FE2C6` | shops |
| Lavender | `#CDB6F3` | bars |
| Leaf | `#5FBF6A` | trees, parks |
| Ink | `#2E3A59` | text, outlines (never near-black) |
| Sunflower | `#FFC83D` | the Build button and stars, nothing else |

Group colors (people and their avatars): pick 5 friendly, distinct hues from
the list above plus `#F7A8C8` (blossom) and `#7FD3E8` (lagoon).

## Type

`Fredoka` (rounded, friendly) for the neighborhood name, the rating and button
labels; `Nunito` for everything else. Bundle them with `@fontsource` so the
game works offline. Sentence case everywhere. No all-caps labels, no
monospace, no italic accents.

## World

- **Fewer, bigger, readable things.** You must tell at a glance what is on a
  block and how tall it is.
  - Housing: a cluster of 3–5 cute houses around a small yard, all with the
    block's number of floors. Floors are countable: each floor is its own band
    with chunky windows.
  - Office: one chunky tower with clear floor bands.
  - Shop: a row of 2–3 shops with striped awnings.
  - Park: lawn, round trees, a pond, a bench.
  - Bar: a small warm building with string lights.
  - Empty open block: a soft dashed plot outline and a small sign post.
  - Fixed block: slightly paler, with a small ribbon on a sign post. No lock
    badge floating in the air.
- **Placement glow.** When a building type is picked, open blocks glow softly.
- **Surroundings.** Inland: meadow, trees and a few far pastel houses in light
  blue haze. River or coast on one side for some seeds. No gray cube city.
- **Light.** Warm late-afternoon key light, sky fill, soft shadows, ACES tone
  mapping. Readable, not foggy.
- **People.** Small round-headed residents in their group's color walk the
  trips Lean returns (walk, bus, car, subway), with a little bob. A few idle in
  parks. Buses carry them.
- **Feelings, live.** After every edit (evaluate already runs), homes whose
  residents are happy pop a small heart; unhappy ones get a tiny gray cloud.
  Use `report.residents` (`happinessEach`, `unhappy`, `has`). Feedback within
  about 100 ms of the reply. Still no rating until Build.
- **Transit on the map.** Bus routes are soft colored ribbons on the road with
  small bus-stop posts; click a route to turn it on or off. Possible station
  sites show a faint subway entrance; click one to build the station there;
  hover says "A subway station could go here · $400k · needs 60 riders a day".

## HUD

```
┌──────────────────────────┐                         ┌──────────────┐
│ Old Harbor               │                         │   ( 72 )     │  ring meter, stars at
│ (●) Families 60%  ♥🌳 ♥🤫 ✕🍺│                         │   ★★☆        │  50 / 80 / 100
│ (●) Students 40%  ♥🍺 ♥🚌   │                         │ ♥ 368  $ 20k left │
└──────────────────────────┘                         └──────────────┘

                       (map, nothing covering the middle)

          ┌───────────────────────────────────────────────────────┐
          │ [house] [office] [shop] [park] [bar] [clear] │ [bus][bus][M] │ ( Build ) │
          │  $100k   $120k   $80k   $40k  $60k          │                │           │
          └───────────────────────────────────────────────────────┘
```

- **Top-left, residents.** For each group: a round avatar in its color, name
  and share, and factor icons: a heart on what it loves, a small "no" mark on
  what it dislikes. Hover an icon for its name. This *is* the culture.
- **Top-right, rating.** A ring meter 0–100 with three stars at 50, 80 and 100.
  Before the first Build it shows "?" and "Build to see". Under it: a heart
  meter (happiness) and a coin meter (money left, red when over).
- **Bottom-center, toy tray.** Big (about 64 px) tiles with a small 3D render
  of the real building (render the same meshes to thumbnails), short name and
  price. Picked tile lifts up. Then bus-route tiles (bus in the route's color,
  on/off) and a subway tile. Then a big round Sunflower **Build** button.
- **Block hover card** near the cursor: "Housing · 2 floors" with ▲ and ▼
  buttons, plus "left-click raise · right-click lower". Fixed blocks say
  "Already built". So controls are visible, not hidden.

## Build moment (one orchestrated moment)

Buildings settle with a small bounce, residents walk out, the ring fills with
a count-up. A postcard slides in on the right:
- the rating with stars,
- one headline from the best fact in `report.residents`, e.g. "Families love
  living by the park",
- two or three notes: what people love (heart) and what they wish for, e.g.
  "Students wish a bar were closer", plus Lean's problems in friendly words,
- buttons "Keep building" and "Peek at the best plan".
At 100: hearts burst and "A perfect neighborhood".

## First play

Three small coach marks, once: "Pick a building", "Click a block (right-click
lowers)", "Press Build to see how residents feel".

## Rules for the code

- No game logic in TypeScript: costs, validity, rating, happiness and trips all
  come from Lean. Writing friendly sentences from Lean's facts is fine.
- Avoid the generic defaults the skills list: stat cards, cream panels,
  all-caps labels, pill buttons, monospace labels, middle-dot meta strings.
- Check 1440×900 and 1280×800; nothing clipped, wrapped or overlapping.
- Score the result with the visual scorecard before calling it done.
