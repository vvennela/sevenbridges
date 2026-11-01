// Shapes of the Lean binary's JSON replies (see web/fixtures/*.json).
// The frontend only reads these; it never computes any of the values.

export type Kind = "housing" | "office" | "shop" | "food" | "park" | "bar" | "empty";

export interface Building {
  kind: Kind;
  stories: number;
}

export interface Point { x: number; y: number }
export interface Segment { a: number; b: number; kind: string; terrain: string }
export interface Block { corners: number[] }
export interface MapData { points: Point[]; segments: Segment[]; blocks: Block[] }

export interface Route { name: string; path: number[] }
/** A personality within a group (e.g. "Night owls", 20%, loves nightlife). */
export interface Personality { name: string; share: number; cares: string[]; hates: string[] }
export interface Group { name: string; share: number; cares: string[]; hates: string[]; types?: Personality[] }

export interface Puzzle {
  name: string;
  allowed: Building[];
  budget: number;
  fixed: (Building | null)[];
  gatewayCommuters: number;
  groups: Group[];
  map: MapData;
  routes: Route[];
  stationSites: number[];
  /** Segment indices where a bridge over the river may be built. */
  bridgeSites?: number[];
  /** Version 2: the seed of this level's simulated day (Lean). */
  simSeed?: number;
  /** Version 2: Lean has proven this level's best plan. */
  verified?: boolean;
  /** Version 2: the metro line to downtown. `from` is the map-edge point it enters at;
   * `sites` are the blocks along it where a station may go (falls back to stationSites). */
  metro?: { from?: Point; sites?: number[] };
  /** Lean V2: the blocks along the metro line (where a station may go), and where the line enters. */
  metroSites?: number[];
  metroEntry?: Point;
}

export interface BuildOption { building: Building; cost: number; jobs: number; residents: number }

export interface Numbers {
  maxBusRoutesPerRoad: number;
  minNewRiders?: number;
  bridgeCost?: number;
  minRouteRiders: number;
  minStationRiders: number;
  routeCost: number;
  stationCost: number;
  years: number;
}

export interface PuzzleReply {
  candidateCount: number;
  culture: string[];
  fixedOptions: BuildOption[];
  numbers: Numbers;
  options: BuildOption[];
  puzzle: Puzzle;
}

export interface Solution {
  build: Building[];
  routesOn: boolean[];
  station: number | null;
  /** One per bridge site: built or not. */
  bridges?: boolean[];
}

export interface RouteReport { busiestStreet?: number; newRiders?: number; on: boolean; riders: number }

export type Mode = "walk" | "bus" | "car" | "subway";

export interface Trip {
  cost: number;
  fromBlock: number | null;
  toBlock: number | null;
  group: number;
  mode: Mode | string;
  people: number;
  routes: number[];
}

export interface Report {
  cost: number;
  crime: number[];
  crimePenalty: number;
  happiness: number;
  productivity: number;
  routes: RouteReport[];
  score: number;
  shortage: number;
  stationRiders: number;
  trips: Trip[];
  residents?: Resident[];
  /** Per-block facts (coming from Lean; the UI hides these when absent). */
  blocks?: BlockReport[];
  stops?: StopReport[];
  buses?: BusReport[];
  leftBehind?: number;
  /** Version 2: streets with cars on them (segment index, number of cars). */
  streets?: { segment: number; cars: number }[];
  /** Version 2: car trips in the morning. */
  carTrips?: number;
  /** Version 2: pollution per block (same order as the blocks). */
  pollution?: number[];
  /** Version 2: car traffic per street segment (same order as map.segments). */
  traffic?: number[];
  /** Version 2: Lean's simulated day, one entry per resident cat. */
  cats?: CatDay[];
}

/** One leg of a cat's simulated day: from block to block (null = outside town / downtown). */
export interface CatLeg {
  /** A block number, or "downtown" (off the map, where the metro and the downtown jobs are). */
  from: number | "downtown" | null;
  to: number | "downtown" | null;
  mode: Mode | "metro" | string;
  /** "commute" | "lunch" | "evening" | "home" (or a number 0..3). */
  phase: string | number;
  /** Bus legs: the route ridden. */
  route?: number;
}
export interface CatDay {
  id: number | string;
  home: number;
  group: number;
  type?: number;
  /** "walker" | "bus" | "driver" */
  mobility?: string;
  /** "works" | "studies" | "retired" */
  day?: string;
  eatsOut?: boolean;
  goesOut?: boolean;
  happiness?: number;
  legs: CatLeg[];
}

export interface BlockReport {
  block: number;
  happiness: number;
  productivity: number;
  jobs: number;
  workers: number;
  crime: number;
  /** City happiness with this building minus with this block empty. */
  moodImpact: number;
  /** Score with this building minus with this block empty. */
  scoreImpact: number;
  /** Version 2 (optional): pollution and traffic on this block. Lean sends booleans:
   * `traffic` = cats of this block or next door drive; `polluted` = traffic and no park next door. */
  pollution?: number;
  traffic?: number | boolean;
  polluted?: boolean;
  /** Cars that leave from this block. */
  cars?: number;
  /** Each neighbor: its value with THIS block empty minus its value now (this block's effect on it is −change). */
  neighbors?: { block: number; change: number }[];
  groupImpact: { group: number; change: number }[];
}
export interface StopReport { route: number; block: number; boardings: number; alightings: number }
export interface BusReport { route: number; direction: number; bus: number; maxLoad: number; capacity: number }

/** One resident group living on one housing block (from Lean's report). */
export interface Resident {
  block: number;
  group: number;
  /** Index into puzzle.groups[group].types, when Lean sends personalities. */
  type?: number;
  people: number;
  has: string[];          // factors this group gets here: parks, nightlife, quiet, shortCommute, walkability, transit, shops
  happinessEach: number;
  unhappy: boolean;
}

/** Rating out of 100 against the proven best (Lean: `rating`, `rating_le_100`). */
export interface Rating {
  rating: number;
  bestScore: number;
  theorem: string;
}

export interface EvalReply {
  rating?: Rating | null;
  problems: string[];
  report: Report;
  score: number;
  solution: Solution;
  valid: boolean;
}

export interface SolveReply {
  best: EvalReply | null;
  theorem?: string;
  reason?: string;
}

export type Reply<T> = { ok: true; data: T } | { ok: false; error: string };

export interface GenerateReply {
  generated: boolean;
  info: { attempts: number; work: number; workBudget: number; randomPlay?: { median: number; p95: number; rated: number } };
  puzzle?: PuzzleReply;
  /** Version 2: the best plan was proven before the level opens (Lean sends the theorem and seeds). */
  verified?: boolean | { theorem?: string; simSeed?: number; bestScore?: number };
  simSeed?: number;
  /** The map seed actually used (may differ from the one asked for). */
  seed?: number;
}

export type Request =
  | { cmd: "puzzle" }
  | { cmd: "demo" }
  | { cmd: "newPuzzle"; seed: number; size?: "easy" | "medium" | "hard" }
  | { cmd: "evaluate"; solution: Solution; rate?: boolean }
  | { cmd: "solve" };
