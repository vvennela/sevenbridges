// Shared colors and names for the world and the HUD (see UI-PLAN.md).

export const C = {
  meadow: "#B7DD98",
  meadowDeep: "#A6D486",
  road: "#E9E6F1",
  curb: "#F7F5FB",
  plot: "#F6F0E2",
  plotFixed: "#F1EEE6",
  lot: "#BDE29C",
  glow: "#F2FFE4",
  butter: "#FFE19A",
  coral: "#FF8B7B",
  sky: "#9CCAF4",
  mint: "#7FDDB4",
  lavender: "#CDB6F3",
  leaf: "#5FBF6A",
  leafLight: "#7FD07F",
  ink: "#2E3A59",
  sunflower: "#FFC83D",
  white: "#FFFDF8",
  window: "#6F8FC9",
  windowWarm: "#FFD98A",
  trunk: "#B98B6A",
  water: "#8FD3EA",
  shallows: "#C5ECF3",
  sand: "#F6E4B8",
  skyTop: "#BFE3FA",
  skyHaze: "#E6F3F5",
  peach: "#FFC59E",
  terracotta: "#E98A6A",
  metro: "#7C8CF0",
};

/** Resident group colors, in group order. */
/** Each group wears its own accessory color (tie, scarf, hat band). */
export const GROUP_COLORS = ["#E0A526", "#2A9D8F", "#8E5A9B", "#7A8B3A", "#D9604C"];
/** HUD avatar fur, per group, so faces differ a little. */
export const AVATAR_FUR = ["#E8914A", "#98A0AA", "#33343B", "#F2DDB3", "#8A6046"];
export const groupColor = (g: number) => GROUP_COLORS[g % GROUP_COLORS.length];

/** Bus route colors, in route order. */
export const ROUTE_COLORS = ["#FF9E7A", "#6FC3E8", "#B79BEF", "#F5B94E"];
export const SUBWAY_COLOR = "#7C8CF0";

export const KIND_NAME: Record<string, string> = {
  housing: "Homes", office: "Offices", shop: "Shops", food: "Food", park: "Park", bar: "Bar", empty: "Open lot",
};

/** Plain-language names of the culture factors in Lean's reports, and friendly
 * sentences about them ({G} is the group name, e.g. "Families"). */
export const FACTOR: Record<string, { name: string; love: string[]; wish: string[]; hate: string[] }> = {
  parks: {
    name: "Parks",
    love: ["{G} love having a park next door", "{G} adore the park around the corner", "{G} spend sunny afternoons in the park"],
    wish: ["{G} would love a park nearby", "{G} miss having green space close by"],
    hate: ["{G} would rather not live by a park", "{G} aren't fond of the park next door"],
  },
  nightlife: {
    name: "Nightlife",
    love: ["{G} love the bar around the corner", "{G} enjoy a night out close to home"],
    wish: ["{G} wish there were a bar nearby", "{G} would like somewhere to go out at night"],
    hate: ["{G} find the bar next door too noisy", "{G} lose sleep over the nearby bar"],
  },
  quiet: {
    name: "Quiet streets",
    love: ["{G} love how peaceful their street is", "{G} sleep soundly on their quiet street"],
    wish: ["{G} wish their street were calmer", "{G} are bothered by tall buildings or a bar next door"],
    hate: ["{G} think their street is a bit too sleepy", "{G} wish there were more going on outside"],
  },
  shortCommute: {
    name: "Short commute",
    love: ["{G} get to work in no time", "{G} love their short trip to work"],
    wish: ["{G} wish work were closer", "{G} spend too long getting to work"],
    hate: ["{G} don't mind a longer trip to work"],
  },
  walkability: {
    name: "Walking",
    love: ["{G} can walk to work, the shops and a park", "{G} love strolling everywhere"],
    wish: ["{G} wish they could walk to work, the shops and a park", "{G} would like to walk more and drive less"],
    hate: ["{G} would rather not walk everywhere"],
  },
  transit: {
    name: "Transit",
    love: ["{G} love having a bus or metro close by", "{G} hop on transit right outside"],
    wish: ["{G} wish a bus or metro stopped nearby", "{G} would love an easy ride into town"],
    hate: ["{G} don't like buses rumbling past", "{G} would rather transit stopped somewhere else"],
  },
  shops: {
    name: "Shops nearby",
    love: ["{G} love popping into the shop next door", "{G} enjoy having shops close by"],
    wish: ["{G} wish a shop were closer", "{G} have a long walk to buy groceries"],
    hate: ["{G} don't want shops on their doorstep", "{G} find the shops next door too busy"],
  },
};

FACTOR.variety = {
  name: "A mix nearby",
  love: ["{G} love the mix of places around them", "{G} enjoy a lively mix of buildings next door"],
  wish: ["{G} wish there were more kinds of places nearby", "{G} would like a livelier mix next door"],
  hate: ["{G} would rather have a plainer street"],
};
FACTOR.food = {
  name: "Food nearby",
  love: ["{G} love the café around the corner", "{G} eat out close to home"],
  wish: ["{G} wish there were a café nearby", "{G} would love somewhere to eat close by"],
  hate: ["{G} find the restaurant next door too busy"],
};
FACTOR.cleanAir = {
  name: "Clean air",
  love: ["{G} breathe easy here", "{G} love the fresh air"],
  wish: ["{G} wish the air were cleaner", "{G} are bothered by car fumes"],
  hate: ["{G} don't mind the traffic"],
};

/** One of several sentences, picked steadily (same facts, same sentence). */
export function say(list: string[] | undefined, group: string, salt: number): string {
  if (!list?.length) return "";
  let h = salt;
  for (const ch of group) h = (h * 31 + ch.charCodeAt(0)) >>> 0;
  return list[h % list.length].replace("{G}", group);
}
