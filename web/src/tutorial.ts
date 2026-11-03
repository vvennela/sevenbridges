// The first-time tutorial: a short guided town with one speech bubble at a time.
// Each step points at one part of the screen and ends when the player does the
// thing it asks (or presses Next on the steps that only explain).

/** What the game reports to the tutorial after every change. */
export interface TutorialState {
  tool: string | null;
  edits: number;
  built: number;        // blocks with a building on them
  blocks: number;
  lens: string;
  routesOn: number;
  station: boolean;
  mode: "edit" | "built";
  rated: boolean;       // the rating has arrived after Build
}

type Side = "right" | "left" | "below" | "above" | "center";

interface Step {
  /** CSS selector of the part of the screen the bubble points at; none = the town itself. */
  at?: string;
  side: Side[];
  title: string;
  text: string;
  /** The step ends when this is true. No test = the step has a Next button. */
  done?: (s: TutorialState, start: TutorialState) => boolean;
  /** Show Next as well, for steps the player may want to skip past. */
  next?: boolean;
}

const STEPS: Step[] = [
  { at: "#town", side: ["right", "below"], title: "Meet your residents",
    text: "Each group of cats loves some things (a heart) and dislikes others (a red no sign). Hover an icon to read it. Here, the Elderly love parks, but Professionals don't." },
  { at: "#tools", side: ["above"], title: "Pick a building",
    text: "Choose Homes from the tray. Cats need somewhere to live before anything else.",
    done: (s) => s.tool === "housing" },
  { side: ["center"], title: "Build on a block",
    text: "Click a glowing block to build there. Click it again to add a floor; right-click to take one off.",
    done: (s, a) => s.edits > a.edits },
  { at: "#meter", side: ["left", "below"], title: "Fill your town",
    text: "Neighbors matter: what's next door decides how happy and how productive each block is. Build on the other blocks too, and keep an eye on the money left.",
    done: (s) => s.built >= s.blocks, next: true },
  { at: "#lenses", side: ["left", "below"], title: "Look through a lens",
    text: "Press Mood to see how happy each home is. Jobs, Transit and Air show the rest of the town's life.",
    done: (s) => s.lens !== "none", next: true },
  { at: "#transit", side: ["above"], title: "Connect the town",
    text: "Buses and the metro take cats to work. Each one must carry enough riders to pay for itself. Cars work too, but they bring traffic and smog.",
    done: (s, a) => s.routesOn !== a.routesOn || s.station !== a.station, next: true },
  { at: "#build", side: ["above", "left"], title: "Build it",
    text: "Press Build to see how your cats feel and get your rating.",
    done: (s) => s.mode === "built" && s.rated },
  { at: "#postcard", side: ["left", "below", "center"], title: "Your rating",
    text: "The card says what your cats enjoy and what to fix. The rating is out of 100, and 100 is the best plan possible for this town. Press Try for 100 to keep improving." },
];

const DONE_KEY = "sb-tutorial-done";

export class Tutorial {
  private step = -1;
  private start: TutorialState | null = null;
  private el = document.createElement("div");
  private focused: HTMLElement | null = null;
  /** Called when the tutorial ends, finished or skipped. */
  onEnd: () => void = () => {};

  constructor(parent: HTMLElement) {
    this.el.id = "tut";
    this.el.className = "tut hidden";
    this.el.setAttribute("role", "dialog");
    parent.appendChild(this.el);
    this.el.addEventListener("click", (e) => {
      const act = (e.target as HTMLElement).closest<HTMLElement>("[data-tut]")?.dataset.tut;
      if (act === "next") this.go(this.step + 1);
      else if (act === "skip") this.end();
    });
  }

  /** True when this device has not finished or skipped the tutorial yet (test runs skip it). */
  static wanted(): boolean {
    const q = new URLSearchParams(location.search);
    return !localStorage.getItem(DONE_KEY) && !q.has("test") && !q.has("nocoach");
  }

  get active() { return this.step >= 0; }

  begin(s: TutorialState) { this.go(0, s); }

  /** Report the game's state; moves on when the current step is done. */
  update(s: TutorialState) {
    if (!this.active) return;
    const st = STEPS[this.step];
    if (!this.start) this.start = s;
    if (st.done?.(s, this.start)) this.go(this.step + 1, s);
    this.last = s;
  }
  private last: TutorialState | null = null;

  end() {
    localStorage.setItem(DONE_KEY, "1");
    this.step = -1;
    this.el.classList.add("hidden");
    this.focus(null);
    this.onEnd();
  }

  private go(i: number, s: TutorialState | null = this.last) {
    if (i >= STEPS.length) { this.end(); return; }
    this.step = i;
    this.start = s;
    const st = STEPS[i];
    const last = i === STEPS.length - 1;
    const button = !st.done || st.next
      ? `<button class="btn primary small" data-tut="next">${last ? "Let's play" : st.done ? "Next" : "Got it"}</button>` : "";
    this.el.innerHTML = `
      <div class="tut-top"><span class="tut-n">${i + 1} of ${STEPS.length}</span>${last ? "" : `<button class="linkish" data-tut="skip">Skip tutorial</button>`}</div>
      <h3>${st.title}</h3><p>${st.text}</p>
      ${button ? `<div class="tut-btns">${button}</div>` : ""}`;
    this.el.classList.remove("hidden");
    this.el.classList.remove("pop");
    void this.el.offsetWidth;
    this.el.classList.add("pop");
    this.place();
  }

  private focus(el: HTMLElement | null) {
    if (this.focused === el) return;
    this.focused?.classList.remove("tut-focus");
    el?.classList.add("tut-focus");
    this.focused = el;
  }

  /** Put the bubble next to its target, on the first side with room. Called every frame. */
  place() {
    if (!this.active) return;
    const st = STEPS[this.step];
    const target = st.at ? document.querySelector<HTMLElement>(st.at) : null;
    const r = target && !target.classList.contains("hidden") ? target.getBoundingClientRect() : null;
    this.focus(r && r.width > 0 ? target : null);
    const W = window.innerWidth, H = window.innerHeight, gap = 14;
    const w = this.el.offsetWidth, h = this.el.offsetHeight;
    let x = (W - w) / 2, y = H * 0.32 - h / 2, side: Side = "center";
    if (r && r.width > 0) {
      for (const sd of st.side) {
        if (sd === "right" && r.right + gap + w <= W - 8) { x = r.right + gap; y = r.top + Math.min(40, r.height / 2 - h / 2); side = sd; break; }
        if (sd === "left" && r.left - gap - w >= 8) { x = r.left - gap - w; y = r.top + Math.min(40, r.height / 2 - h / 2); side = sd; break; }
        if (sd === "below" && r.bottom + gap + h <= H - 8) { x = r.left + r.width / 2 - w / 2; y = r.bottom + gap; side = sd; break; }
        if (sd === "above" && r.top - gap - h >= 8) { x = r.left + r.width / 2 - w / 2; y = r.top - gap - h; side = sd; break; }
        if (sd === "center") break;
      }
    }
    x = Math.max(8, Math.min(W - w - 8, x));
    y = Math.max(8, Math.min(H - h - 8, y));
    this.el.style.transform = `translate(${Math.round(x)}px, ${Math.round(y)}px)`;
    this.el.dataset.side = side;
  }
}
