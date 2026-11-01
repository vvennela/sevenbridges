import SevenBridges.Rules.Score

/-!
# Facts about the morning rush (DESIGN.md §14.2)

For any capacity, number of buses, number of stops and parties:

- `run_maxLoad_le`: no bus ever carries more than its capacity,
- `run_all_off`: at the end nobody is on a bus, and every rider who got on got off,
- `run_boarded_add_leftBehind`: riders who got on plus riders left behind is
  everyone who waited (with at least one bus).
-/

namespace SevenBridges
namespace Rush

/-! ## Lists of counts -/

theorem sum_set (l : List Nat) (i v : Nat) :
    (l.set i v).sum + l.getD i 0 = l.sum + (if i < l.length then v else 0) := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      have := ih i
      simp only [List.set_cons_succ, List.sum_cons, List.getD_cons_succ, List.length_cons]
      by_cases hi : i < xs.length
      · rw [if_pos hi] at this; rw [if_pos (by omega)]; omega
      · rw [if_neg hi] at this; rw [if_neg (by omega)]; omega

theorem getD_le_sum (l : List Nat) (i : Nat) : l.getD i 0 ≤ l.sum := by
  have := sum_set l i 0
  split at this <;> omega

theorem sum_eq_zero_of (l : List Nat) (h : ∀ i < l.length, l.getD i 0 = 0) : l.sum = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h0 := h 0 (by simp)
    simp at h0
    have := ih fun i hi => by simpa using h (i + 1) (by simp; omega)
    simp [h0, this]

theorem foldl_range_succ {β : Type} (f : β → Nat → β) (k : Nat) (init : β) :
    (List.range (k + 1)).foldl f init = f ((List.range k).foldl f init) k := by
  simp [List.range_succ, List.foldl_append]

/-- A property kept by every step of a fold over `0, 1, …, k - 1`. -/
theorem foldl_range_inv {β : Type} (f : β → Nat → β) (P : β → Prop) (k : Nat)
    (step : ∀ b i, i < k → P b → P (f b i)) : ∀ init, P init → P ((List.range k).foldl f init) := by
  induction k with
  | zero => intro init h; simpa using h
  | succ k ih =>
    intro init h
    rw [foldl_range_succ]
    exact step _ _ (by omega) (ih (fun b i hi hb => step b i (by omega) hb) init h)

theorem sum_range_getD {α : Type} [Inhabited α] (f : α → Nat) :
    ∀ l : List α, ((List.range l.length).map fun i => f (l.getD i default)).sum = (l.map f).sum
  | [] => by simp
  | x :: xs => by
    have := sum_range_getD f xs
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      List.sum_cons, List.map]
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
    omega

/-! ## What stays true at every step -/

variable (cap buses n : Nat) (ps : List Party)

/-- The rush's bookkeeping is right: one count per party; the load is the riders
on board and fits the bus; riders who got off plus riders on board are those
who got on; riders waiting plus riders who got on are those who arrived; and
no bus has been fuller than its capacity. -/
def Inv (st : State) : Prop :=
  st.wait.length = ps.length ∧ st.aboard.length = ps.length ∧ st.load = st.aboard.sum
  ∧ st.load ≤ cap ∧ st.alighted + st.load = st.boarded ∧ st.wait.sum + st.boarded = st.arrived
  ∧ st.peak ≤ cap ∧ ∀ x ∈ st.maxLoads, x ≤ cap

theorem sum_map_zero {α : Type} : ∀ l : List α, (l.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: xs => by simp only [List.map_cons, List.sum_cons, sum_map_zero xs]

theorem inv_start : Inv cap ps (start n ps) := by
  refine ⟨by simp [start], by simp [start], ?_, Nat.zero_le _, rfl, ?_, Nat.zero_le _,
    by simp [start]⟩
  · simp only [start, sum_map_zero]
  · simp only [start, sum_map_zero]

theorem inv_getOff (s : Nat) (st : State) (i : Nat) (h : Inv cap ps st) : Inv cap ps (getOff n ps s st i) := by
  obtain ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩ := h
  unfold getOff
  split
  · have h1 := sum_set st.aboard i 0
    have h2 := getD_le_sum st.aboard i
    refine ⟨hw, by simp [ha], ?_, by dsimp only; omega, by dsimp only; omega, hwa, hp, hm⟩
    dsimp only
    split at h1 <;> omega
  · exact ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩

theorem inv_getOn (s : Nat) (st : State) (i : Nat) (h : Inv cap ps st) : Inv cap ps (getOn cap n ps s st i) := by
  obtain ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩ := h
  unfold getOn
  dsimp only
  split
  · have h1 := sum_set st.aboard i (st.aboard.getD i 0 + min (st.wait.getD i 0) (cap - st.load))
    have h2 := sum_set st.wait i (st.wait.getD i 0 - min (st.wait.getD i 0) (cap - st.load))
    have h3 : ¬ i < st.wait.length → st.wait.getD i 0 = 0 := fun hi => by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
    refine ⟨by simp [hw], by simp [ha], ?_, by dsimp only; omega, by dsimp only; omega, ?_,
      by dsimp only; omega, hm⟩
    · dsimp only
      by_cases hi : i < st.wait.length
      · rw [if_pos (by omega)] at h1; omega
      · rw [h3 hi, Nat.zero_min, Nat.add_zero, List.set_eq_of_length_le (by omega)]; exact hl
    · dsimp only
      by_cases hi : i < st.wait.length
      · rw [if_pos hi] at h2; omega
      · rw [h3 hi, Nat.zero_min, Nat.add_zero, List.set_eq_of_length_le (by omega)]; omega
  · exact ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩

theorem inv_atStop (st : State) (s : Nat) (h : Inv cap ps st) : Inv cap ps (atStop cap n ps st s) := by
  unfold atStop
  exact foldl_range_inv _ (Inv cap ps) _ (fun b i _ hb => inv_getOn cap n ps s b i hb) _
    (foldl_range_inv _ (Inv cap ps) _ (fun b i _ hb => inv_getOff cap n ps s b i hb) _ h)

/-- Arrivals before bus `b` keep the bookkeeping right, and add each party's
share to the riders who arrived. -/
theorem inv_arrive (b : Nat) (st : State) (h : Inv cap ps st) :
    Inv cap ps (arrive buses ps b st)
    ∧ (arrive buses ps b st).arrived
        = st.arrived + ((List.range ps.length).map fun i => share (ps.getD i default).people buses b).sum := by
  unfold arrive
  suffices ∀ k, k ≤ ps.length → Inv cap ps ((List.range k).foldl (arriveOne buses ps b) st)
      ∧ ((List.range k).foldl (arriveOne buses ps b) st).arrived
        = st.arrived + ((List.range k).map fun i => share (ps.getD i default).people buses b).sum from
    this _ (Nat.le_refl _)
  intro k
  induction k with
  | zero => intro _; exact ⟨h, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨hinv, harr⟩ := ih (by omega)
    rw [foldl_range_succ]
    simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    generalize (List.range k).foldl (arriveOne buses ps b) st = X at hinv harr ⊢
    obtain ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩ := hinv
    have h1 := sum_set X.wait k (X.wait.getD k 0 + share (ps.getD k default).people buses b)
    rw [if_pos (by omega)] at h1
    refine ⟨⟨by simp [arriveOne, hw], ha, hl, hc, hal, ?_, hp, hm⟩, ?_⟩
    · simp only [arriveOne]; omega
    · simp only [arriveOne]; omega

/-- The state after arrivals for bus `b`, with a fresh peak. -/
theorem inv_fresh (b : Nat) (st : State) (h : Inv cap ps st) :
    Inv cap ps { arrive buses ps b st with peak := 0 } := by
  obtain ⟨hw, ha, hl, hc, hal, hwa, _, hm⟩ := (inv_arrive cap buses ps b st h).1
  exact ⟨hw, ha, hl, hc, hal, hwa, Nat.zero_le _, hm⟩

theorem inv_runBus (st : State) (b : Nat) (h : Inv cap ps st) : Inv cap ps (runBus cap buses n ps st b) := by
  unfold runBus
  have h2 := foldl_range_inv (atStop cap n ps) (Inv cap ps) n
    (fun b' s _ hb => inv_atStop cap n ps b' s hb) _ (inv_fresh cap buses ps b st h)
  obtain ⟨hw, ha, hl, hc, hal, hwa, hp, hm⟩ := h2
  refine ⟨hw, ha, hl, hc, hal, hwa, hp, ?_⟩
  intro x hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hm x hx
  · exact hp

theorem inv_run : Inv cap ps (run cap buses n ps) :=
  foldl_range_inv _ (Inv cap ps) buses (fun b' i _ hb => inv_runBus cap buses n ps b' i hb) _
    (inv_start cap n ps)

/-! ## The bus is empty after every run -/

theorem getOff_last_aboard (s : Nat) (hs : s + 1 = n) (st : State) (i : Nat) :
    (getOff n ps s st i).aboard = st.aboard.set i 0 := by
  unfold getOff; rw [if_pos (Or.inr hs)]

/-- At the last stop `s`, after the riders of parties `0 … k - 1` got off,
none of them is on board. -/
theorem getOff_last_empties (s : Nat) (hs : s + 1 = n) (st : State) :
    ∀ k, ∀ i < k, ((List.range k).foldl (getOff n ps s) st).aboard.getD i 0 = 0 := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi
    rw [foldl_range_succ, getOff_last_aboard n ps s hs]
    generalize (List.range k).foldl (getOff n ps s) st = X at ih ⊢
    by_cases hik : k = i
    · subst hik
      by_cases hl : k < X.aboard.length
      · simp [List.getD_eq_getElem?_getD, List.getElem?_set, hl]
      · rw [List.set_eq_of_length_le (by omega)]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    · have := ih i (by omega)
      simp only [List.getD_eq_getElem?_getD] at this
      simp [List.getD_eq_getElem?_getD, List.getElem?_set, hik, this]

/-- Nobody gets on at the last stop `s`. -/
theorem foldl_getOn_last (s : Nat) (hs : s + 1 = n) (st : State) :
    ∀ k, (List.range k).foldl (getOn cap n ps s) st = st := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldl_range_succ, ih]
    unfold getOn; rw [if_neg (by omega)]

/-- After the last stop, the bus is empty. -/
theorem load_after_stops (st : State) (h : Inv cap ps st) (hn : 0 < n) :
    ((List.range n).foldl (atStop cap n ps) st).load = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [foldl_range_succ]
  have hinv := foldl_range_inv _ (Inv cap ps) k (fun b s _ hb => inv_atStop cap (k + 1) ps b s hb) _ h
  generalize (List.range k).foldl (atStop cap (k + 1) ps) st = st' at hinv ⊢
  simp only [atStop]
  rw [foldl_getOn_last cap (k + 1) ps k rfl]
  have hoff := foldl_range_inv _ (Inv cap ps) ps.length
    (fun b i _ hb => inv_getOff cap (k + 1) ps k b i hb) _ hinv
  obtain ⟨_, ha, hl, _⟩ := hoff
  rw [hl]
  apply sum_eq_zero_of
  intro i hi
  rw [ha] at hi
  exact getOff_last_empties (k + 1) ps k rfl st' _ i hi

theorem load_runBus (st : State) (b : Nat) (h : Inv cap ps st) (h0 : st.load = 0) :
    (runBus cap buses n ps st b).load = 0 := by
  unfold runBus
  by_cases hn : n = 0
  · subst hn
    simp only [List.range_zero, List.foldl_nil]
    -- arrivals don't change the load
    have : (arrive buses ps b st).load = st.load := by
      unfold arrive
      exact foldl_range_inv (arriveOne buses ps b) (fun x : State => x.load = st.load) _
        (fun _ _ _ hb => hb) _ rfl
    simp [this, h0]
  · exact load_after_stops cap n ps _ (inv_fresh cap buses ps b st h) (by omega)

/-! ## Riders who arrived -/

theorem arrived_runBus (st : State) (b : Nat) (h : Inv cap ps st) :
    (runBus cap buses n ps st b).arrived
      = st.arrived + ((List.range ps.length).map fun i => share (ps.getD i default).people buses b).sum := by
  unfold runBus
  rw [← (inv_arrive cap buses ps b st h).2]
  simp only
  refine foldl_range_inv (atStop cap n ps) (fun x : State => x.arrived = (arrive buses ps b st).arrived)
    n ?_ _ rfl
  intro x s _ hx
  rw [← hx]
  unfold atStop
  have hoff : ∀ y : State, ∀ i, (getOff n ps s y i).arrived = y.arrived := by
    intro y i; unfold getOff; split <;> rfl
  have hon : ∀ y : State, ∀ i, (getOn cap n ps s y i).arrived = y.arrived := by
    intro y i; unfold getOn; dsimp only; split <;> rfl
  have h1 := foldl_range_inv (getOff n ps s) (fun y : State => y.arrived = x.arrived) ps.length
    (fun y i _ hy => by rw [hoff]; exact hy) x rfl
  exact foldl_range_inv (getOn cap n ps s) (fun y : State => y.arrived = x.arrived) ps.length
    (fun y i _ hy => by rw [hon]; exact hy) _ h1

/-- `p × (b + 1) ÷ B` never goes down as `b` grows. -/
theorem div_mono (p B b : Nat) : p * b / B ≤ p * (b + 1) / B :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.le_succ _))

theorem sum_share (B b : Nat) :
    ∀ (l : List Nat), (l.map fun p => p * b / B).sum + (l.map fun p => share p B b).sum
      = (l.map fun p => p * (b + 1) / B).sum
  | [] => rfl
  | p :: rest => by
    have := sum_share B b rest
    have := div_mono p B b
    simp only [List.map_cons, List.sum_cons, share] at *
    omega

/-- After `b` buses, each party's first `people × b ÷ buses` riders have arrived. -/
theorem arrived_after (b : Nat) :
    ((List.range b).foldl (runBus cap buses n ps) (start n ps)).arrived
      = ((List.range ps.length).map fun i => (ps.getD i default).people * b / buses).sum := by
  induction b with
  | zero => simp [start, sum_map_zero]
  | succ b ih =>
    rw [foldl_range_succ, arrived_runBus cap buses n ps _ b
      (foldl_range_inv _ (Inv cap ps) b (fun b' i _ hb => inv_runBus cap buses n ps b' i hb) _
        (inv_start cap n ps)), ih]
    have := sum_share buses b ((List.range ps.length).map fun i => (ps.getD i default).people)
    simp only [List.map_map, Function.comp_def] at this
    exact this

/-! ## Main facts -/

/-- **No bus is ever fuller than its capacity.** -/
theorem run_maxLoad_le : ∀ x ∈ (run cap buses n ps).maxLoads, x ≤ cap :=
  (inv_run cap buses n ps).2.2.2.2.2.2.2

/-- **Everyone who got on got off**: at the end the bus is empty, and riders who
got off equal riders who got on. -/
theorem run_all_off :
    (run cap buses n ps).load = 0 ∧ (run cap buses n ps).alighted = (run cap buses n ps).boarded := by
  have hload : (run cap buses n ps).load = 0 := by
    unfold run
    apply foldl_range_inv _ (fun st => Inv cap ps st ∧ st.load = 0) buses
      (fun b i _ hb => ⟨inv_runBus cap buses n ps b i hb.1, load_runBus cap buses n ps b i hb.1 hb.2⟩)
      _ ⟨inv_start cap n ps, rfl⟩ |>.2
  have := (inv_run cap buses n ps).2.2.2.2.1
  exact ⟨hload, by omega⟩

/-- **Riders who got on plus riders left behind is everyone who waited**, when
at least one bus runs. -/
theorem run_boarded_add_leftBehind (hb : 0 < buses) :
    (run cap buses n ps).boarded + (run cap buses n ps).leftBehind = (ps.map (·.people)).sum := by
  have h1 := (inv_run cap buses n ps).2.2.2.2.2.1
  have h2 := arrived_after cap buses n ps buses
  unfold run State.leftBehind
  rw [← sum_range_getD (·.people) ps]
  have : (fun i => (ps.getD i default).people * buses / buses) = fun i => (ps.getD i default).people := by
    funext i; exact Nat.mul_div_cancel _ hb
  rw [this] at h2
  unfold run at h1
  omega

end Rush

/-! ## The same facts for every route of every layout -/

/-- **A bus never carries more than `busCapacity`**, on any route, in either
direction, in any layout. -/
theorem routeRush_maxLoad_le (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r dir : Nat) :
    ∀ x ∈ (routeRush c T d look r dir).maxLoads, x ≤ Numbers.busCapacity :=
  Rush.run_maxLoad_le _ _ _ _

/-- **Every rider who gets on gets off**: after the rush the buses are empty,
and boardings equal alightings. -/
theorem routeRush_all_off (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r dir : Nat) :
    (routeRush c T d look r dir).load = 0
    ∧ (routeRush c T d look r dir).alighted = (routeRush c T d look r dir).boarded :=
  Rush.run_all_off _ _ _ _

/-- **Riders who got on plus riders left behind is everyone who waited.** -/
theorem routeRush_boarded_add_leftBehind (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building) (r dir : Nat) :
    (routeRush c T d look r dir).boarded + (routeRush c T d look r dir).leftBehind
      = ((rushParties c T d look r dir).map (·.people)).sum :=
  Rush.run_boarded_add_leftBehind _ _ _ _ (by decide)

end SevenBridges
