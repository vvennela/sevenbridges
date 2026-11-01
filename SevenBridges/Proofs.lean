import SevenBridges.Solver

/-!
# The solver returns the best valid solution (DESIGN.md §8.1)
-/

namespace SevenBridges

/-! ## Listing candidates misses nothing -/

theorem mem_allPicks {α : Type} (ls : List (List α)) (l : List α) :
    l ∈ allPicks ls ↔ l.length = ls.length ∧ ∀ pair ∈ l.zip ls, pair.1 ∈ pair.2 := by
  induction ls generalizing l with
  | nil => cases l <;> simp [allPicks]
  | cons xs rest ih =>
    cases l with
    | nil => simp [allPicks]
    | cons y t =>
      simp only [allPicks, List.mem_flatMap, List.mem_map, List.length_cons,
        List.zip_cons_cons, List.mem_cons, forall_eq_or_imp, ih]
      constructor
      · rintro ⟨x, hx, t', ⟨hlen, hall⟩, heq⟩
        simp only [List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact ⟨by omega, hx, hall⟩
      · rintro ⟨hlen, hy, hall⟩
        exact ⟨y, hy, t, ⟨by omega, hall⟩, rfl⟩

theorem mem_allSwitches (n : Nat) (l : List Bool) : l ∈ allSwitches n ↔ l.length = n := by
  induction n generalizing l with
  | zero => cases l <;> simp [allSwitches]
  | succ n ih =>
    cases l with
    | nil => simp [allSwitches]
    | cons b t => cases b <;> simp [allSwitches, ih]

/-- Every solution that fits the puzzle is a candidate. -/
theorem mem_candidates {p : Puzzle} {s : Solution} (h : FitsPuzzle p s) :
    s ∈ candidates p := by
  obtain ⟨hlen, hpick, hroutes, hstation, hbridges⟩ := h
  have hchoices : p.choices.length = p.blockCount := by simp [Puzzle.choices]
  simp only [candidates, List.mem_flatMap, List.mem_map, List.mem_cons]
  refine ⟨s.build, (mem_allPicks _ _).2 ⟨by omega, hpick⟩,
    s.routesOn, (mem_allSwitches _ _).2 hroutes, s.station, ?_,
    s.bridges, (mem_allSwitches _ _).2 hbridges, rfl⟩
  cases hs : s.station with
  | none => simp
  | some k => simp_all

/-! ## Picking the best -/

theorem bestOf_mem {α : Type} (f : α → Int) :
    ∀ (l : List α) (x : α), bestOf f l = some x → x ∈ l
  | [], _, h => by simp [bestOf] at h
  | y :: ys, x, h => by
    simp only [bestOf] at h
    split at h
    · simp_all
    · rename_i z hz
      have := bestOf_mem f ys z hz
      split at h <;> simp_all

theorem bestOf_eq_none {α : Type} (f : α → Int) (l : List α) :
    bestOf f l = none ↔ l = [] := by
  cases l with
  | nil => simp [bestOf]
  | cons y ys =>
    simp only [bestOf, reduceCtorEq, iff_false]
    split
    · simp
    · split <;> simp

theorem bestOf_max {α : Type} (f : α → Int) :
    ∀ (l : List α) (x : α), bestOf f l = some x → ∀ y ∈ l, f y ≤ f x
  | [], _, h => by simp [bestOf] at h
  | y :: ys, x, h => by
    simp only [bestOf] at h
    split at h
    · rename_i hnone
      cases h
      intro w hw
      cases hw with
      | head => exact Int.le_refl _
      | tail _ hw =>
        have := (bestOf_eq_none f ys).1 hnone
        subst this
        cases hw
    · rename_i z hz
      have hmax := bestOf_max f ys z hz
      intro w hw
      split at h
      · cases h
        cases hw with
        | head => omega
        | tail _ hw => exact hmax w hw
      · cases h
        cases hw with
        | head => exact Int.le_refl _
        | tail _ hw => have := hmax w hw; omega

/-! ## The scored list -/

/-- The cost in the report is `costOf`. -/
theorem report_cost (p : Puzzle) (s : Solution) : (report p s).cost = costOf p s := rfl

@[simp] theorem prepare_puzzle (p : Puzzle) : (prepare p).puzzle = p := rfl

/-- The score in the report is `scoreWith`. -/
theorem evaluateWith_score (c : Context) (s : Solution) :
    (evaluateWith c s).score = scoreWith c s := rfl

theorem mem_scoredValid {p : Puzzle} {s : Solution} {v : Int} :
    (s, v) ∈ scoredValid p ↔ s ∈ candidates p ∧ Valid p s ∧ v = score p s := by
  simp only [scoredValid, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hsome⟩
    split at hsome
    · simp at hsome
    · split at hsome
      · rename_i hv
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨ht, hv, rfl⟩
      · simp at hsome
  · rintro ⟨hs, hv, rfl⟩
    refine ⟨s, hs, ?_⟩
    have hv' : ValidWith (prepare p) s := hv
    have hbudget : ¬ costOf p s > p.budget := by
      have := hv.2.1; simp only [prepare_puzzle] at this; omega
    simp [hbudget, hv', score]

/-! ## Main theorem -/

/-- **The solver is right.** For every puzzle, if the solver returns a
solution, that solution is valid, and no valid solution has a higher score. -/
theorem solvePlain_is_best (p : Puzzle) (s : Solution) (h : solvePlain p = some s) :
    Valid p s ∧ ∀ t, Valid p t → score p t ≤ score p s := by
  unfold solvePlain at h
  split at h
  · simp at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s', v⟩, hbest, rfl⟩ := h
    have hmem := bestOf_mem _ _ _ hbest
    obtain ⟨_, hvalid, rfl⟩ := mem_scoredValid.1 hmem
    refine ⟨hvalid, fun t ht => ?_⟩
    have htmem : (t, score p t) ∈ scoredValid p :=
      mem_scoredValid.2 ⟨mem_candidates ht.1, ht, rfl⟩
    exact bestOf_max _ _ _ hbest _ htmem

/-! ## Every puzzle has a valid layout -/

theorem foldl_unchanged {α β : Type} (f : β → α → β) :
    ∀ (l : List α) (t : β), (∀ a ∈ l, ∀ t, f t a = t) → l.foldl f t = t
  | [], _, _ => rfl
  | a :: as, t, h => by
    simp only [List.foldl_cons, h a (by simp) t]
    exact foldl_unchanged f as t (fun b hb => h b (by simp [hb]))

theorem costOf_empty (p : Puzzle) : costOf p (emptyLayout p) = 0 := by
  unfold costOf
  rw [foldl_unchanged]
  · have hoff : List.filter (fun (_ : Route) => false) p.routes = [] := by
      induction p.routes <;> simp_all
    have hbr : List.filter (fun (_ : Nat) => false) p.bridgeSites = [] := by
      induction p.bridgeSites <;> simp_all
    simp [emptyLayout, List.filter_map, Function.comp_def, hoff, hbr]
  · intro i hi t
    split
    · rfl
    · rename_i hfix
      have hnone : p.fixedAt i = none := by cases hp : p.fixedAt i <;> simp_all
      have hi' : i < p.blockCount := by simpa using hi
      simp [emptyLayout, hi', hnone, Building.cost]

theorem mem_zip_map_same {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ (l : List α) (x : β × γ), x ∈ (l.map f).zip (l.map g) → ∃ a ∈ l, x = (f a, g a)
  | [], x, h => by simp at h
  | a :: as, x, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, by simp, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := mem_zip_map_same f g as x h
      exact ⟨b, by simp [hb], rfl⟩

theorem fits_empty (p : Puzzle) : FitsPuzzle p (emptyLayout p) := by
  refine ⟨by simp [emptyLayout, Puzzle.blockCount], ?_, by simp [emptyLayout],
    by simp [emptyLayout], by simp [emptyLayout]⟩
  intro pair hpair
  obtain ⟨i, _, rfl⟩ := mem_zip_map_same _ _ _ _ hpair
  simp only [Puzzle.choicesFor]
  cases p.fixedAt i <;> simp

/-- **Every puzzle has a valid layout**: the empty one. -/
theorem empty_valid (p : Puzzle) : Valid p (emptyLayout p) := by
  unfold Valid ValidWith
  refine ⟨fits_empty p, ?_, ?_, ?_⟩
  · simp only [prepare_puzzle, costOf_empty]; exact Nat.zero_le _
  · intro r _ hon
    exfalso
    simp only [emptyLayout, List.getD_eq_getElem?_getD, List.getElem?_map] at hon
    cases h : p.routes[r]? <;> simp_all
  · intro h; simp [emptyLayout] at h

/-- **The solver always answers when the puzzle is small enough.** -/
theorem solvePlain_isSome (p : Puzzle) (h : candidateCount p ≤ stepLimit) :
    (solvePlain p).isSome := by
  unfold solvePlain
  split
  · omega
  have hmem : (emptyLayout p, score p (emptyLayout p)) ∈ scoredValid p :=
    mem_scoredValid.2 ⟨mem_candidates (fits_empty p), empty_valid p, rfl⟩
  cases hb : bestOf (·.2) (scoredValid p) with
  | none =>
    have := (bestOf_eq_none _ _).1 hb
    simp [this] at hmem
  | some x => simp

/-! ## The solver's work is bounded

The solver scores each candidate once. `length_candidates` shows there are
exactly `candidateCount p` of them, and `solvePlain` only starts when that is at most
`stepLimit`. -/

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : Nat)
    (h : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    rw [Nat.succ_mul, Nat.add_comm]

theorem length_allPicks {α : Type} (ls : List (List α)) :
    (allPicks ls).length = productOfLengths ls := by
  induction ls with
  | nil => rfl
  | cons xs rest ih =>
    simp only [allPicks, productOfLengths]
    rw [length_flatMap_const _ _ (productOfLengths rest) (by intro a _; simp [ih])]

theorem length_allSwitches (n : Nat) : (allSwitches n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [allSwitches]
    rw [length_flatMap_const _ _ (2 ^ n) (by intro a _; simp [ih])]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem length_candidates (p : Puzzle) : (candidates p).length = candidateCount p := by
  unfold candidates candidateCount
  rw [length_flatMap_const _ _ (2 ^ p.routes.length * (p.stationSites.length + 1)
    * 2 ^ p.bridgeSites.length)]
  · rw [length_allPicks, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
  · intro b _
    rw [length_flatMap_const _ _ ((p.stationSites.length + 1) * 2 ^ p.bridgeSites.length)]
    · rw [length_allSwitches, Nat.mul_assoc]
    · intro r _
      rw [length_flatMap_const _ _ (2 ^ p.bridgeSites.length)]
      · simp
      · intro k _; simp [length_allSwitches]

/-- Layouts the solver scores for puzzle `p`: none if it gives up at once,
otherwise every candidate. -/
def solveWork (p : Puzzle) : Nat :=
  if candidateCount p > stepLimit then 0 else (candidates p).length

/-- **The solver never scores more than `stepLimit` layouts.** -/
theorem solveWork_le (p : Puzzle) : solveWork p ≤ stepLimit := by
  unfold solveWork
  split
  · exact Nat.zero_le _
  · rw [length_candidates]; omega

end SevenBridges
