import SevenBridges.Branch
import SevenBridges.BoundProofs

/-!
# The fast solver returns the best valid layout (DESIGN.md §8.1)

`solve_is_best`: if `solve` returns a layout, it is valid and no valid layout
scores more. `solveWithFuel_steps_le`: the solver takes at most `fuel` steps.
-/

namespace SevenBridges

/-! ## Search states -/

/-- The best layout so far is valid and `bestScore` is its score. -/
def Search.Good (p : Puzzle) (st : Search) : Prop :=
  Valid p st.best ∧ score p st.best = st.bestScore

/-- `b` comes later in a search than `a`: a good state stays good, the best
score never goes down, fuel never goes up, and steps taken plus fuel left
never go up. -/
def Search.Later (p : Puzzle) (a b : Search) : Prop :=
  (a.Good p → b.Good p) ∧ a.bestScore ≤ b.bestScore ∧ b.fuel ≤ a.fuel
  ∧ b.steps + b.fuel ≤ a.steps + a.fuel

/-- If the search has fuel left, no allowed valid layout in `S` scores more
than the best so far. -/
def Search.Covered (p : Puzzle) (keep : Solution → Bool) (S : Solution → Prop) (st : Search) : Prop :=
  st.fuel > 0 → ∀ t, Valid p t → keep t = true → S t → score p t ≤ st.bestScore

namespace Search
variable {p : Puzzle} {keep : Solution → Bool}

theorem Later.refl (a : Search) : a.Later p a := ⟨id, Int.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem Later.trans {a b c : Search} (h1 : a.Later p b) (h2 : b.Later p c) : a.Later p c :=
  ⟨fun h => h2.1 (h1.1 h), Int.le_trans h1.2.1 h2.2.1, Nat.le_trans h2.2.2.1 h1.2.2.1,
   Nat.le_trans h2.2.2.2 h1.2.2.2⟩

theorem Covered.later {S : Solution → Prop} {a b : Search} (h : a.Covered p keep S) (hab : a.Later p b) :
    b.Covered p keep S := by
  intro hf t hv hk hs
  exact Int.le_trans (h (Nat.lt_of_lt_of_le hf hab.2.2.1) t hv hk hs) hab.2.1

theorem covered_of_fuel_zero {S : Solution → Prop} {a : Search} (h : a.fuel = 0) : a.Covered p keep S := by
  intro hf; omega

theorem Covered.mono {S S' : Solution → Prop} {a : Search} (h : a.Covered p keep S)
    (hS : ∀ t, S' t → S t) : a.Covered p keep S' :=
  fun hf t hv hk hs => h hf t hv hk (hS t hs)

theorem later_spend (st : Search) (h : st.fuel ≠ 0) : st.Later p st.spend := by
  refine ⟨id, Int.le_refl _, ?_, ?_⟩ <;> simp [spend] <;> omega

theorem later_fuel_zero (st : Search) : st.Later p { st with fuel := 0 } :=
  ⟨id, Int.le_refl _, Nat.zero_le _, by simp⟩

theorem later_consider (c : Context) (hc : c = prepare p) (st : Search) (s : Solution) :
    st.Later p (st.consider c keep s) := by
  subst hc
  unfold consider
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨fun _ => ⟨h.1.2, rfl⟩, Int.le_of_lt h.2, Nat.le_refl _, Nat.le_refl _⟩
  · exact Later.refl _

theorem consider_ge (c : Context) (hc : c = prepare p) (st : Search) (s : Solution)
    (hk : keep s = true) (hv : Valid p s) : score p s ≤ (st.consider c keep s).bestScore := by
  subst hc
  unfold consider
  split
  · exact Int.le_refl _
  · rename_i h
    have hv' : ValidWith (prepare p) s := hv
    simp only [hk, hv', decide_true, Bool.true_and, decide_eq_true_eq] at h
    exact Int.not_lt.1 h

end Search

/-! ## Folds that visit every item -/

/-- A fold where each step moves the state later, and each item leaves behind a
fact that later states keep: at the end, every item's fact holds. -/
theorem foldl_cover {α β : Type} (f : β → α → β) (R : β → β → Prop) (C : α → β → Prop)
    (hrefl : ∀ b, R b b) (htrans : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → R b (f b a)) → (∀ b a, a ∈ l → C a (f b a)) →
      (∀ a b b', C a b → R b b' → C a b') →
      R init (l.foldl f init) ∧ ∀ a ∈ l, C a (l.foldl f init)
  | [], init, _, _, _ => ⟨hrefl _, fun _ h => by simp at h⟩
  | a :: as, init, hstep, hcov, hstable => by
    have ih := foldl_cover f R C hrefl htrans as (f init a) (fun b x hx => hstep b x (by simp [hx]))
      (fun b x hx => hcov b x (by simp [hx])) hstable
    refine ⟨htrans _ _ _ (hstep init a (by simp)) ih.1, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hstable _ _ _ (hcov init x (by simp)) ih.1
    · exact ih.2 x hx

/-! ## Plans and search nodes -/

/-- A plan is set up for puzzle `p`. -/
def Plan.Ok (p : Puzzle) (P : Plan) : Prop := P.Sound ∧ P.c = prepare p

/-- A search node is set up right: the plan and the per-transit plans are set
up for `p`, every transit choice of the group has its plan, and there is an
option list for every block. -/
def NodeOk (p : Puzzle) (P : Plan) (exacts : List Plan) (opts : List (List Building)) : Prop :=
  P.Ok p ∧ (∀ P' ∈ exacts, P'.Ok p ∧ ∃ T ∈ P.group, P'.group = [T])
  ∧ (∀ T ∈ P.group, ∃ P' ∈ exacts, P'.group = [T]) ∧ opts.length = p.blockCount

theorem puzzle_of_ok {p : Puzzle} {P : Plan} (h : P.Ok p) : P.c.puzzle = p := by rw [h.2]; rfl

theorem tryNode_spec (p : Puzzle) (keep : Solution → Bool) (P : Plan) (hP : P.Ok p)
    (opts : List (List Building)) (vals : Caps) (hvals : vals = P.optionValues opts)
    (go : Search → Search)
    (hgo : ∀ st, st.Later p (go st) ∧ (go st).Covered p keep (FitsNode P opts)) (st : Search) :
    st.Later p (st.tryNode P opts vals go) ∧ (st.tryNode P opts vals go).Covered p keep (FitsNode P opts) := by
  have hpz := puzzle_of_ok hP
  have hub : P.boundFrom vals = P.bound opts := by rw [hvals]; rfl
  unfold Search.tryNode
  split
  · exact ⟨Search.Later.refl _, Search.covered_of_fuel_zero (by assumption)⟩
  · rename_i hf
    have h1 : st.Later p st.spend := Search.later_spend st hf
    simp only
    split
    · rename_i hcost
      refine ⟨h1, fun _ t hv _ hfit => ?_⟩
      have := leastBuildCost_le p P hP.1 opts t hfit
      have := hv.2.1
      simp only [prepare_puzzle] at this
      rw [hpz] at hcost
      omega
    · split
      · rename_i hle
        refine ⟨h1, fun _ t hv _ hfit => ?_⟩
        have := score_le_bound p P hP.1 hP.2 opts t hv hfit
        rw [← hub] at this
        exact Int.le_trans this hle
      · split
        · rename_i hle
          refine ⟨h1, fun _ t hv _ hfit => ?_⟩
          rw [hvals] at hle
          exact score_le_of_knapsackCut p P hP.1 hP.2 opts t hv hfit _ hle
        · exact ⟨Search.Later.trans h1 (hgo _).1, (hgo _).2⟩

/-! ## Leaves: trying each transit choice -/

theorem fits_map_single (P : Plan) (build : List Building) (t : Solution) (hT : t.transit ∈ P.group)
    (hb : t.build = build) : FitsNode P (build.map ([·])) t := by
  refine ⟨hT, fun j => ?_⟩
  simp only [optsAt, Solution.look, hb, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases build[j]? <;> simp

theorem tryTransits_spec (p : Puzzle) (keep : Solution → Bool) (exacts : List Plan)
    (hex : ∀ P' ∈ exacts, P'.Ok p ∧ ∃ T, P'.group = [T]) (build : List Building) (st : Search) :
    st.Later p (tryTransits exacts keep build st)
    ∧ ∀ P' ∈ exacts, (tryTransits exacts keep build st).Covered p keep
        (fun t => P'.group = [t.transit] ∧ t.build = build) := by
  unfold tryTransits
  refine foldl_cover _ (Search.Later p) (fun P' st => st.Covered p keep (fun t => P'.group = [t.transit] ∧ t.build = build))
    Search.Later.refl (fun _ _ _ => Search.Later.trans) exacts st ?_ ?_
    (by intro a b b' h h'; exact Search.Covered.later h h')
  · intro st P' hP'
    obtain ⟨hok, T, hT⟩ := hex P' hP'
    simp only [hT]
    split
    · exact Search.Later.refl _
    · rename_i hf
      have h1 := Search.later_spend (p := p) st hf
      split
      · exact h1
      · split
        · exact h1
        · exact Search.Later.trans h1 (Search.later_consider _ hok.2 _ _)
  · intro st P' hP'
    obtain ⟨hok, T, hT⟩ := hex P' hP'
    have hpz := puzzle_of_ok hok
    simp only [hT]
    split
    · exact Search.covered_of_fuel_zero (by assumption)
    · rename_i hf
      split
      · rename_i hcost
        intro _ t hv _ ⟨hgT, hb⟩
        have hTt : t.transit = T := by simpa using hgT.symm
        have := hv.2.1
        simp only [prepare_puzzle] at this
        rw [costOf_eq, hb, hTt] at this
        rw [hpz] at hcost
        omega
      · split
        · rename_i hle
          intro _ t hv _ ⟨hgT, hb⟩
          have hTt : t.transit = T := by simpa using hgT.symm
          have := score_le_bound p P' hok.1 hok.2 _ t hv
            (fits_map_single P' build t (by rw [hT, hTt]; simp) hb)
          exact Int.le_trans this hle
        · intro _ t hv hk ⟨hgT, hb⟩
          have hTt : t.transit = T := by simpa using hgT.symm
          have hs : t = ⟨build, T.on, T.station, T.bridges⟩ := by
            rw [← hTt, ← hb]; rfl
          have := Search.consider_ge (p := p) (keep := keep) P'.c hok.2 st.spend t hk hv
          rw [← hs]
          exact this

/-! ## The branch search -/

theorem split_covers (sp : Split) (l : List Building) (b : Building) (hb : b ∈ l) :
    ∃ part ∈ sp.apply l, b ∈ part := by
  cases sp with
  | single => exact ⟨[b], List.mem_map.2 ⟨b, hb, rfl⟩, by simp⟩
  | byKey key count =>
    simp only [Split.apply, List.mem_filter, List.mem_append, List.mem_map, List.mem_range,
      List.mem_singleton]
    by_cases hk : key b < count
    · refine ⟨l.filter (key · == key b), ⟨Or.inl ⟨key b, hk, rfl⟩, ?_⟩, ?_⟩
      · simp only [ne_eq, decide_eq_true_eq]; intro h
        have : b ∈ l.filter (key · == key b) := List.mem_filter.2 ⟨hb, by simp⟩
        rw [h] at this; simp at this
      · exact List.mem_filter.2 ⟨hb, by simp⟩
    · refine ⟨l.filter (count ≤ key ·), ⟨Or.inr rfl, ?_⟩, ?_⟩
      · simp only [ne_eq, decide_eq_true_eq]; intro h
        have : b ∈ l.filter (count ≤ key ·) := List.mem_filter.2 ⟨hb, by simp; omega⟩
        rw [h] at this; simp at this
      · exact List.mem_filter.2 ⟨hb, by simp; omega⟩

theorem fits_set (P : Plan) (opts : List (List Building)) (t : Solution) (hfit : FitsNode P opts t)
    (k : Nat) (part : List Building) (hpart : t.look k ∈ part) : FitsNode P (opts.set k part) t := by
  refine ⟨hfit.1, fun j => ?_⟩
  have := hfit.2 j
  simp only [optsAt, List.getD_eq_getElem?_getD, List.getElem?_set] at this ⊢
  by_cases hj : k = j
  · subst hj
    by_cases hk : k < opts.length
    · simp [hk, hpart]
    · have hn : opts[k]? = none := List.getElem?_eq_none (by omega)
      simp only [hk, hn, ite_false, if_true, Option.getD_none] at this ⊢
      simpa using this
  · simp [hj, this]

theorem leaf_build (p : Puzzle) (opts : List (List Building)) (hlen : opts.length = p.blockCount)
    (hsingle : opts.all (·.length == 1) = true) (t : Solution) (hv : Valid p t)
    (hfit : ∀ j, t.look j ∈ optsAt opts j) : t.build = opts.map (·.headD .empty) := by
  have hbl : t.build.length = p.blockCount := hv.1.1
  apply List.ext_getElem (by simp [hbl, hlen])
  intro j h1 h2
  have hj : j < opts.length := by simpa using h2
  have hs : (opts[j]).length = 1 := by
    have := List.all_eq_true.1 hsingle opts[j] (List.getElem_mem hj)
    simpa using this
  have hmem := hfit j
  simp only [optsAt, Solution.look, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem hj, Option.getD_some] at hmem
  simp only [List.getElem_map]
  match hl : opts[j], hs with
  | [x], _ => rw [hl] at hmem; simp at hmem; simp [hmem]

theorem branch_spec (p : Puzzle) (keep : Solution → Bool) :
    ∀ (steps : List Step) (P : Plan) (exacts : List Plan) (opts : List (List Building)) (st : Search),
      NodeOk p P exacts opts →
      st.Later p (branch keep steps P exacts opts st)
      ∧ (branch keep steps P exacts opts st).Covered p keep (FitsNode P opts) := by
  intro steps
  induction steps with
  | nil =>
    intro P exacts opts st hok
    unfold branch
    split
    · rename_i hsingle
      have hex : ∀ P' ∈ exacts, P'.Ok p ∧ ∃ T, P'.group = [T] := fun P' h => by
        obtain ⟨h1, T, _, h2⟩ := hok.2.1 P' h; exact ⟨h1, T, h2⟩
      have := tryTransits_spec p keep exacts hex (opts.map (·.headD .empty)) st
      refine ⟨this.1, fun hf t hv hk hfit => ?_⟩
      obtain ⟨P', hP', hg⟩ := hok.2.2.1 t.transit hfit.1
      exact this.2 P' hP' hf t hv hk ⟨hg, leaf_build p opts hok.2.2.2 hsingle t hv hfit.2⟩
    · exact ⟨Search.later_fuel_zero _, Search.covered_of_fuel_zero rfl⟩
  | cons step steps ih =>
    intro P exacts opts st hok
    cases step with
    | block k sp =>
      unfold branch
      simp only
      let parts := ((sp.apply (optsAt opts k)).map fun part =>
        (opts.set k part, P.optionValues (opts.set k part), P.boundFrom (P.optionValues (opts.set k part)))).mergeSort
          (fun x y => x.2.2 ≥ y.2.2)
      have hparts : ∀ x ∈ parts, ∃ part, x = (opts.set k part, P.optionValues (opts.set k part),
          P.boundFrom (P.optionValues (opts.set k part))) := by
        intro x hx
        rw [List.mem_mergeSort, List.mem_map] at hx
        obtain ⟨part, _, rfl⟩ := hx
        exact ⟨part, rfl⟩
      have hokx : ∀ x ∈ parts, NodeOk p P exacts x.1 := by
        intro x hx
        obtain ⟨part, rfl⟩ := hparts x hx
        exact ⟨hok.1, hok.2.1, hok.2.2.1, by simp [hok.2.2.2]⟩
      have := foldl_cover (fun st x => st.tryNode P x.1 x.2.1 (branch keep steps P exacts x.1))
        (Search.Later p) (fun x st => st.Covered p keep (FitsNode P x.1))
        Search.Later.refl (fun _ _ _ => Search.Later.trans) parts st
        (fun b x hx => (tryNode_spec p keep P hok.1 x.1 x.2.1 (by obtain ⟨part, rfl⟩ := hparts x hx; rfl) _
          (fun st' => ih P exacts x.1 st' (hokx x hx)) b).1)
        (fun b x hx => (tryNode_spec p keep P hok.1 x.1 x.2.1 (by obtain ⟨part, rfl⟩ := hparts x hx; rfl) _
          (fun st' => ih P exacts x.1 st' (hokx x hx)) b).2)
        (by intro a b b' h h'; exact Search.Covered.later h h')
      refine ⟨this.1, fun hf t hv hk hfit => ?_⟩
      obtain ⟨part, hpart, hin⟩ := split_covers sp (optsAt opts k) (t.look k) (hfit.2 k)
      have hx : (opts.set k part, P.optionValues (opts.set k part),
          P.boundFrom (P.optionValues (opts.set k part))) ∈ parts := by
        rw [List.mem_mergeSort, List.mem_map]; exact ⟨part, hpart, rfl⟩
      exact this.2 _ hx hf t hv hk (fits_set P opts t hfit k part hin)
    | transit =>
      unfold branch
      simp only
      let parts := (exacts.map fun P' => (P', P'.optionValues opts, P'.boundFrom (P'.optionValues opts))).mergeSort
        (fun x y => x.2.2 ≥ y.2.2)
      have hparts : ∀ x ∈ parts, x.1 ∈ exacts ∧ x.2.1 = x.1.optionValues opts := by
        intro x hx
        rw [List.mem_mergeSort, List.mem_map] at hx
        obtain ⟨P', hP', rfl⟩ := hx
        exact ⟨hP', rfl⟩
      have hokx : ∀ x ∈ parts, NodeOk p x.1 [x.1] opts := by
        intro x hx
        obtain ⟨hok', T, _, hg⟩ := hok.2.1 x.1 (hparts x hx).1
        refine ⟨hok', fun P'' h => ?_, fun T' h => ?_, hok.2.2.2⟩
        · simp only [List.mem_singleton] at h; subst h; exact ⟨hok', T, by simp [hg], hg⟩
        · rw [hg] at h; simp only [List.mem_singleton] at h; subst h; exact ⟨x.1, by simp, hg⟩
      have := foldl_cover (fun st x => st.tryNode x.1 opts x.2.1 (branch keep steps x.1 [x.1] opts))
        (Search.Later p) (fun x st => st.Covered p keep (FitsNode x.1 opts))
        Search.Later.refl (fun _ _ _ => Search.Later.trans) parts st
        (fun b x hx => (tryNode_spec p keep x.1 (hokx x hx).1 opts x.2.1 (hparts x hx).2 _
          (fun st' => ih x.1 [x.1] opts st' (hokx x hx)) b).1)
        (fun b x hx => (tryNode_spec p keep x.1 (hokx x hx).1 opts x.2.1 (hparts x hx).2 _
          (fun st' => ih x.1 [x.1] opts st' (hokx x hx)) b).2)
        (by intro a b b' h h'; exact Search.Covered.later h h')
      refine ⟨this.1, fun hf t hv hk hfit => ?_⟩
      obtain ⟨P', hP', hg⟩ := hok.2.2.1 t.transit hfit.1
      have hx : (P', P'.optionValues opts, P'.boundFrom (P'.optionValues opts)) ∈ parts := by
        rw [List.mem_mergeSort, List.mem_map]; exact ⟨P', hP', rfl⟩
      exact this.2 _ hx hf t hv hk ⟨by rw [hg]; simp, hfit.2⟩

end SevenBridges

namespace SevenBridges

/-! ## Pieces of the search -/

/-- A piece of the search is set up right for `p`. -/
def Job.Ok (p : Puzzle) (j : Job) : Prop := NodeOk p j.P j.exacts j.opts

/-- Layouts a piece of the search looks at. -/
def Job.Fits (j : Job) (t : Solution) : Prop := FitsNode j.P j.opts t

theorem run_spec (p : Puzzle) (keep : Solution → Bool) (j : Job) (hj : j.Ok p) (st : Search) :
    st.Later p (j.run keep st) ∧ (j.run keep st).Covered p keep j.Fits :=
  branch_spec p keep j.steps j.P j.exacts j.opts st hj

theorem expand_spec (p : Puzzle) (j : Job) (hj : j.Ok p) :
    (∀ j' ∈ j.expand, j'.Ok p) ∧ ∀ t, j.Fits t → ∃ j' ∈ j.expand, j'.Fits t := by
  unfold Job.expand
  split
  · rename_i k sp rest _
    constructor
    · intro j' hj'
      obtain ⟨part, _, rfl⟩ := List.mem_map.1 hj'
      exact ⟨hj.1, hj.2.1, hj.2.2.1, by simp [hj.2.2.2]⟩
    · intro t hfit
      obtain ⟨part, hpart, hin⟩ := split_covers sp _ _ (hfit.2 k)
      exact ⟨_, List.mem_map.2 ⟨part, hpart, rfl⟩, fits_set _ _ t hfit k part hin⟩
  · exact ⟨fun j' h => by simp only [List.mem_singleton] at h; subst h; exact hj,
      fun t h => ⟨j, by simp, h⟩⟩

theorem expandAll_spec (p : Puzzle) (js : List Job) (hjs : ∀ j ∈ js, j.Ok p) :
    (∀ j' ∈ js.flatMap Job.expand, j'.Ok p)
    ∧ ∀ t, (∃ j ∈ js, j.Fits t) → ∃ j' ∈ js.flatMap Job.expand, j'.Fits t := by
  constructor
  · intro j' h
    obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.1 h
    exact (expand_spec p j (hjs j hj)).1 j' hj'
  · rintro t ⟨j, hj, hfit⟩
    obtain ⟨j', hj', hfit'⟩ := (expand_spec p j (hjs j hj)).2 t hfit
    exact ⟨j', List.mem_flatMap.2 ⟨j, hj, hj'⟩, hfit'⟩

theorem rootJobs_spec (p : Puzzle) :
    (∀ j ∈ rootJobs p, j.Ok p) ∧ ∀ t, Valid p t → ∃ j ∈ rootJobs p, j.Fits t := by
  constructor
  · intro j hj
    simp only [rootJobs, List.mem_map] at hj
    obtain ⟨Ts, _, rfl⟩ := hj
    refine ⟨⟨makePlan_sound _ _ _ _ rfl rfl, rfl⟩, ?_, ?_, by simp [Puzzle.choices, Puzzle.blockCount]⟩
    · intro P' hP'
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hP'
      exact ⟨⟨makePlan_sound _ _ _ _ rfl rfl, rfl⟩, T, hT, rfl⟩
    · intro T hT
      exact ⟨_, List.mem_map.2 ⟨T, hT, rfl⟩, rfl⟩
  · intro t hv
    have hfp : FitsPuzzle p t := hv.1
    obtain ⟨hlen, hpick, hroutes, hstation, hbridges⟩ := hfp
    let Ts : List Transit :=
      (none :: p.metroSites.map some).map fun station => ⟨t.routesOn, station, t.bridges⟩
    refine ⟨_, List.mem_map.2 ⟨Ts, ?_, rfl⟩, ?_, ?_⟩
    · refine List.mem_map.2 ⟨(t.routesOn, t.bridges), List.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
      · exact List.mem_flatMap.2 ⟨t.routesOn, (mem_allSwitches _ _).2 hroutes,
          List.mem_map.2 ⟨t.bridges, (mem_allSwitches _ _).2 hbridges, rfl⟩⟩
      · simp only [bridgesReadyFor, List.all_eq_true]
        intro r hr
        cases hon : t.routesOn.getD r false
        · rfl
        · simp only [Bool.not_true, Bool.false_or]
          exact (hv.2.2.1 r (by simpa using hr) hon).1
    · refine List.mem_map.2 ⟨t.station, ?_, rfl⟩
      cases hs : t.station with
      | none => simp
      | some k => simp only [hs] at hstation; simp_all
    · intro j
      simp only [optsAt, Solution.look]
      have hcl : p.choices.length = p.blockCount := by simp [Puzzle.choices]
      by_cases hj : j < p.blockCount
      · have h1 : j < t.build.length := by omega
        have h2 : j < p.choices.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
          List.getElem?_eq_getElem h2]
        simp only [Option.getD_some]
        have := hpick (t.build[j], p.choices[j])
          (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)
        exact this
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
        simp

theorem expandTimes_spec (p : Puzzle) :
    ∀ (n : Nat) (js : List Job), (∀ j ∈ js, j.Ok p) →
      (∀ j' ∈ expandTimes n js, j'.Ok p)
      ∧ ∀ t, (∃ j ∈ js, j.Fits t) → ∃ j' ∈ expandTimes n js, j'.Fits t
  | 0, js, h => ⟨h, fun _ h => h⟩
  | n + 1, js, h => by
    have h1 := expandAll_spec p js h
    have ih := expandTimes_spec p n _ h1.1
    exact ⟨ih.1, fun t ht => ih.2 t (h1.2 t ht)⟩

theorem jobs_spec (p : Puzzle) :
    (∀ j ∈ jobs p, j.Ok p) ∧ ∀ t, Valid p t → ∃ j ∈ jobs p, j.Fits t := by
  have h0 := rootJobs_spec p
  have h2 := expandTimes_spec p splitDepth _ h0.1
  have hmem : ∀ j, j ∈ jobs p ↔ j ∈ expandTimes splitDepth (rootJobs p) := by
    intro j
    simp only [jobs, List.mem_map, List.mem_mergeSort, Prod.exists]
    constructor
    · rintro ⟨j', b, ⟨a, ha, heq⟩, rfl⟩
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      exact ha
    · intro h; exact ⟨j, _, ⟨j, h, rfl⟩, rfl⟩
  constructor
  · intro j hj; exact h2.1 j ((hmem j).1 hj)
  · intro t hv
    obtain ⟨j, hj, hfit⟩ := h2.2 t (h0.2 t hv)
    exact ⟨j, (hmem j).2 hj, hfit⟩

/-! ## Running the pieces -/

theorem runInTurn_spec (p : Puzzle) (keep : Solution → Bool) (js : List Job) (hjs : ∀ j ∈ js, j.Ok p)
    (start : Search) :
    start.Later p (runInTurn keep js start) ∧ ∀ j ∈ js, (runInTurn keep js start).Covered p keep j.Fits := by
  unfold runInTurn
  refine foldl_cover _ (Search.Later p) (fun j st => st.Covered p keep j.Fits)
    Search.Later.refl (fun _ _ _ => Search.Later.trans) js start ?_ ?_
    (by intro a b b' h h'; exact Search.Covered.later h h')
  · intro st j hj
    simp only
    split
    · exact Search.Later.refl _
    · rename_i hf
      have h1 := Search.later_spend (p := p) st hf
      split
      · exact h1
      · exact Search.Later.trans h1 (run_spec p keep j (hjs j hj) _).1
  · intro st j hj
    simp only
    split
    · exact Search.covered_of_fuel_zero (by assumption)
    · split
      · rename_i hle
        intro _ t hv _ hfit
        exact Int.le_trans (score_le_bound p j.P (hjs j hj).1.1 (hjs j hj).1.2 j.opts t hv hfit) hle
      · exact (run_spec p keep j (hjs j hj) _).2

theorem better_fold (p : Puzzle) (g : Prop) :
    ∀ (rs : List Search) (a : Search), (g → a.Good p) → (∀ r ∈ rs, g → r.Good p) →
      (g → (rs.foldl Search.better a).Good p)
      ∧ a.bestScore ≤ (rs.foldl Search.better a).bestScore
      ∧ ∀ r ∈ rs, r.bestScore ≤ (rs.foldl Search.better a).bestScore
  | [], a, ha, _ => ⟨ha, Int.le_refl _, fun _ h => by simp at h⟩
  | r :: rs, a, ha, hrs => by
    simp only [List.foldl_cons]
    have hb : g → (a.better r).Good p := by
      intro hg; unfold Search.better; split
      · exact hrs r (by simp) hg
      · exact ha hg
    have hab : a.bestScore ≤ (a.better r).bestScore ∧ r.bestScore ≤ (a.better r).bestScore := by
      unfold Search.better; split <;> constructor <;> omega
    have ih := better_fold p g rs (a.better r) hb (fun r' hr' => hrs r' (by simp [hr']))
    refine ⟨ih.1, Int.le_trans hab.1 ih.2.1, ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact Int.le_trans hab.2 ih.2.1
    · exact ih.2.2 r' hr'

theorem sum_map_const {α : Type} (l : List α) (c : Nat) : (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]; omega

theorem sum_steps_le (rs : List Search) (share : Nat) (h : ∀ r ∈ rs, r.steps ≤ share) :
    rs.foldl (fun t r => t + r.steps) 0 ≤ rs.length * share := by
  rw [foldl_add_nat, ← sum_map_const rs share]
  have := sum_le_sum_nat Search.steps (fun _ => share) rs h
  omega

theorem task_spawn_get {α : Type} (f : Unit → α) (prio : Task.Priority) : (Task.spawn f prio).get = f () := rfl

/-- Every piece is in some hand. -/
theorem mem_deal {α : Type} (k : Nat) (hk : 0 < k) (js : List α) (j : α) (hj : j ∈ js) :
    ∃ h ∈ deal k js, j ∈ h := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hj
  refine ⟨_, List.mem_map.2 ⟨i % k, List.mem_range.2 (Nat.mod_lt _ hk), rfl⟩, ?_⟩
  refine List.mem_map.2 ⟨(js[i], i), List.mem_filter.2 ⟨?_, by simp⟩, rfl⟩
  exact List.mem_iff_getElem.2 ⟨i, by simp [hi], by simp⟩

theorem runHands_spec (p : Puzzle) (keep : Solution → Bool) (hs : List (List Job))
    (hjs : ∀ h ∈ hs, ∀ j ∈ h, j.Ok p) (start : Search) :
    start.Later p (runHands keep hs start)
    ∧ ∀ h ∈ hs, ∀ j ∈ h, (runHands keep hs start).Covered p keep j.Fits := by
  unfold runHands
  simp only [List.map_map, Function.comp_def, task_spawn_get]
  generalize hshare : start.fuel / hs.length = share
  generalize hs0 : ({ start with fuel := share, steps := 0 } : Search) = s0
  have hs0f : s0.fuel = share := by rw [← hs0]
  have hs0s : s0.steps = 0 := by rw [← hs0]
  have hs0g : start.Good p → s0.Good p := by rw [← hs0]; exact id
  generalize hR : (hs.map fun h => runInTurn keep h s0) = rs
  have hspec := fun h (hh : h ∈ hs) => runInTurn_spec p keep h (hjs h hh) s0
  have hmemR : ∀ r ∈ rs, ∃ h ∈ hs, r = runInTurn keep h s0 := by
    intro r hr; rw [← hR] at hr; obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hr; exact ⟨h, hh, rfl⟩
  have hgood : ∀ r ∈ rs, start.Good p → r.Good p := by
    intro r hr hg
    obtain ⟨j, hj, rfl⟩ := hmemR r hr
    exact (hspec j hj).1.1 (hs0g hg)
  have hfold := better_fold p (start.Good p) rs start id hgood
  have hsteps : ∀ r ∈ rs, r.steps ≤ share := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := hmemR r hr
    have := (hspec j hj).1.2.2.2
    omega
  have hused := sum_steps_le rs share hsteps
  have hlen : rs.length * share ≤ start.fuel := by
    rw [← hR, List.length_map, ← hshare]; exact Nat.mul_div_le start.fuel hs.length
  refine ⟨⟨fun hg => hfold.1 hg, hfold.2.1, ?_, ?_⟩, ?_⟩
  · simp only; split <;> omega
  · simp only; split <;> omega
  · intro h hh j hj hf t hv hk hfit
    have hall : ∀ r ∈ rs, r.fuel > 0 := by
      simp only at hf; split at hf
      · rename_i h; intro r hr; exact of_decide_eq_true (List.all_eq_true.1 h r hr)
      · omega
    have hr : runInTurn keep h s0 ∈ rs := by rw [← hR]; exact List.mem_map.2 ⟨h, hh, rfl⟩
    exact Int.le_trans ((hspec h hh).2 j hj (hall _ hr) t hv hk hfit) (hfold.2.2 _ hr)

/-- Running the hands at the same time gives the same result as `runHands`. -/
theorem runTogether_eq (keep : Solution → Bool) (p : Puzzle) (start : Search) :
    runTogether keep p start = runHands keep (deal hands (jobs p)) start := by
  unfold runTogether runHands combineHands
  simp only [List.map_map, Function.comp_def, task_spawn_get, Puzzle.fresh_eq, deal,
    List.length_map, List.length_range]

/-- **The whole search** visits everything: if it has fuel left, no allowed
valid layout scores more than the best it found. -/
theorem searchAll_spec (p : Puzzle) (keep : Solution → Bool) (start : Search) :
    start.Later p (searchAll p keep start)
    ∧ (searchAll p keep start).Covered p keep (fun _ => True) := by
  have hj := jobs_spec p
  unfold searchAll
  simp only
  have hq0 : start.Later p { start with fuel := min quickFuel start.fuel } :=
    ⟨id, Int.le_refl _, Nat.min_le_right _ _, by simp; omega⟩
  generalize hq : runInTurn keep (jobs p) { start with fuel := min quickFuel start.fuel } = quick
  have hquick := runInTurn_spec p keep (jobs p) hj.1 { start with fuel := min quickFuel start.fuel }
  rw [hq] at hquick
  have hlq := Search.Later.trans hq0 hquick.1
  have hst := hlq.2.2.2
  split
  · rename_i hf
    refine ⟨⟨fun hg => hlq.1 hg, hlq.2.1, Nat.sub_le _ _, by simp only; omega⟩, ?_⟩
    intro _ t hv hk _
    obtain ⟨j, hjm, hfit⟩ := hj.2 t hv
    exact hquick.2 j hjm hf t hv hk hfit
  · have hq1 : start.Later p { quick with fuel := start.fuel - (quick.steps - start.steps) } :=
      ⟨fun hg => hlq.1 hg, hlq.2.1, Nat.sub_le _ _, by simp only; omega⟩
    have hdeal : ∀ h ∈ deal hands (jobs p), ∀ j ∈ h, j.Ok p := by
      intro h hh j hjh
      simp only [deal, List.mem_map, List.mem_range] at hh
      obtain ⟨_, _, rfl⟩ := hh
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hjh
      exact hj.1 _ (List.of_mem_zip (List.mem_filter.1 hx).1).1
    have htog := runHands_spec p keep (deal hands (jobs p)) hdeal
      { quick with fuel := start.fuel - (quick.steps - start.steps) }
    rw [runTogether_eq]
    refine ⟨Search.Later.trans hq1 htog.1, ?_⟩
    intro hf t hv hk _
    obtain ⟨j, hjm, hfit⟩ := hj.2 t hv
    obtain ⟨h, hh, hjh⟩ := mem_deal hands (by decide) (jobs p) j hjm
    exact htog.2 h hh j hjh hf t hv hk hfit

/-! ## Main theorems -/

theorem startSearch_good (p : Puzzle) (fuel : Nat) : (startSearch p fuel).Good p := by
  unfold startSearch
  simp only
  split
  · rename_i h; exact ⟨of_decide_eq_true h, rfl⟩
  · exact ⟨empty_valid p, rfl⟩

/-- **The solver is right.** For every puzzle, if the solver returns a layout,
that layout is valid, and no valid layout has a higher score. -/
theorem solve_is_best (p : Puzzle) (s : Solution) (h : solve p = some s) :
    Valid p s ∧ ∀ t, Valid p t → score p t ≤ score p s := by
  unfold solve at h
  simp only at h
  split at h
  · rename_i hf
    cases h
    have hspec := searchAll_spec p (fun _ => true) (startSearch p searchFuel)
    have hgood := hspec.1.1 (startSearch_good p searchFuel)
    refine ⟨hgood.1, fun t ht => ?_⟩
    unfold solveWithFuel at hf ⊢
    rw [hgood.2]
    exact hspec.2 hf t ht rfl trivial
  · simp at h

/-- **The solver takes at most `fuel` steps.** -/
theorem solveWithFuel_steps_le (p : Puzzle) (fuel : Nat) : (solveWithFuel p fuel).steps ≤ fuel := by
  have := (searchAll_spec p (fun _ => true) (startSearch p fuel)).1.2.2.2
  unfold solveWithFuel
  simp only [startSearch] at this ⊢
  omega

end SevenBridges

namespace SevenBridges

/-! ## The rating out of 100 -/

theorem rating_eq (p : Puzzle) (bestScore : Int) (s : Solution) :
    rating p bestScore s = if Valid p s then
      (let base := score p (emptyLayout p)
       if base < bestScore then ((score p s - base) * 100 / (bestScore - base)).toNat
       else if bestScore ≤ score p s then 100 else 0)
    else 0 := rfl

/-- **No layout rates above 100**, when rated against the solver's best. -/
theorem rating_le_100 (p : Puzzle) (b : Solution) (hb : solve p = some b) (s : Solution) :
    rating p (score p b) s ≤ 100 := by
  have hbest := solve_is_best p b hb
  rw [rating_eq]
  split
  · rename_i hv
    have hle := hbest.2 s hv
    simp only
    split
    · rename_i hpos
      have hd : 0 < score p b - score p (emptyLayout p) := by omega
      have : (score p s - score p (emptyLayout p)) * 100 / (score p b - score p (emptyLayout p)) ≤ 100 :=
        Int.ediv_le_of_le_mul hd (by
          have := Int.mul_le_mul_of_nonneg_right (show score p s - score p (emptyLayout p)
            ≤ score p b - score p (emptyLayout p) by omega) (by decide : (0:Int) ≤ 100)
          rw [Int.mul_comm 100]; exact this)
      omega
    · split <;> omega
  · omega

/-- **Only a best layout rates 100.** -/
theorem rating_eq_100_iff (p : Puzzle) (b : Solution) (hb : solve p = some b) (s : Solution)
    (hs : Valid p s) : rating p (score p b) s = 100 ↔ score p s = score p b := by
  have hle := (solve_is_best p b hb).2 s hs
  have hempty := (solve_is_best p b hb).2 _ (empty_valid p)
  rw [rating_eq]
  simp only [hs, ite_true]
  split
  · rename_i hpos
    have hd : 0 < score p b - score p (emptyLayout p) := by omega
    constructor
    · intro h
      have h1 : (score p s - score p (emptyLayout p)) * 100 / (score p b - score p (emptyLayout p)) = 100 := by
        omega
      have h2 := Int.ediv_mul_le ((score p s - score p (emptyLayout p)) * 100) (Int.ne_of_gt hd)
      rw [h1] at h2
      omega
    · intro h
      rw [h, Int.mul_comm, Int.mul_ediv_cancel _ (Int.ne_of_gt hd)]
      rfl
  · constructor
    · intro h; split at h <;> omega
    · intro h; simp only [show score p b ≤ score p s by omega, ite_true]

end SevenBridges

namespace SevenBridges

/-- The search takes at most the fuel it is given. -/
theorem searchAll_steps_le (p : Puzzle) (keep : Solution → Bool) (start : Search) :
    (searchAll p keep start).steps + (searchAll p keep start).fuel ≤ start.steps + start.fuel :=
  (searchAll_spec p keep start).1.2.2.2

/-- The solver takes at most `fuel` steps, counting the fuel it has left. -/
theorem solveWithFuel_steps_fuel_le (p : Puzzle) (fuel : Nat) :
    (solveWithFuel p fuel).steps + (solveWithFuel p fuel).fuel ≤ fuel := by
  have := searchAll_steps_le p (fun _ => true) (startSearch p fuel)
  unfold solveWithFuel
  simp only [startSearch] at this ⊢
  omega

end SevenBridges
