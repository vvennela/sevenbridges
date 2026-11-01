import SevenBridges.Rules.Score

/-!
# Facts about the simulated day (DESIGN.md §15.2)

- `legs_return_home`: following a cat's trips from home brings it back home,
  and each trip starts where the previous one ended.
- `simulate_cats`: the day has exactly one entry per cat in town, in order,
  and no cat appears twice (`population_nodup`).
- `cats_conserved`: at every moment of the day, the cats at all places add up
  to the number of cats in town.

The rest are facts the bound needs (`SevenBridges/BoundProofs.lean`): a cat
only works where it can get to, only working cats drive, working drivers
always drive, and only cats in metro reach ride the metro.
-/

namespace SevenBridges
open Numbers

/-! ## Every cat ends the day at home -/

/-- **Every cat ends the day at home**: its trips, followed from home, each
start where the last one ended, and end at home. -/
theorem legs_return_home (cd : CatDay) :
    follow (.block cd.who.home) cd.legs = some (.block cd.who.home) := by
  unfold CatDay.legs
  cases hw : cd.work <;> cases hl : cd.lunch <;> cases he : cd.evening <;> simp [follow]

/-! ## Choices -/

section choices
variable (c : Context) (T : Transit) (seats : List Nat) (r : Resident)

theorem find?_prop {α : Type} {p : α → Bool} {l : List α} {a : α} (h : l.find? p = some a) :
    p a = true := List.find?_some h

theorem find?_mem {α : Type} {p : α → Bool} {l : List α} {a : α} (h : l.find? p = some a) :
    a ∈ l := List.mem_of_find?_eq_some h

/-- A cat only works on a block it can get to without a car or the metro, and
that block is in town. -/
theorem chooseWork_block (j : Nat) (h : (chooseWork c T seats r).1 = some (.block j)) :
    T.canReach c j r.home = true ∧ j ∈ c.blocks := by
  unfold chooseWork at h
  simp only at h
  split at h
  · simp at h
  · split at h <;> simp at h
  · split at h
    · rename_i j' hj
      simp only [Option.some.injEq, Place.block.injEq] at h
      subst h
      rcases Option.or_eq_some_iff.1 hj with hj | ⟨_, hj⟩
      · have := find?_prop hj
        simp only [Bool.and_eq_true] at this
        exact ⟨by simp [Transit.canReach, this.1], find?_mem hj⟩
      · have := find?_prop hj
        simp only [Bool.and_eq_true] at this
        exact ⟨by simp [Transit.canReach, this.1], find?_mem hj⟩
    · simp at h
  · split at h
    · rename_i j' hj
      simp only [Option.some.injEq, Place.block.injEq] at h
      subst h
      have := find?_prop hj
      simp only [Bool.and_eq_true] at this
      exact ⟨by simp [Transit.canReach, this.1], find?_mem hj⟩
    · split at h <;> simp at h
  · split at h
    · rename_i j' _ hj
      simp only [Option.some.injEq, Place.block.injEq] at h
      subst h
      have := find?_prop hj
      simp only [Bool.and_eq_true] at this
      exact ⟨by simp [Transit.canReach, this.1], find?_mem hj⟩
    · rename_i j' _ hj
      simp only [Option.some.injEq, Place.block.injEq] at h
      subst h
      have := find?_prop hj
      simp only [Bool.and_eq_true] at this
      exact ⟨by simp [Transit.canReach, this.1], find?_mem hj⟩
    · split at h <;> simp at h

/-- Only cats who work drive. -/
theorem chooseWork_car (h : (chooseWork c T seats r).2 = .car) : r.traits.day = .works := by
  unfold chooseWork at h
  simp only at h
  split at h
  · simp at h
  · split at h <;> simp at h
  · assumption
  · assumption
  · assumption

/-- A cat who works and is a driver always drives. -/
theorem chooseWork_driver (hw : r.traits.day = .works) (hd : r.traits.mobility = .driver) :
    (chooseWork c T seats r).2 = .car := by
  unfold chooseWork
  simp only [hw, hd]
  split <;> rfl

/-- Only cats in metro reach ride the metro. -/
theorem chooseWork_metro (h : (chooseWork c T seats r).2 = .metro) :
    T.stationReaches c r.home = true := by
  unfold chooseWork at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · assumption
    · simp at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h
      · assumption
      · simp at h
  · split at h
    · simp at h
    · simp at h
    · split at h
      · assumption
      · simp at h

end choices

/-! ## The day has one entry per cat -/

/-- The commute fold notes one day per cat, in order, each made by
`chooseWork` from some free seats. -/
theorem commute_fold (c : Context) (T : Transit) (look : Nat → Building) :
    ∀ (l : List Resident) (s : List Nat) (acc : List CatDay),
      ∃ outs : List CatDay, (l.foldl (commuteStep c T look) (s, acc)).2 = outs.reverse ++ acc
        ∧ outs.map (·.who) = l
        ∧ ∀ cd ∈ outs, ∃ seats, cd = dayOf c T look cd.who (chooseWork c T seats cd.who)
  | [], s, acc => ⟨[], by simp, by simp, by simp⟩
  | r :: rest, s, acc => by
    simp only [List.foldl_cons, commuteStep]
    obtain ⟨outs, h1, h2, h3⟩ := commute_fold c T look rest _ (dayOf c T look r (chooseWork c T s r) :: acc)
    refine ⟨dayOf c T look r (chooseWork c T s r) :: outs, ?_, ?_, ?_⟩
    · rw [h1]; simp
    · simp [h2, dayOf]
    · intro cd hcd
      rcases List.mem_cons.1 hcd with rfl | hcd
      · exact ⟨s, rfl⟩
      · exact h3 cd hcd

theorem simulate_spec (c : Context) (T : Transit) (look : Nat → Building) :
    (simulate c T look).map (·.who) = population c look
    ∧ ∀ cd ∈ simulate c T look, ∃ seats, cd = dayOf c T look cd.who (chooseWork c T seats cd.who) := by
  obtain ⟨outs, h1, h2, h3⟩ := commute_fold c T look (population c look) (startSeats c look) []
  unfold simulate
  rw [h1]
  simp only [List.append_nil, List.reverse_reverse]
  exact ⟨h2, h3⟩

theorem simulate_mem (c : Context) (T : Transit) (look : Nat → Building) (cd : CatDay)
    (h : cd ∈ simulate c T look) :
    ∃ seats, cd = dayOf c T look cd.who (chooseWork c T seats cd.who) :=
  (simulate_spec c T look).2 cd h

/-! ## The cats in town -/

theorem home_of_mem_residentsOn (c : Context) (h : Nat) (b : Building) (r : Resident)
    (hr : r ∈ residentsOn c h b) : r.home = h := by
  simp only [residentsOn, List.mem_map] at hr
  obtain ⟨i, _, rfl⟩ := hr
  rfl

theorem mem_population (c : Context) (look : Nat → Building) (r : Resident) :
    r ∈ population c look ↔ r.home ∈ c.blocks ∧ r ∈ residentsOn c r.home (look r.home) := by
  simp only [population, List.mem_flatMap]
  constructor
  · rintro ⟨h, hh, hr⟩
    have := home_of_mem_residentsOn c h _ r hr
    subst this
    exact ⟨hh, hr⟩
  · rintro ⟨hh, hr⟩
    exact ⟨r.home, hh, hr⟩

theorem nodup_map_range {α : Type} (f : Nat → α) (hf : ∀ i j, f i = f j → i = j) :
    ∀ n, ((List.range n).map f).Nodup
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.nodup_append]
    refine ⟨nodup_map_range f hf n, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_map, List.mem_range] at ha
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    obtain ⟨i, hi, rfl⟩ := ha
    subst hb
    intro heq
    have := hf _ _ heq
    omega

/-- **No cat is counted twice**: each cat in town has its own block and number. -/
theorem population_nodup (c : Context) (look : Nat → Building) :
    ((population c look).map fun r => (r.home, r.index)).Nodup := by
  unfold population Context.blocks
  generalize c.puzzle.blockCount = n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.nodup_append]
    refine ⟨ih, ?_, ?_⟩
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, residentsOn, List.map_map]
      exact nodup_map_range _ (fun i j h => by simp [Function.comp_def] at h; exact h) _
    · intro a ha b hb heq
      simp only [List.mem_map, List.mem_flatMap, List.mem_range] at ha hb
      obtain ⟨r, ⟨h, hh, hr⟩, rfl⟩ := ha
      obtain ⟨r', ⟨h', hh', hr'⟩, rfl⟩ := hb
      have e1 := home_of_mem_residentsOn c _ _ _ hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hh'
      subst hh'
      have e2 := home_of_mem_residentsOn c _ _ _ hr'
      simp only [Prod.mk.injEq] at heq
      omega

/-- **Each cat is counted exactly once**: the simulated day has one entry per
cat in town, in order, and no cat appears twice. -/
theorem simulate_cats (c : Context) (T : Transit) (look : Nat → Building) :
    (simulate c T look).map (·.who) = population c look
    ∧ (((simulate c T look).map (·.who)).map fun r => (r.home, r.index)).Nodup := by
  have h := (simulate_spec c T look).1
  exact ⟨h, by rw [h]; exact population_nodup c look⟩

/-! ## Cats are conserved through the day -/

theorem sum_map_eq_zero {α : Type} (f : α → Nat) :
    ∀ l : List α, (∀ x ∈ l, f x = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons, h x (by simp),
      sum_map_eq_zero f xs (fun y hy => h y (by simp [hy]))]

theorem sum_indicator_eq_one {α : Type} [DecidableEq α] (x : α) :
    ∀ (P : List α), P.Nodup → x ∈ P → (P.map fun pl => if x = pl then 1 else 0).sum = 1
  | [], _, h => by simp at h
  | y :: ys, hn, h => by
    rw [List.nodup_cons] at hn
    simp only [List.map_cons, List.sum_cons]
    by_cases hxy : x = y
    · subst hxy
      have : (ys.map fun pl => if x = pl then 1 else 0).sum = 0 := by
        apply sum_map_eq_zero
        intro pl hpl
        have : x ≠ pl := fun e => hn.1 (e ▸ hpl)
        simp [this]
      simp [this]
    · have hm : x ∈ ys := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h hxy
        · exact h
      simp [hxy, sum_indicator_eq_one x ys hn.2 hm]

theorem sum_counts {α β : Type} [DecidableEq β] (f : α → β) (P : List β) (hP : P.Nodup) :
    ∀ d : List α, (∀ x ∈ d, f x ∈ P) →
      (P.map fun pl => (d.filter fun x => f x == pl).length).sum = d.length
  | [], _ => by simpa using sum_map_eq_zero (fun _ => 0) P (fun _ _ => rfl)
  | x :: xs, h => by
    have ih := sum_counts f P hP xs (fun y hy => h y (by simp [hy]))
    have h1 : (P.map fun pl => ((x :: xs).filter fun y => f y == pl).length)
        = (P.map fun pl => (if f x = pl then 1 else 0) + (xs.filter fun y => f y == pl).length) := by
      apply List.map_congr_left
      intro pl _
      by_cases hx : f x = pl <;> simp [hx] <;> omega
    rw [h1]
    have h2 : ∀ (l : List β), (l.map fun pl => (if f x = pl then 1 else 0)
        + (xs.filter fun y => f y == pl).length).sum
        = (l.map fun pl => if f x = pl then 1 else 0).sum
          + (l.map fun pl => (xs.filter fun y => f y == pl).length).sum := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega
    rw [h2, ih, sum_indicator_eq_one (f x) P hP (h x (by simp))]
    simp; omega

theorem places_nodup (c : Context) : (places c).Nodup := by
  unfold places
  rw [List.nodup_cons]
  refine ⟨by simp, ?_⟩
  exact nodup_map_range _ (fun i j h => by simpa using h) _

theorem block_mem_places (c : Context) (j : Nat) (h : j ∈ c.blocks) : Place.block j ∈ places c := by
  simp only [places, List.mem_cons, List.mem_map]
  exact Or.inr ⟨j, h, rfl⟩

/-- Every place a cat goes to during the day is a place in town. -/
theorem place_mem (c : Context) (T : Transit) (look : Nat → Building) (cd : CatDay)
    (hcd : cd ∈ simulate c T look) (m : Moment) : cd.place m ∈ places c := by
  obtain ⟨seats, hday⟩ := simulate_mem c T look cd hcd
  have hwho : cd.who ∈ population c look := by
    rw [← (simulate_spec c T look).1]; exact List.mem_map_of_mem hcd
  have hhome := ((mem_population c look cd.who).1 hwho).1
  have hwork : ∀ p, cd.work = some p → p ∈ places c := by
    intro p hp
    cases p with
    | downtown => simp [places]
    | block j =>
      rw [hday] at hp
      exact block_mem_places c j (chooseWork_block c T seats cd.who j hp).2
  have hgetD : cd.work.getD (.block cd.who.home) ∈ places c := by
    cases h : cd.work with
    | none => exact block_mem_places c _ hhome
    | some p => exact hwork p h
  have hlunch : ∀ f, cd.lunch = some f → f ∈ c.blocks := by
    intro f hf
    rw [hday] at hf
    simp only [dayOf, lunchSpot] at hf
    split at hf
    · split at hf
      · exact find?_mem hf
      · simp at hf
    · simp at hf
  have heve : ∀ v, cd.evening = some v → v ∈ c.blocks := by
    intro v hv
    rw [hday] at hv
    simp only [dayOf, eveningSpot] at hv
    split at hv
    · rcases Option.or_eq_some_iff.1 hv with hv | ⟨_, hv⟩
      · exact find?_mem hv
      · exact find?_mem hv
    · simp at hv
  cases m with
  | dawn => exact block_mem_places c _ hhome
  | morning => exact hgetD
  | noon =>
    simp only [CatDay.place]
    cases h : cd.lunch with
    | none => exact hgetD
    | some f => exact block_mem_places c f (hlunch f h)
  | afternoon => exact hgetD
  | evening =>
    simp only [CatDay.place]
    cases h : cd.evening with
    | none => exact block_mem_places c _ hhome
    | some v => exact block_mem_places c v (heve v h)
  | night => exact block_mem_places c _ hhome

/-- **Cats are conserved**: at every moment of the day, the cats downtown and
on each block add up to the number of cats in town. -/
theorem cats_conserved (c : Context) (T : Transit) (look : Nat → Building) (m : Moment) :
    ((places c).map (countAt (simulate c T look) m)).sum = (population c look).length := by
  have h := sum_counts (fun cd : CatDay => cd.place m) (places c) (places_nodup c) (simulate c T look)
    (fun cd hcd => place_mem c T look cd hcd m)
  unfold countAt
  rw [h, ← (simulate_spec c T look).1, List.length_map]

/-- At night every cat is home. -/
theorem night_at_home (c : Context) (T : Transit) (look : Nat → Building) :
    ∀ cd ∈ simulate c T look, cd.place .night = .block cd.who.home := fun _ _ => rfl

end SevenBridges
