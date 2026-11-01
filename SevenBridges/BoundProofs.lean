import SevenBridges.Bound
import SevenBridges.DayProofs

/-!
# The bound is safe

`score_le_knapsackBound` and `score_le_bound`: no valid layout that fits a
search node scores more than the node's bound. Also: the cost cut never
throws away a valid layout.
-/

namespace SevenBridges
open Numbers

/-! ## Sums and folds -/

theorem foldl_add_int {α : Type} (f : α → Int) :
    ∀ (l : List α) (a : Int), l.foldl (fun t x => t + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: xs, a => by simp [foldl_add_int f xs]; omega

theorem foldl_add_nat {α : Type} (f : α → Nat) :
    ∀ (l : List α) (a : Nat), l.foldl (fun t x => t + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: xs, a => by simp [foldl_add_nat f xs]; omega

theorem sum_le_sum_int {α : Type} (f g : α → Int) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    have := h x (by simp)
    have := sum_le_sum_int f g xs (fun y hy => h y (by simp [hy]))
    simp; omega

theorem sum_le_sum_nat {α : Type} (f g : α → Nat) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    have := h x (by simp)
    have := sum_le_sum_nat f g xs (fun y hy => h y (by simp [hy]))
    simp; omega

/-- A sum over fewer items, of smaller values, is smaller. -/
theorem sum_filter_le {α : Type} (p q : α → Bool) (f g : α → Nat) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) → (∀ x ∈ l, f x ≤ g x) →
      ((l.filter p).map f).sum ≤ ((l.filter q).map g).sum
  | [], _, _ => by simp
  | x :: xs, hpq, hfg => by
    have ih := sum_filter_le p q f g xs (fun y hy => hpq y (by simp [hy]))
      (fun y hy => hfg y (by simp [hy]))
    have h1 := hfg x (by simp)
    by_cases hp : p x = true
    · have hq := hpq x (by simp) hp
      simp [List.filter_cons, hp, hq]; omega
    · by_cases hq : q x = true
      · simp [List.filter_cons, hp, hq]; omega
      · simp [List.filter_cons, hp, hq]; omega

theorem le_foldl_max {α : Type} (f : α → Int) :
    ∀ (l : List α) (init : Int), init ≤ l.foldl (fun m y => max m (f y)) init
  | [], _ => by simp
  | y :: ys, init => by
    simp only [List.foldl_cons]
    exact Int.le_trans (Int.le_max_left _ _) (le_foldl_max f ys _)

theorem mem_le_foldl_max {α : Type} (f : α → Int) :
    ∀ (l : List α) (init : Int) (x : α), x ∈ l → f x ≤ l.foldl (fun m y => max m (f y)) init
  | [], _, _, h => by simp at h
  | y :: ys, init, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Int.le_trans (Int.le_max_right _ _) (le_foldl_max f ys _)
    · exact mem_le_foldl_max f ys _ x h

theorem le_foldl_min {α : Type} (g : α → Int) (v : Int) :
    ∀ (l : List α) (init : Int), v ≤ init → (∀ x ∈ l, v ≤ g x) →
      v ≤ l.foldl (fun m x => min m (g x)) init
  | [], _, h, _ => by simpa using h
  | y :: ys, init, h, hl => by
    simp only [List.foldl_cons]
    refine le_foldl_min g v ys _ ?_ (fun x hx => hl x (by simp [hx]))
    exact Int.le_min.2 ⟨h, hl y (by simp)⟩

theorem foldl_min_le_nat {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat), l.foldl (fun m x => min m (f x)) init ≤ init
  | [], _ => by simp
  | y :: ys, init => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (foldl_min_le_nat f ys _) (Nat.min_le_left _ _)

theorem foldl_min_le_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat) (x : α), x ∈ l → l.foldl (fun m y => min m (f y)) init ≤ f x
  | [], _, _, h => by simp at h
  | y :: ys, init, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (foldl_min_le_nat f ys _) (Nat.min_le_right _ _)
    · exact foldl_min_le_mem f ys _ x h

theorem leastOf_le {α : Type} (f : α → Nat) (l : List α) (x : α) (h : x ∈ l) :
    leastOf f l ≤ f x := by
  cases l with
  | nil => simp at h
  | cons a rest =>
    simp only [leastOf]
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_min_le_nat f rest _
    · exact foldl_min_le_mem f rest _ x h

theorem le_foldl_max_nat {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat), init ≤ l.foldl (fun m y => max m (f y)) init
  | [], _ => by simp
  | y :: ys, init => by
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (le_foldl_max_nat f ys _)

theorem mem_le_foldl_max_nat {α : Type} (f : α → Nat) :
    ∀ (l : List α) (init : Nat) (x : α), x ∈ l → f x ≤ l.foldl (fun m y => max m (f y)) init
  | [], _, _, h => by simp at h
  | y :: ys, init, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max_nat f ys _)
    · exact mem_le_foldl_max_nat f ys _ x h

/-! ## Facts that are not settled yet -/

namespace Maybe

theorem covers_exact (v : Bool) : (exact v).Covers v := ⟨id, id⟩

theorem covers_and {a b : Maybe} {u v : Bool} (ha : a.Covers u) (hb : b.Covers v) :
    (a.and b).Covers (u && v) := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  constructor <;> intro h <;> simp_all [Maybe.and]

theorem covers_or {a b : Maybe} {u v : Bool} (ha : a.Covers u) (hb : b.Covers v) :
    (a.or b).Covers (u || v) := by
  obtain ⟨ha1, ha2⟩ := ha; obtain ⟨hb1, hb2⟩ := hb
  constructor <;> intro h
  · simp only [Maybe.or, Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp_all
  · simp only [Maybe.or, Bool.or_eq_true] at h ⊢; rcases h with h | h <;> simp_all

theorem covers_not {a : Maybe} {u : Bool} (ha : a.Covers u) : a.not.Covers (!u) := by
  obtain ⟨ha1, ha2⟩ := ha
  constructor <;> intro h <;> cases u <;> cases hm : a.must <;> cases hc : a.could <;>
    simp_all [Maybe.not]

theorem covers_anyOf {α : Type} (l : List α) (F : α → Maybe) (G : α → Bool)
    (h : ∀ x ∈ l, (F x).Covers (G x)) : (anyOf l F).Covers (l.any G) := by
  constructor
  · intro hm
    simp only [anyOf, List.any_eq_true] at hm ⊢
    obtain ⟨x, hx, hmx⟩ := hm
    exact ⟨x, hx, (h x hx).1 hmx⟩
  · intro hg
    simp only [anyOf, List.any_eq_true] at hg ⊢
    obtain ⟨x, hx, hgx⟩ := hg
    exact ⟨x, hx, (h x hx).2 hgx⟩

theorem covers_ofTest (l : List Building) (test : Building → Bool) (b : Building) (hb : b ∈ l) :
    (ofTest l test).Covers (test b) := by
  constructor
  · intro h
    simp only [ofTest, List.all_eq_true] at h
    exact h b hb
  · intro h
    simp only [ofTest, List.any_eq_true]
    exact ⟨b, hb, h⟩

theorem count_le_of_covers :
    ∀ (ps : List (Maybe × Bool)), (∀ p ∈ ps, p.1.Covers p.2) →
      ((ps.map (·.1)).filter (·.must)).length ≤ ((ps.map (·.2)).filter id).length
      ∧ ((ps.map (·.2)).filter id).length ≤ ((ps.map (·.1)).filter (·.could)).length
  | [], _ => by simp
  | (r, v) :: ps, h => by
    have ih := count_le_of_covers ps (fun p hp => h p (by simp [hp]))
    obtain ⟨h1, h2⟩ := h (r, v) (by simp)
    cases v <;> cases hm : r.must <;> cases hc : r.could <;>
      simp_all [List.filter_cons] <;> omega

theorem covers_atLeast (k : Nat) (ps : List (Maybe × Bool)) (h : ∀ p ∈ ps, p.1.Covers p.2) :
    (atLeast k (ps.map (·.1))).Covers (decide (((ps.map (·.2)).filter id).length ≥ k)) := by
  have := count_le_of_covers ps h
  constructor <;> intro h' <;> simp only [atLeast, decide_eq_true_eq] at h' ⊢ <;> omega

theorem ofCode_code (r : Maybe) : ofCode r.code = r := by
  cases r with
  | mk could must => cases could <;> cases must <;> rfl

theorem code_lt (r : Maybe) : r.code < 4 := by
  simp only [code]; split <;> split <;> omega

end Maybe

/-! ## What a block may hold -/

/-- `s` is right about building `b`. -/
def Spot.Admits (s : Spot) (b : Building) : Prop :=
  s.office.Covers b.isOffice ∧ s.food.Covers b.isFood ∧ b.residents ≤ s.residents

theorem Spot.admits_of (l : List Building) (b : Building) (hb : b ∈ l) : (Spot.of l).Admits b :=
  ⟨Maybe.covers_ofTest _ _ _ hb, Maybe.covers_ofTest _ _ _ hb,
   mem_le_foldl_max_nat Building.residents l 0 b hb⟩

/-! ## Mixes of neighbors -/

theorem foldl_inv {α β : Type} (f : β → α → β) (P : β → Prop) :
    ∀ (l : List α) (init : β), P init → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f init)
  | [], _, h, _ => h
  | a :: as, init, h, hs => foldl_inv f P as _ (hs init a (by simp) h)
      (fun b x hx hb => hs b x (by simp [hx]) hb)

/-- After a fold passes `a0`, a property `Q` that `a0` sets up and later steps
keep, holds. -/
theorem foldl_after {α β : Type} (f : β → α → β) (P Q : β → Prop) :
    ∀ (l : List α) (init : β) (a0 : α), a0 ∈ l → P init → (∀ b a, a ∈ l → P b → P (f b a)) →
      (∀ b, P b → Q (f b a0)) → (∀ b a, a ∈ l → P b → Q b → Q (f b a)) → Q (l.foldl f init)
  | [], _, _, h, _, _, _, _ => by simp at h
  | a :: as, init, a0, h, hP, hstep, hset, hkeep => by
    simp only [List.foldl_cons]
    have hP' := hstep init a (by simp) hP
    have hstep' : ∀ b x, x ∈ as → P b → P (f b x) := fun b x hx hb => hstep b x (by simp [hx]) hb
    have hkeep' : ∀ b x, x ∈ as → P b → Q b → Q (f b x) :=
      fun b x hx hb hq => hkeep b x (by simp [hx]) hb hq
    by_cases ha : a = a0
    · subst ha
      exact foldl_inv f (fun b => P b ∧ Q b) as _ ⟨hP', hset init hP⟩
        (fun b x hx ⟨hb, hq⟩ => ⟨hstep' b x hx hb, hkeep' b x hx hb hq⟩) |>.2
    · have : a0 ∈ as := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm ha
        · exact h
      exact foldl_after f P Q as _ a0 this hP' hstep' hset hkeep'

theorem profile_lt (c : Context) (x : Nat) (b : Building) : profile c x b < 512 := by
  unfold profile
  cases carsMust c x b <;> cases carsCould c x b <;> cases b <;> (try rename_i h; cases h) <;> decide

theorem ownCars_lt (c : Context) (x : Nat) (b : Building) : ownCars c x b < 512 := by
  unfold ownCars
  cases carsMust c x b <;> cases carsCould c x b <;> decide

theorem profile_bits (c : Context) (x : Nat) (b : Building) :
    (profile c x b).testBit 0 = b.isPark ∧ (profile c x b).testBit 1 = b.isBar
    ∧ (profile c x b).testBit 2 = b.isShop ∧ (profile c x b).testBit 3 = b.isLoud
    ∧ (profile c x b).testBit 4 = b.isHousing ∧ (profile c x b).testBit 5 = b.isOffice
    ∧ (profile c x b).testBit 6 = b.isFood ∧ (profile c x b).testBit 7 = carsMust c x b
    ∧ (profile c x b).testBit 8 = carsCould c x b := by
  unfold profile
  cases carsMust c x b <;> cases carsCould c x b <;> cases b <;> (try rename_i h; cases h) <;> decide

theorem ownCars_bits (c : Context) (x : Nat) (b : Building) :
    (∀ i < 7, (ownCars c x b).testBit i = false)
    ∧ (ownCars c x b).testBit 7 = carsMust c x b ∧ (ownCars c x b).testBit 8 = carsCould c x b := by
  unfold ownCars
  cases carsMust c x b <;> cases carsCould c x b <;>
    exact ⟨fun i hi => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide, by decide, by decide⟩

theorem or_lt_512 {a b : Nat} (ha : a < 512) (hb : b < 512) : a ||| b < 512 :=
  Nat.or_lt_two_pow (n := 9) ha hb

/-- What block `x.1` actually offers: its profile if it is an actual neighbor
(`sel`), else nothing. -/
def pick (c : Context) (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) : Nat :=
  if sel x.1 then profile c x.1 (look x.1) else 0

theorem pick_lt (c : Context) (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) :
    pick c look sel x < 512 := by
  unfold pick; split
  · exact profile_lt _ _ _
  · decide

theorem testBit_pick (c : Context) (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) (i : Nat) :
    (pick c look sel x).testBit i = (sel x.1 && (profile c x.1 (look x.1)).testBit i) := by
  unfold pick; cases sel x.1 <;> simp

/-- The mix the block itself (`a`) and the blocks in `nbrs` that are actual
neighbors (`sel`) offer. -/
def mixOf (c : Context) (look : Nat → Building) (sel : Nat → Bool) (nbrs : List (Nat × Bool))
    (a : Nat) : Nat :=
  nbrs.foldl (fun m x => m ||| pick c look sel x) a

theorem testBit_mixOf (c : Context) (look : Nat → Building) (sel : Nat → Bool) (i : Nat) :
    ∀ (nbrs : List (Nat × Bool)) (a : Nat),
      (mixOf c look sel nbrs a).testBit i
        = (a.testBit i || nbrs.any fun x => sel x.1 && (profile c x.1 (look x.1)).testBit i)
  | [], a => by simp [mixOf]
  | x :: xs, a => by
    simp only [mixOf, List.foldl_cons] at *
    rw [show List.foldl (fun m x => m ||| pick c look sel x) (a ||| pick c look sel x) xs
      = mixOf c look sel xs (a ||| pick c look sel x) from rfl, testBit_mixOf c look sel i xs]
    simp [Nat.testBit_or, testBit_pick, Bool.or_assoc]

theorem mixOf_lt (c : Context) (look : Nat → Building) (sel : Nat → Bool) :
    ∀ (nbrs : List (Nat × Bool)) (a : Nat), a < 512 → mixOf c look sel nbrs a < 512
  | [], _, h => h
  | x :: xs, a, h => mixOf_lt c look sel xs _ (or_lt_512 h (pick_lt c look sel x))

/-- The marks table is 512 long, every marked mix is listed, and every listed
mix is below 512. -/
def MarksOk (acc : Array Bool × List Nat) : Prop :=
  acc.1.size = 512 ∧ (∀ x, acc.1.getD x false = true → x ∈ acc.2) ∧ (∀ x ∈ acc.2, x < 512)

theorem getD_setIfInBounds (a : Array Bool) (i j : Nat) :
    (a.setIfInBounds i true).getD j false = if i = j ∧ i < a.size then true else a.getD j false := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

theorem markMix_ok (acc : Array Bool × List Nat) (x : Nat) (hx : x < 512) (h : MarksOk acc) :
    MarksOk (markMix acc x) := by
  obtain ⟨marks, l⟩ := acc
  obtain ⟨hs, hm, hl⟩ := h
  simp only at hs hm hl
  simp only [markMix]
  split
  · exact ⟨hs, hm, hl⟩
  · refine ⟨by simp [Array.set!_eq_setIfInBounds, hs], ?_, ?_⟩
    · intro y hy
      simp only [Array.set!_eq_setIfInBounds, getD_setIfInBounds] at hy
      split at hy
      · rename_i h; simp [h.1]
      · exact List.mem_cons_of_mem _ (hm y hy)
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hl y hy

theorem markMix_marked (acc : Array Bool × List Nat) (x : Nat) (hx : x < 512) (h : MarksOk acc) :
    (markMix acc x).1.getD x false = true := by
  obtain ⟨marks, l⟩ := acc
  simp only [markMix]
  split
  · assumption
  · simp [Array.set!_eq_setIfInBounds, getD_setIfInBounds, h.1, hx]

theorem markMix_mono (acc : Array Bool × List Nat) (x y : Nat) (h : acc.1.getD y false = true) :
    (markMix acc x).1.getD y false = true := by
  obtain ⟨marks, l⟩ := acc
  simp only [markMix]
  split
  · exact h
  · simp only [Array.set!_eq_setIfInBounds, getD_setIfInBounds]; split <;> simp_all

theorem addNeighbor_spec (mixes profiles : List Nat) (hm : ∀ m ∈ mixes, m < 512)
    (hp : ∀ q ∈ profiles, q < 512) :
    (∀ x ∈ addNeighbor mixes profiles, x < 512)
    ∧ ∀ m ∈ mixes, ∀ q ∈ profiles, m ||| q ∈ addNeighbor mixes profiles := by
  let inner (acc : Array Bool × List Nat) (m : Nat) :=
    profiles.foldl (fun acc q => markMix acc (m ||| q)) acc
  have hinner : ∀ acc m, m ∈ mixes → MarksOk acc → MarksOk (inner acc m) := fun acc m hmm hacc =>
    foldl_inv _ MarksOk profiles acc hacc fun b q hq hb => markMix_ok b _ (or_lt_512 (hm m hmm) (hp q hq)) hb
  have hinit : MarksOk (Array.replicate 512 false, []) := by
    refine ⟨by simp, ?_, by simp⟩
    intro x hx
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hx
    split at hx <;> simp at hx
  have hok : MarksOk (mixes.foldl inner (Array.replicate 512 false, [])) :=
    foldl_inv _ MarksOk mixes _ hinit fun b m hmm hb => hinner b m hmm hb
  refine ⟨hok.2.2, ?_⟩
  intro m hmm q hq
  apply hok.2.1
  let x := m ||| q
  have hmono : ∀ b m', m' ∈ mixes → MarksOk b → b.1.getD x false = true →
      (inner b m').1.getD x false = true := fun b m' _ _ hb =>
    foldl_inv _ (fun b => b.1.getD x false = true) profiles b hb
      fun b' q' _ hb' => markMix_mono b' _ x hb'
  refine foldl_after inner MarksOk (fun b => b.1.getD x false = true) mixes _ m hmm hinit
    (fun b m' hm' hb => hinner b m' hm' hb) ?_ hmono
  intro b hb
  exact foldl_after (fun acc q => markMix acc (m ||| q)) MarksOk (fun b => b.1.getD x false = true)
    profiles b q hq hb (fun b' q' hq' hb' => markMix_ok b' _ (or_lt_512 (hm m hmm) (hp q' hq')) hb')
    (fun b' hb' => markMix_marked b' x (or_lt_512 (hm m hmm) (hp q hq)) hb')
    (fun b' q' _ _ hb' => markMix_mono b' _ x hb')

/-- The mix the block itself and its actual neighbors offer is among the mixes
considered, when every sure neighbor is an actual one and every block holds
one of its options. -/
theorem mixOf_mem_neighborMixes (c : Context) (k : Nat) (opts : Nat → List Building)
    (look : Nat → Building) (sel : Nat → Bool)
    (nbrs : List (Nat × Bool)) (hsure : ∀ x ∈ nbrs, x.2 = true → sel x.1 = true)
    (hlook : ∀ j, look j ∈ opts j) :
    mixOf c look sel nbrs (ownCars c k (look k)) ∈ neighborMixes (profile c) (ownCars c) k nbrs opts := by
  unfold neighborMixes
  suffices ∀ (nbrs : List (Nat × Bool)) (mixes : List Nat) (a : Nat),
      (∀ x ∈ nbrs, x.2 = true → sel x.1 = true) →
      a ∈ mixes → (∀ m ∈ mixes, m < 512) → a < 512 →
      mixOf c look sel nbrs a ∈ nbrs.foldl (fun mixes x => addNeighbor mixes (offers (profile c) opts x)) mixes by
    refine this _ _ _ hsure (List.mem_map.2 ⟨look k, hlook k, rfl⟩) ?_ (ownCars_lt _ _ _)
    intro m hm
    obtain ⟨b, _, rfl⟩ := List.mem_map.1 hm
    exact ownCars_lt _ _ _
  intro nbrs
  induction nbrs with
  | nil => intro mixes a _ ha _ _; simpa [mixOf] using ha
  | cons x xs ih =>
    intro mixes a hs ha hm halt
    simp only [List.foldl_cons]
    have hp : ∀ q ∈ offers (profile c) opts x, q < 512 := by
      intro q hq
      simp only [offers, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨b, _, rfl⟩ | hq
      · exact profile_lt _ _ b
      · split at hq
        · simp at hq
        · simp only [List.mem_singleton] at hq; subst hq; decide
    have hq : pick c look sel x ∈ offers (profile c) opts x := by
      unfold pick offers
      by_cases hsel : sel x.1 = true
      · simp only [hsel, ite_true]
        exact List.mem_append_left _ (List.mem_map.2 ⟨look x.1, hlook x.1, rfl⟩)
      · have h2 : x.2 = false := by
          cases h : x.2
          · rfl
          · exact absurd (hs x (by simp) h) hsel
        simp [hsel, h2]
    have spec := addNeighbor_spec mixes _ hm hp
    have : mixOf c look sel (x :: xs) a = mixOf c look sel xs (a ||| pick c look sel x) := rfl
    rw [this]
    exact ih _ _ (fun y hy => hs y (by simp [hy]))
      (spec.2 a ha _ hq) spec.1 (or_lt_512 halt (pick_lt c look sel x))

/-! ## Happiness -/

theorem factorBest_ge (v : Int) (r : Maybe) (b : Bool) (h : r.Covers b) :
    (if b then v else 0) ≤ factorBest v r := by
  obtain ⟨h1, h2⟩ := h
  by_cases hv : v > 0 <;> cases b <;> cases hm : r.must <;> cases hc : r.could <;>
    simp_all [factorBest] <;> omega

/-- Happiness per person with the factors that hold is at most `bestEach`, when
each factor's `Maybe` is right. -/
theorem hpp_filter_le (t : Personality) (fm : Factor → Maybe) (P : Factor → Bool)
    (h : ∀ f, (fm f).Covers (P f)) :
    happinessPerPerson t (Factor.all.filter P) ≤ bestEach t fm := by
  unfold happinessPerPerson bestEach
  rw [foldl_add_int (fun f => (t.feeling f).value), foldl_add_int (fun f => factorBest (t.feeling f).value (fm f))]
  suffices ∀ l : List Factor, ((l.filter P).map fun f => (t.feeling f).value).sum
      ≤ (l.map fun f => factorBest (t.feeling f).value (fm f)).sum by
    have := this Factor.all; omega
  intro l
  induction l with
  | nil => simp
  | cons f fs ih =>
    have := factorBest_ge (t.feeling f).value (fm f) (P f) (h f)
    by_cases hp : P f = true <;> simp_all [List.filter_cons] <;> omega

theorem length_filter_eq_map {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.filter p).length = ((l.map p).filter id).length
  | [] => rfl
  | x :: xs => by
    have := length_filter_eq_map p xs
    by_cases hp : p x = true <;> simp_all [List.filter_cons]

/-- Each factor's `Maybe` is right, so happiness per person is at most
`bestEach`. One case per factor. -/
theorem factors_covered (c : Context) (T : Transit) (d : List CatDay) (look : Nat → Building)
    (t : Personality) (h : Nat) (m : Nat) (tn sn : Maybe)
    (hpark : m.testBit 0 = (T.neighborsOf c h).any fun j => (look j).isPark)
    (hbar : m.testBit 1 = (T.neighborsOf c h).any fun j => (look j).isBar)
    (hshop : m.testBit 2 = (T.neighborsOf c h).any fun j => (look j).isShop)
    (hloud : m.testBit 3 = (T.neighborsOf c h).any fun j => (look j).isLoud)
    (hhousing : m.testBit 4 = (T.neighborsOf c h).any fun j => (look j).isHousing)
    (hoffice : m.testBit 5 = (T.neighborsOf c h).any fun j => (look j).isOffice)
    (hfood : m.testBit 6 = (T.neighborsOf c h).any fun j => (look j).isFood)
    (htraffic : (⟨m.testBit 8, m.testBit 7⟩ : Maybe).Covers (traffic c T d h))
    (htn : tn.Covers (T.served c h || T.nearStation c h))
    (hsn : sn.Covers (T.nearStation c h)) :
    happinessPerPerson t (factorsHad c T d look h) ≤ bestEach t (factorMaybe m tn sn) := by
  unfold factorsHad
  apply hpp_filter_le
  have ex : ∀ i (v : Bool), m.testBit i = v → (Maybe.exact (m.testBit i)).Covers v := by
    intro i v hv; rw [hv]; exact Maybe.covers_exact v
  intro f
  cases f with
  | parks => exact ex 0 _ hpark
  | nightlife => exact ex 1 _ hbar
  | quiet =>
    exact Maybe.covers_not (Maybe.covers_or (Maybe.covers_or (ex 3 _ hloud) htraffic) hsn)
  | transit => exact htn
  | shops => exact ex 2 _ hshop
  | variety =>
    simp only [factorMaybe]
    have := Maybe.covers_atLeast 3
      [(Maybe.exact (m.testBit 4), (T.neighborsOf c h).any fun j => (look j).isHousing),
       (Maybe.exact (m.testBit 5), (T.neighborsOf c h).any fun j => (look j).isOffice),
       (Maybe.exact (m.testBit 2), (T.neighborsOf c h).any fun j => (look j).isShop),
       (Maybe.exact (m.testBit 0), (T.neighborsOf c h).any fun j => (look j).isPark),
       (Maybe.exact (m.testBit 1), (T.neighborsOf c h).any fun j => (look j).isBar),
       (Maybe.exact (m.testBit 6), (T.neighborsOf c h).any fun j => (look j).isFood)]
      (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
          rintro p (rfl | rfl | rfl | rfl | rfl | rfl)
          · exact ex 4 _ hhousing
          · exact ex 5 _ hoffice
          · exact ex 2 _ hshop
          · exact ex 0 _ hpark
          · exact ex 1 _ hbar
          · exact ex 6 _ hfood)
    simp only [List.map_cons, List.map_nil] at this
    rw [length_filter_eq_map]
    exact this
  | food => exact ex 6 _ hfood
  | cleanAir => exact Maybe.covers_or (Maybe.covers_not htraffic) (ex 0 _ hpark)

/-! ## Facts about the transit -/

/-- A plan is set up as `makePlan` sets it up. -/
def Plan.Sound (P : Plan) : Prop :=
  P.L = Lines.make P.c P.group ∧ P.moods = moodTables P.c ∧ P.tables = makeTables P.c

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (k : Nat) (d : α) (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem covers_any_all {α : Type} (Ts : List α) (F : α → Bool) (T : α) (hT : T ∈ Ts) :
    (⟨Ts.any F, Ts.all F⟩ : Maybe).Covers (F T) := by
  constructor
  · intro h; simp only [List.all_eq_true] at h; exact h T hT
  · intro h; simp only [List.any_eq_true]; exact ⟨T, hT, h⟩

theorem makePlan_sound (c : Context) (moods : Array (Array Int)) (tables : Tables) (Ts : List Transit)
    (h : moods = moodTables c) (ht : tables = makeTables c) : (makePlan c moods tables Ts).Sound :=
  ⟨rfl, h, ht⟩

/-- The tables hold what they should. -/
theorem readTable_eq (c : Context) (f : Nat → Building → Nat) (x : Nat) (b : Building) :
    readTable (buildingTable c f) f x b = f x b := by
  unfold readTable
  split
  · split
    · simp [buildingTable, Building.ofCode_code]
    · rfl
  · rfl

theorem readSlot_eq (c : Context) (x i : Nat) : readSlot (makeTables c).slots c x i = catSlot c x i := by
  unfold readSlot
  split
  · split
    · simp [makeTables]
    · rfl
  · rfl

theorem moodTable_get (p : Personality) (m t s : Nat) (hm : m < 512) (ht : t < 4) (hs : s < 4) :
    (moodTable p).getD (16 * m + (4 * t + s)) 0
      = bestEach p (factorMaybe m (Maybe.ofCode t) (Maybe.ofCode s)) := by
  unfold moodTable
  rw [getD_ofFn _ _ _ (by omega)]
  have e1 : (16 * m + (4 * t + s)) / 16 = m := by omega
  have e2 : (16 * m + (4 * t + s)) / 4 % 4 = t := by omega
  have e3 : (16 * m + (4 * t + s)) % 4 = s := by omega
  simp only [e1, e2, e3]

theorem moodValue_mono (p : Nat) (e e' : Int) (h : e ≤ e') : moodValue p e ≤ moodValue p e' := by
  unfold moodValue
  have h1 : (p : Int) * e ≤ (p : Int) * e' := Int.mul_le_mul_of_nonneg_left h (by omega)
  have h2 : (unhappyLine - e').toNat ≤ (unhappyLine - e).toNat := by omega
  have h3 : unhappyCost * (unhappyLine - e').toNat * p ≤ unhappyCost * (unhappyLine - e).toNat * p :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
  omega

theorem sum_sub_sum {α : Type} (f : α → Int) (g : α → Nat) :
    ∀ l : List α, (l.map f).sum - ((l.map g).sum : Int) = (l.map fun x => f x - (g x : Int)).sum
  | [] => by simp
  | x :: xs => by
    have := sum_sub_sum f g xs
    simp only [List.map_cons, List.sum_cons, Int.natCast_add]; omega

theorem le_maxOver {α : Type} (F : α → Int) (l : List α) (x : α) (hx : x ∈ l) :
    F x ≤ maxOver F l := by
  cases l with
  | nil => simp at hx
  | cons y ys =>
    simp only [maxOver]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_foldl_max F ys _
    · exact mem_le_foldl_max F ys _ x hx

theorem length_filter_mono {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | x :: xs, h => by
    have ih := length_filter_mono p q xs (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    by_cases hp : p x = true
    · simp [hp, hx _]; omega
    · by_cases hq : q x = true <;> simp [hp, hq] <;> omega

/-! ## What the simulated day gives each block, at most -/

theorem sum_map_ite_const {α : Type} (p : α → Bool) (a : Nat) :
    ∀ l : List α, (l.map fun x => if p x then a else 0).sum = a * (l.filter p).length
  | [] => by simp
  | x :: xs => by
    have := sum_map_ite_const p a xs
    by_cases hp : p x = true <;> simp [hp, List.filter_cons, this, Nat.mul_add] <;> omega

theorem mul_sum_map {α : Type} (a : Nat) (f : α → Nat) :
    ∀ l : List α, a * (l.map f).sum = (l.map fun x => a * f x).sum
  | [] => by simp
  | x :: xs => by simp [Nat.mul_add, mul_sum_map a f xs]

theorem sum_range_single (f : Nat → Nat) (k : Nat) (hf : ∀ h, h ≠ k → f h = 0) :
    ∀ n, k < n → ((List.range n).map f).sum = f k
  | 0, h => by omega
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hk : k = n
    · subst hk
      have : ((List.range k).map f).sum = 0 :=
        sum_map_eq_zero f _ (fun h hh => hf h (by simp at hh; omega))
      simp [this]
    · rw [sum_range_single f k hf n (by omega)]
      simp [hf n (Ne.symm hk)]

/-- Counting cats with a property on the day is counting them in town. -/
theorem length_filter_simulate (c : Context) (T : Transit) (look : Nat → Building)
    (Q : Resident → Bool) :
    ((simulate c T look).filter fun cd => Q cd.who).length = ((population c look).filter Q).length := by
  rw [← (simulate_spec c T look).1, List.filter_map, List.length_map]
  rfl

/-- Counting cats in town with a property, block by block. -/
theorem length_filter_population (c : Context) (look : Nat → Building) (Q : Resident → Bool) :
    ((population c look).filter Q).length
      = (c.blocks.map fun h => ((residentsOn c h (look h)).filter Q).length).sum := by
  simp [population, List.filter_flatMap, List.length_flatMap, Function.comp_def]

/-- Cats of block `h` with a property that only looks at their home. -/
theorem length_filter_residentsOn_home (c : Context) (h : Nat) (b : Building) (Q : Nat → Bool) :
    ((residentsOn c h b).filter fun r => Q r.home).length = if Q h then b.cats else 0 := by
  unfold residentsOn
  rw [List.filter_map, List.length_map]
  by_cases hq : Q h = true
  · simp [Function.comp_def, hq, List.filter_eq_self.2]
  · have : (List.filter ((fun r : Resident => Q r.home) ∘ fun i => (⟨h, i, c.traitsAt h i⟩ : Resident))
        (List.range b.cats)) = [] := by
      simp [Function.comp_def, hq]
    simp [this, hq]

theorem sum_filter_map_eq {α : Type} (p : α → Bool) (f : α → Nat) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum
  | [] => rfl
  | x :: xs => by
    have := sum_filter_map_eq p f xs
    by_cases hp : p x = true <;> simp [List.filter_cons, hp, this]

theorem cats_mul_le (b : Building) : residentsPerCat * b.cats ≤ b.residents := by
  unfold Building.cats residentsPerCat; omega

/-- **Workers who came from town are at most the residents who can reach the
office.** -/
theorem localWorkers_le (c : Context) (T : Transit) (look : Nat → Building) (j : Nat) :
    localWorkers (simulate c T look) j ≤ workersFor c T look j := by
  unfold localWorkers workersFor
  have h1 : ((simulate c T look).filter fun cd => cd.work == some (.block j)).length
      ≤ ((simulate c T look).filter fun cd => T.canReach c j cd.who.home).length := by
    apply length_filter_mono
    intro cd hcd hw
    obtain ⟨seats, hday⟩ := simulate_mem c T look cd hcd
    have hw' : cd.work = some (.block j) := by simpa using hw
    have : (chooseWork c T seats cd.who).1 = some (.block j) := by
      rw [← hw', hday]; rfl
    exact (chooseWork_block c T seats cd.who j this).1
  rw [length_filter_simulate c T look (fun r => T.canReach c j r.home),
    length_filter_population] at h1
  simp only [length_filter_residentsOn_home] at h1
  rw [foldl_add_nat, Nat.zero_add, sum_filter_map_eq]
  refine Nat.le_trans (Nat.mul_le_mul_left _ h1) ?_
  rw [mul_sum_map]
  apply sum_le_sum_nat
  intro h _
  split
  · exact cats_mul_le _
  · simp

/-- Some cat of block `x` drives only if a cat of `x` works. -/
theorem carFrom_could (c : Context) (T : Transit) (look : Nat → Building) (x : Nat)
    (h : carFrom (simulate c T look) x = true) : carsCould c x (look x) = true := by
  unfold carFrom at h
  obtain ⟨cd, hcd, hx⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨seats, hday⟩ := simulate_mem c T look cd hcd
  have hmode : (chooseWork c T seats cd.who).2 = .car := by rw [← hx.2, hday]; rfl
  have hworks := chooseWork_car c T seats cd.who hmode
  have hwho : cd.who ∈ population c look := by
    rw [← (simulate_spec c T look).1]; exact List.mem_map_of_mem hcd
  have hmem := ((mem_population c look cd.who).1 hwho).2
  rw [hx.1] at hmem
  unfold carsCould
  exact List.any_eq_true.2 ⟨cd.who, hmem, by simp [hworks]⟩

/-- A working driver of block `x` always drives. -/
theorem carFrom_must (c : Context) (T : Transit) (look : Nat → Building) (x : Nat)
    (hx : x ∈ c.blocks) (h : carsMust c x (look x) = true) : carFrom (simulate c T look) x = true := by
  unfold carsMust at h
  obtain ⟨r, hr, hwd⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hwd
  have hhome := home_of_mem_residentsOn c x _ r hr
  have hpop : r ∈ population c look := by
    rw [mem_population, hhome]; exact ⟨hx, hr⟩
  rw [← (simulate_spec c T look).1] at hpop
  obtain ⟨cd, hcd, rfl⟩ := List.mem_map.1 hpop
  obtain ⟨seats, hday⟩ := simulate_mem c T look cd hcd
  have hmode : cd.mode = .car := by
    rw [hday]; exact chooseWork_driver c T seats cd.who hwd.1 hwd.2
  unfold carFrom
  exact List.any_eq_true.2 ⟨cd, hcd, by simp [hhome, hmode]⟩

theorem foldl_if_add {α : Type} (r : α → Bool) (X : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun t j => if r j then t + X j else t) a = a + (l.map fun j => if r j then X j else 0).sum := by
  have : (fun t j => if r j = true then t + X j else t) = (fun t j => t + (if r j then X j else 0)) := by
    funext t j; split <;> simp
  rw [this, foldl_add_nat]

/-- **Downtown jobs of block `k` are at most every working cat, at the metro
rate if `k` is in metro reach, else at the car rate.** -/
theorem downtownOutput_le (c : Context) (T : Transit) (look : Nat → Building) (k : Nat)
    (hk : k < c.puzzle.blockCount) :
    downtownOutput (simulate c T look) k
      ≤ residentsPerCat * workingCats c k (look k)
          * (if T.stationReaches c k then metroJobWorth else carJobWorth) := by
  let W := if T.stationReaches c k then metroJobWorth else carJobWorth
  let Q : Resident → Bool := fun r => r.home == k && r.traits.day == .works
  unfold downtownOutput
  rw [foldl_if_add, Nat.zero_add]
  have h1 : ((simulate c T look).map fun cd =>
        if cd.who.home == k && cd.who.traits.day == .works && cd.work == some .downtown then
          residentsPerCat * downtownWorth cd.mode else 0).sum
      ≤ ((simulate c T look).map fun cd => if Q cd.who then residentsPerCat * W else 0).sum := by
    apply sum_le_sum_nat
    intro cd hcd
    by_cases hC : (cd.who.home == k && cd.who.traits.day == .works && cd.work == some .downtown) = true
    · have hQ : Q cd.who = true := by
        simp only [Q]; simp only [Bool.and_eq_true] at hC ⊢; exact hC.1
      simp only [hC, hQ, ite_true]
      apply Nat.mul_le_mul_left
      have hk' : cd.who.home = k := by simp only [Bool.and_eq_true, beq_iff_eq] at hC; exact hC.1.1
      obtain ⟨seats, hday⟩ := simulate_mem c T look cd hcd
      have hmode : cd.mode = (chooseWork c T seats cd.who).2 := by rw [hday]; rfl
      cases hm : cd.mode with
      | metro =>
        have hr := chooseWork_metro c T seats cd.who (hm ▸ hmode).symm
        rw [hk'] at hr
        simp [W, hr, downtownWorth]
      | car => simp only [downtownWorth, W]; split <;> simp [metroJobWorth, carJobWorth]
      | walk => simp [downtownWorth]
      | bus => simp [downtownWorth]
    · simp only [hC, Bool.false_eq_true, ite_false]; exact Nat.zero_le _
  rw [sum_map_ite_const] at h1
  have h2 := length_filter_simulate c T look Q
  have h3 : ((population c look).filter Q).length = workingCats c k (look k) := by
    rw [length_filter_population]
    unfold Context.blocks
    rw [sum_range_single (fun h => ((residentsOn c h (look h)).filter Q).length) k ?_ _ hk]
    · unfold workingCats
      congr 1
      apply List.filter_congr
      intro r hr
      simp [Q, home_of_mem_residentsOn c k _ r hr]
    · intro h hne
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro r hr
      simp [Q, home_of_mem_residentsOn c h _ r hr, hne]
  have h4 : ((simulate c T look).filter fun cd => Q cd.who).length = workingCats c k (look k) := by
    rw [h2, h3]
  rw [h4] at h1
  refine Nat.le_trans h1 (Nat.le_of_eq ?_)
  simp only [W]
  rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (workingCats c k (look k))]

/-! ## One block's value is at most its cap -/

theorem getD_map_range {α : Type} (f : Nat → α) (n i : Nat) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hi]

/-- The residents who can reach block `k` are at most the cap's workers. -/
theorem workers_le (c : Context) (Ts : List Transit) (T : Transit) (hT : T ∈ Ts)
    (spot : Nat → Spot) (look : Nat → Building) (hspot : ∀ j, (spot j).Admits (look j))
    (k : Nat) (hk : k < c.puzzle.blockCount) :
    workersFor c T look k
      ≤ ((Lines.make c Ts).workerSources.getD k []).foldl (fun t h => t + (spot h).residents) 0 := by
  unfold workersFor
  have hw : (Lines.make c Ts).workerSources.getD k []
      = c.blocks.filter fun h => Ts.any (·.canReach c k h) :=
    getD_ofFn _ _ _ hk
  rw [hw, foldl_add_nat (fun h => (look h).residents), foldl_add_nat (fun h => (spot h).residents)]
  simp only [Nat.zero_add]
  apply sum_filter_le
  · intro h _ hh
    exact List.any_eq_true.2 ⟨T, hT, hh⟩
  · intro h _; exact (hspot h).2.2

/-- Looking over the blocks that could be neighbors and keeping the actual ones
is the same as looking over the actual neighbors. -/
theorem any_neighbors (c : Context) (Ts : List Transit) (T : Transit) (hT : T ∈ Ts) (k : Nat)
    (hk : k < c.puzzle.blockCount) (test : Nat → Bool) :
    (((Lines.make c Ts).neighbors.getD k []).any fun x => T.isNeighbor c k x.1 && test x.1)
      = (T.neighborsOf c k).any test := by
  simp only [Lines.make]
  rw [getD_ofFn _ _ _ hk]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_map, List.mem_filter, Transit.neighborsOf, Bool.and_eq_true]
  constructor
  · rintro ⟨x, ⟨j, ⟨hj, _⟩, rfl⟩, hn, ht⟩
    exact ⟨j, ⟨hj, hn⟩, ht⟩
  · rintro ⟨j, ⟨hj, hn⟩, ht⟩
    exact ⟨_, ⟨j, ⟨hj, ⟨T, hT, hn⟩⟩, rfl⟩, hn, ht⟩

/-- Every block that surely is a neighbor, is one. -/
theorem sure_neighbor (P : Plan) (hL : P.L = Lines.make P.c P.group) (T : Transit) (hT : T ∈ P.group)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    ∀ x ∈ P.L.neighbors.getD k [], x.2 = true → T.isNeighbor P.c k x.1 = true := by
  rw [hL]
  simp only [Lines.make]
  rw [getD_ofFn _ _ _ hk]
  intro x hx hs
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
  exact List.all_eq_true.1 hs T hT

theorem residentType_min (c : Context) (k : Nat) :
    c.residentType (min k c.typeCount) = c.residentType k := by
  unfold Context.residentType Context.typeCount
  by_cases h : k < c.residentTypes.size
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right (by omega)]
    simp [Array.getD_eq_getD_getElem?, h]

/-- The actual traffic on block `k` is covered by the cars bits of the mix. -/
theorem traffic_covered (c : Context) (Ts : List Transit) (T : Transit) (hT : T ∈ Ts)
    (look : Nat → Building) (k : Nat) (hk : k < c.puzzle.blockCount) (m : Nat)
    (h7 : m.testBit 7 = (carsMust c k (look k) || (T.neighborsOf c k).any fun x => carsMust c x (look x)))
    (h8 : m.testBit 8 = (carsCould c k (look k) || (T.neighborsOf c k).any fun x => carsCould c x (look x))) :
    (⟨m.testBit 8, m.testBit 7⟩ : Maybe).Covers (traffic c T (simulate c T look) k) := by
  constructor
  · intro hm
    simp only at hm
    rw [h7] at hm
    unfold traffic
    rcases Bool.or_eq_true_iff.1 hm with hm | hm
    · simp [carFrom_must c T look k (List.mem_range.2 hk) hm]
    · obtain ⟨x, hx, hxm⟩ := List.any_eq_true.1 hm
      have hxb : x ∈ c.blocks := (List.mem_filter.1 hx).1
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨x, hx, carFrom_must c T look x hxb hxm⟩
  · intro ht
    simp only
    rw [h8]
    unfold traffic at ht
    rcases Bool.or_eq_true_iff.1 ht with ht | ht
    · simp [carFrom_could c T look k ht]
    · obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 ht
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨x, hx, carFrom_could c T look x hxc⟩

/-- A bit of the mix for a building test (bits 0–6), read off the actual
neighbors. -/
theorem mix_bit (c : Context) (Ts : List Transit) (T : Transit) (hT : T ∈ Ts)
    (look : Nat → Building) (k : Nat) (hk : k < c.puzzle.blockCount) (i : Nat)
    (test : Building → Bool) (hpt : ∀ x b, (profile c x b).testBit i = test b)
    (hown : (ownCars c k (look k)).testBit i = false) :
    (mixOf c look (T.isNeighbor c k) ((Lines.make c Ts).neighbors.getD k []) (ownCars c k (look k))).testBit i
      = (T.neighborsOf c k).any fun j => test (look j) := by
  rw [testBit_mixOf, hown, Bool.false_or]
  simp only [hpt]
  exact any_neighbors c Ts T hT k hk (fun j => test (look j))

/-- A cars bit of the mix (bits 7 and 8), read off the block and its actual
neighbors. -/
theorem mix_bit_cars (c : Context) (Ts : List Transit) (T : Transit) (hT : T ∈ Ts)
    (look : Nat → Building) (k : Nat) (hk : k < c.puzzle.blockCount) (i : Nat)
    (test : Nat → Building → Bool) (hpt : ∀ x b, (profile c x b).testBit i = test x b)
    (hown : (ownCars c k (look k)).testBit i = test k (look k)) :
    (mixOf c look (T.isNeighbor c k) ((Lines.make c Ts).neighbors.getD k []) (ownCars c k (look k))).testBit i
      = (test k (look k) || (T.neighborsOf c k).any fun j => test j (look j)) := by
  rw [testBit_mixOf, hown]
  simp only [hpt]
  rw [any_neighbors c Ts T hT k hk (fun j => test j (look j))]

/-- Happiness minus crime on block `k` is at most `bestMood`. -/
theorem mood_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hopts : ∀ j, look j ∈ opts j)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockHappiness P.c T (simulate P.c T look) look k
        - (blockCrime P.c T (simulate P.c T look) look k : Int)
      ≤ bestMood P.c P.tables (P.blockInfo spot opts k) (look k) := by
  obtain ⟨hL, hM, hTab⟩ := hP
  let d := simulate P.c T look
  let F := factorsHad P.c T d look k
  have hreal : blockHappiness P.c T d look k - (blockCrime P.c T d look k : Int)
      = ((residentsOn P.c k (look k)).map fun r =>
          moodValue residentsPerCat (happinessPerPerson (P.c.personalityOf r) F)).sum := by
    unfold blockHappiness blockCrime
    rw [foldl_add_int, foldl_add_nat]
    simp only [Int.zero_add, Nat.zero_add]
    rw [sum_sub_sum]
    rfl
  show blockHappiness P.c T d look k - (blockCrime P.c T d look k : Int) ≤ _
  rw [hreal]
  unfold bestMood
  split
  · rename_i h0
    apply Int.le_of_eq
    have : residentsOn P.c k (look k) = [] := by simp [residentsOn, h0]
    simp [this]
  · rename_i h0
    have hany : (opts k).any (·.cats > 0) = true :=
      List.any_eq_true.2 ⟨look k, hopts k, by simp; omega⟩
    let tn := P.L.transitNear.getD k (.exact false)
    let sn := P.L.stationNear.getD k (.exact false)
    let nbrs := P.L.neighbors.getD k []
    let M := mixOf P.c look (T.isNeighbor P.c k) nbrs (ownCars P.c k (look k))
    have hM512 : M < 512 := mixOf_lt P.c look _ _ _ (ownCars_lt _ _ _)
    let eachesM := Array.ofFn (n := P.c.typeCount + 1) fun ti =>
      (P.moods.getD ti.val #[]).getD (16 * M + (4 * tn.code + sn.code)) 0
    have hprof : readTable P.tables.profiles (profile P.c) = profile P.c := by
      funext x b; rw [hTab]; exact readTable_eq P.c _ x b
    have hown : readTable P.tables.own (ownCars P.c) = ownCars P.c := by
      funext x b; rw [hTab]; exact readTable_eq P.c _ x b
    have hmem : eachesM ∈ (P.blockInfo spot opts k).eaches := by
      simp only [Plan.blockInfo, hany, ite_true, hprof, hown]
      exact List.mem_map.2 ⟨M, mixOf_mem_neighborMixes P.c k opts look _ _
        (sure_neighbor P hL T hT k hk) hopts, rfl⟩
    refine Int.le_trans ?_
      (le_maxOver (moodWith (readSlot P.tables.slots P.c (P.blockInfo spot opts k).block) (look k)) _
        eachesM hmem)
    show _ ≤ moodWith (readSlot P.tables.slots P.c k) (look k) eachesM
    unfold moodWith
    rw [foldl_add_int (fun i => moodValue residentsPerCat (eachesM.getD (readSlot P.tables.slots P.c k i) 0))]
    simp only [Int.zero_add, residentsOn, List.map_map]
    apply sum_le_sum_int
    intro i _
    simp only [Function.comp_apply]
    apply moodValue_mono
    rw [hTab, readSlot_eq]
    have hti : catSlot P.c k i < P.c.typeCount + 1 := by unfold catSlot; omega
    simp only [eachesM]
    rw [getD_ofFn _ _ _ hti, hM, moodTables, getD_ofFn _ _ _ hti,
      moodTable_get _ _ _ _ hM512 (Maybe.code_lt _) (Maybe.code_lt _), Maybe.ofCode_code,
      Maybe.ofCode_code]
    simp only [catSlot]
    rw [residentType_min]
    have hML : M = mixOf P.c look (T.isNeighbor P.c k) ((Lines.make P.c P.group).neighbors.getD k [])
        (ownCars P.c k (look k)) := by simp only [M, nbrs, hL]
    have ob := ownCars_bits P.c k (look k)
    have pb := fun x b => profile_bits P.c x b
    unfold Context.personalityOf
    apply factors_covered
    · rw [hML]; exact mix_bit P.c P.group T hT look k hk 0 _ (fun x b => (pb x b).1) (ob.1 0 (by decide))
    · rw [hML]; exact mix_bit P.c P.group T hT look k hk 1 _ (fun x b => (pb x b).2.1) (ob.1 1 (by decide))
    · rw [hML]; exact mix_bit P.c P.group T hT look k hk 2 _ (fun x b => (pb x b).2.2.1) (ob.1 2 (by decide))
    · rw [hML]; exact mix_bit P.c P.group T hT look k hk 3 _ (fun x b => (pb x b).2.2.2.1) (ob.1 3 (by decide))
    · rw [hML]
      exact mix_bit P.c P.group T hT look k hk 4 _ (fun x b => (pb x b).2.2.2.2.1) (ob.1 4 (by decide))
    · rw [hML]
      exact mix_bit P.c P.group T hT look k hk 5 _ (fun x b => (pb x b).2.2.2.2.2.1) (ob.1 5 (by decide))
    · rw [hML]
      exact mix_bit P.c P.group T hT look k hk 6 _ (fun x b => (pb x b).2.2.2.2.2.2.1) (ob.1 6 (by decide))
    · apply traffic_covered P.c P.group T hT look k hk
      · rw [hML]
        exact mix_bit_cars P.c P.group T hT look k hk 7 (carsMust P.c)
          (fun x b => (pb x b).2.2.2.2.2.2.2.1) ob.2.1
      · rw [hML]
        exact mix_bit_cars P.c P.group T hT look k hk 8 (carsCould P.c)
          (fun x b => (pb x b).2.2.2.2.2.2.2.2) ob.2.2
    · simp only [tn, hL, Lines.make]; rw [getD_ofFn _ _ _ hk]
      exact covers_any_all P.group (fun T => T.served P.c k || T.nearStation P.c k) T hT
    · simp only [sn, hL, Lines.make]; rw [getD_ofFn _ _ _ hk]
      exact covers_any_all P.group (fun T => T.nearStation P.c k) T hT

theorem workers_le_info (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    workersFor P.c T look k ≤ (P.blockInfo spot opts k).workers := by
  simp only [Plan.blockInfo, hP.1]
  exact workers_le P.c P.group T hT spot look hspot k hk

theorem reached_of (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    T.stationReaches P.c k = true → (P.blockInfo spot opts k).reached = true := by
  intro h
  simp only [Plan.blockInfo, hP.1, Lines.make]
  rw [getD_ofFn _ _ _ hk]
  exact (covers_any_all P.group (fun T => T.stationReaches P.c k) T hT).2 h

/-- Productivity on block `k` is at most `jobsCap`. -/
theorem productivity_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockProductivity P.c T (simulate P.c T look) look k ≤ jobsCap (P.blockInfo spot opts k) (look k) := by
  have hW := workers_le_info P hP T hT spot opts look hspot k hk
  have hLW := localWorkers_le P.c T look k
  have hR := reached_of P hP T hT spot opts k hk
  have hfill : jobsFilled P.c T (simulate P.c T look) look k ≤
      min (look k).jobs ((P.blockInfo spot opts k).workers
        + if (P.blockInfo spot opts k).reached then stationWorkersPerBlock else 0) := by
    unfold jobsFilled stationWorkersAt
    by_cases h : T.stationReaches P.c k = true
    · simp only [h, hR h, ite_true]; omega
    · simp only [h, Bool.false_eq_true, ite_false]; split <;> omega
  have hoff : ((T.neighborsOf P.c k).filter fun j => (look j).isOffice).length
      ≤ (P.blockInfo spot opts k).offices := by
    simp only [Plan.blockInfo, hP.1, Lines.make]
    rw [getD_ofFn _ _ _ hk]
    simp only [Transit.neighborsOf, List.filter_filter, List.filter_map, List.length_map]
    apply length_filter_mono
    intro j _ h
    simp only [Bool.and_eq_true, Function.comp_apply] at h ⊢
    exact ⟨(hspot j).1.2 h.1, List.any_eq_true.2 ⟨T, hT, h.2⟩⟩
  have hfood : (T.neighborsOf P.c k).any (fun j => (look j).isFood) = true →
      (P.blockInfo spot opts k).food = true := by
    intro h
    obtain ⟨j, hj, hf⟩ := List.any_eq_true.1 h
    have hn : T.isNeighbor P.c k j = true := (List.mem_filter.1 hj).2
    have hj' : (j, P.group.all (·.isNeighbor P.c k j)) ∈ P.L.neighbors.getD k [] := by
      rw [hP.1]; simp only [Lines.make]; rw [getD_ofFn _ _ _ hk]
      exact List.mem_map.2 ⟨j, List.mem_filter.2 ⟨(List.mem_filter.1 hj).1,
        List.any_eq_true.2 ⟨T, hT, hn⟩⟩, rfl⟩
    simp only [Plan.blockInfo]
    exact List.any_eq_true.2 ⟨_, hj', (hspot j).2.1.2 hf⟩
  have hbonus : officeBonus P.c T look k ≤ bonusCap (P.blockInfo spot opts k) (look k) := by
    unfold officeBonus bonusCap
    split
    · have h1 : min officeBonusMax (officeBonusPerOffice * ((T.neighborsOf P.c k).filter fun j => (look j).isOffice).length)
          ≤ min officeBonusMax (officeBonusPerOffice * (P.blockInfo spot opts k).offices) :=
        by have := Nat.mul_le_mul_left officeBonusPerOffice hoff; omega
      have h2 : (if (T.neighborsOf P.c k).any (fun j => (look j).isFood) then lunchBonus else 0)
          ≤ (if (P.blockInfo spot opts k).food then lunchBonus else 0) := by
        by_cases hf : (T.neighborsOf P.c k).any (fun j => (look j).isFood) = true
        · simp [hf, hfood hf]
        · simp only [hf, Bool.false_eq_true, ite_false]; exact Nat.zero_le _
      omega
    · simp
  unfold blockProductivity jobsCap
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ hfill) (Nat.add_le_add_left hbonus _))

/-- Downtown jobs of block `k` are at most `downtownCap`. -/
theorem downtown_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    downtownOutput (simulate P.c T look) k
      ≤ downtownCap P.c P.tables (P.blockInfo spot opts k) (look k) := by
  have h := downtownOutput_le P.c T look k hk
  have hR := reached_of P hP T hT spot opts k hk
  unfold downtownCap
  have hblock : (P.blockInfo spot opts k).block = k := rfl
  rw [hblock, hP.2.2]
  simp only [makeTables]
  rw [readTable_eq]
  refine Nat.le_trans h (Nat.mul_le_mul_left _ ?_)
  by_cases hr : T.stationReaches P.c k = true
  · simp [hr, hR hr]
  · simp only [hr, Bool.false_eq_true, ite_false]
    split <;> simp [metroJobWorth, carJobWorth]

/-- Sales on block `k` are at most `salesCap`. -/
theorem sales_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockSales P.c T look k ≤ salesCap (P.blockInfo spot opts k) (look k) := by
  have hW := workers_le_info P hP T hT spot opts look hspot k hk
  have hR := reached_of P hP T hT spot opts k hk
  unfold blockSales salesCap
  cases look k with
  | shop h =>
    apply Nat.mul_le_mul_left
    by_cases h' : T.stationReaches P.c k = true
    · simp only [h', hR h', ite_true]; omega
    · simp only [h', Bool.false_eq_true, ite_false]; split <;> omega
  | _ => simp

/-- **One block's value is at most its cap.** -/
theorem blockValue_le_valueCap (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (hopts : ∀ j, look j ∈ opts j)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockValue P.c T (simulate P.c T look) look k
      ≤ valueCap P.c P.tables (P.blockInfo spot opts k) (look k) := by
  have h1 := mood_le P hP T hT spot opts look hopts k hk
  have h2 := productivity_le P hP T hT spot opts look hspot k hk
  have h3 := downtown_le P hP T hT spot opts look k hk
  have h4 := sales_le P hP T hT spot opts look hspot k hk
  unfold blockValue valueCap
  omega

/-! ## Costs -/

theorem costOf_eq (p : Puzzle) (s : Solution) :
    costOf p s = buildCost p s.build + transitCost s.transit := by
  unfold costOf buildCost transitCost Solution.transit
  simp only
  omega

theorem buildCost_eq (p : Puzzle) (build : List Building) :
    buildCost p build = ((List.range p.blockCount).map fun k => buildCostAt p k (build.getD k .empty)).sum := by
  unfold buildCost
  have : (fun t i => if (p.fixedAt i).isSome = true then t else t + (build.getD i .empty).cost)
      = (fun t i => t + buildCostAt p i (build.getD i .empty)) := by
    funext t i; unfold buildCostAt; split <;> simp
  rw [this, foldl_add_nat]; simp

/-! ## Adding up within the budget -/

theorem le_foldl_if_max {α : Type} (F : α → Int) (cond : α → Prop) [DecidablePred cond] :
    ∀ (l : List α) (init : Int), init ≤ l.foldl (fun m y => if cond y then max m (F y) else m) init
  | [], _ => by simp
  | y :: ys, init => by
    simp only [List.foldl_cons]
    refine Int.le_trans ?_ (le_foldl_if_max F cond ys _)
    split
    · exact Int.le_max_left _ _
    · exact Int.le_refl _

theorem mem_le_foldl_if_max {α : Type} (F : α → Int) (cond : α → Prop) [DecidablePred cond] :
    ∀ (l : List α) (init : Int) (x : α), x ∈ l → cond x →
      F x ≤ l.foldl (fun m y => if cond y then max m (F y) else m) init
  | [], _, _, h, _ => by simp at h
  | y :: ys, init, x, h, hc => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · refine Int.le_trans ?_ (le_foldl_if_max F cond ys _)
      simp only [hc, ite_true]; exact Int.le_max_right _ _
    · exact mem_le_foldl_if_max F cond ys _ x h hc

/-- One pick per list: `xs` has an item of each list in `vals`. -/
def Picks {α : Type} (xs : List α) (vals : List (List α)) : Prop :=
  xs.length = vals.length ∧ ∀ q ∈ xs.zip vals, q.1 ∈ q.2

theorem picks_cons {α : Type} {x : α} {xs : List α} {opts : List α} {vals : List (List α)}
    (h : Picks (x :: xs) (opts :: vals)) : x ∈ opts ∧ Picks xs vals := by
  obtain ⟨hl, hm⟩ := h
  exact ⟨hm (x, opts) (by simp), by simpa using hl, fun q hq => hm q (by simp [hq])⟩

/-- **The knapsack is right**: any picks whose costs fit add up to at most the
knapsack's answer. -/
theorem knapsack_ge (units : Nat) :
    ∀ (vals : List (List (Int × Nat))) (xs : List (Int × Nat)) (r : Nat), Picks xs vals → r ≤ units →
      (xs.map (·.2 / 30)).sum ≤ r →
      (xs.map (·.1)).sum ≤ (vals.foldr (knapsackRow units) (Array.replicate (units + 1) 0)).getD r impossible
  | [], xs, r, h, hr, _ => by
    have : xs = [] := by cases xs <;> simp_all [Picks]
    subst this
    have hr' : r < units + 1 := by omega
    simp [Array.getD_eq_getD_getElem?, hr']
  | opts :: vals, [], r, h, _, _ => by simp [Picks] at h
  | opts :: vals, x :: xs, r, h, hr, hsum => by
    obtain ⟨hx, hxs⟩ := picks_cons h
    simp only [List.map_cons, List.sum_cons] at hsum ⊢
    have ih := knapsack_ge units vals xs (r - x.2 / 30) hxs (by omega) (by omega)
    rw [List.foldr_cons]
    unfold knapsackRow
    rw [getD_ofFn _ _ _ (by omega)]
    refine Int.le_trans ?_ (mem_le_foldl_if_max
      (fun y => y.1 + (vals.foldr (knapsackRow units) (Array.replicate (units + 1) 0)).getD (r - y.2 / 30) impossible)
      (fun y => y.2 / 30 ≤ r) opts impossible x hx (by omega))
    omega

theorem sum_div_le {α : Type} (f : α → Nat) :
    ∀ l : List α, (l.map fun x => f x / 30).sum ≤ (l.map f).sum / 30
  | [] => by simp
  | x :: xs => by
    have := sum_div_le f xs
    simp only [List.map_cons, List.sum_cons]; omega

theorem bestTrade_ge (rate : Nat) (opts : List (Int × Nat)) (x : Int × Nat) (hx : x ∈ opts) :
    4 * x.1 - (rate * x.2 : Nat) ≤ bestTrade rate opts := by
  cases opts with
  | nil => simp at hx
  | cons y ys =>
    simp only [bestTrade]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_foldl_max (fun x : Int × Nat => 4 * x.1 - (rate * x.2 : Nat)) ys _
    · exact mem_le_foldl_max (fun x : Int × Nat => 4 * x.1 - (rate * x.2 : Nat)) ys _ x hx

theorem sum_picks_le {β : Type} (F : β → Int) (G : List β → Int) (hG : ∀ opts x, x ∈ opts → F x ≤ G opts) :
    ∀ (vals : List (List β)) (xs : List β), Picks xs vals → (xs.map F).sum ≤ (vals.map G).sum
  | [], xs, h => by
    have : xs = [] := by cases xs <;> simp_all [Picks]
    subst this; simp
  | opts :: vals, [], h => by simp [Picks] at h
  | opts :: vals, x :: xs, h => by
    obtain ⟨hx, hxs⟩ := picks_cons h
    have := sum_picks_le F G hG vals xs hxs
    have := hG opts x hx
    simp only [List.map_cons, List.sum_cons]; omega

/-- **The trade-off bound is right**, for any rate. -/
theorem tradeBound_ge (vals : List (List (Int × Nat))) (xs : List (Int × Nat)) (h : Picks xs vals)
    (left : Nat) (hcost : (xs.map (·.2)).sum ≤ left) (rate : Nat) :
    (xs.map (·.1)).sum ≤ tradeBound vals left rate := by
  unfold tradeBound
  apply Int.le_ediv_of_mul_le (by decide)
  have h1 := sum_picks_le (fun x : Int × Nat => 4 * x.1 - (rate * x.2 : Nat)) (bestTrade rate)
    (fun opts x hx => bestTrade_ge rate opts x hx) vals xs h
  have h2 : (xs.map fun x : Int × Nat => 4 * x.1 - (rate * x.2 : Nat)).sum
      = 4 * (xs.map (·.1)).sum - (rate * (xs.map (·.2)).sum : Nat) := by
    clear h h1 hcost
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]; push_cast; omega
  have h3 : rate * (xs.map (·.2)).sum ≤ rate * left := Nat.mul_le_mul_left _ hcost
  omega

/-! ## The bound for a search node -/

theorem spotAt_eq (c : Context) (opts : List (List Building)) (j : Nat) :
    spotAt (spotTable c opts) opts j = Spot.of (optsAt opts j) := by
  unfold spotAt
  split
  · simp [spotTable]
  · rfl

/-- A layout fits a search node: its transit is one of the plan's, and each
block holds one of its options. -/
def FitsNode (P : Plan) (opts : List (List Building)) (t : Solution) : Prop :=
  t.transit ∈ P.group ∧ ∀ j, t.look j ∈ optsAt opts j

def first (x : Int × Int × Nat) : Int × Nat := (x.1, x.2.2)
def second (x : Int × Int × Nat) : Int × Nat := (x.2.1, x.2.2)

/-- The spots at a node. -/
def nodeSpot (P : Plan) (opts : List (List Building)) : Nat → Spot := spotAt (spotTable P.c opts) opts

/-- Each block's cap (picked by `proj`) and cost, for the building layout `t`
puts on it. -/
def capsOf (P : Plan) (opts : List (List Building)) (t : Solution) (proj : Int × Int × Nat → Int × Nat) :
    List (Int × Nat) :=
  P.c.blocks.map fun k => proj (P.capRow (nodeSpot P opts) (optsAt opts) k (t.look k))

theorem optionValues_eq (P : Plan) (opts : List (List Building)) :
    P.optionValues opts
      = (P.c.blocks.map fun k => (optsAt opts k).map fun b => first (P.capRow (nodeSpot P opts) (optsAt opts) k b),
         P.c.blocks.map fun k => (optsAt opts k).map fun b => second (P.capRow (nodeSpot P opts) (optsAt opts) k b)) := by
  simp [Plan.optionValues, Plan.capRow, first, second, nodeSpot, List.map_map, Function.comp_def]

theorem score_le_caps (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hfit : FitsNode P opts t) :
    score p t ≤ ((capsOf P opts t first).map (·.1)).sum := by
  obtain ⟨hT, hopts⟩ := hfit
  have hspot : ∀ j, (nodeSpot P opts j).Admits (t.look j) := fun j => by
    unfold nodeSpot; rw [spotAt_eq]; exact Spot.admits_of _ _ (hopts j)
  unfold score scoreWith
  dsimp only
  rw [← hc, foldl_add_int]
  simp only [Int.zero_add, capsOf, List.map_map]
  have hle : ((P.c.blocks.map (blockValue P.c t.transit (simulate P.c t.transit t.look) t.look))).sum
      ≤ ((P.c.blocks.map ((·.1) ∘ fun k => first (P.capRow (nodeSpot P opts) (optsAt opts) k (t.look k))))).sum := by
    apply sum_le_sum_int
    intro k hk
    exact blockValue_le_valueCap P hP t.transit hT _ _ t.look hspot hopts k (List.mem_range.1 hk)
  omega

theorem score_le_capsW (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hfit : FitsNode P opts t) :
    score p t ≤ ((capsOf P opts t second).map (·.1)).sum := by
  have h := score_le_caps p P hP hc opts t hfit
  have : capsOf P opts t second = capsOf P opts t first := by
    simp [capsOf, first, second, Plan.capRow, valueCapW]
  rw [this]; exact h

theorem picks_capsOf (P : Plan) (opts : List (List Building)) (t : Solution)
    (hopts : ∀ j, t.look j ∈ optsAt opts j) (proj : Int × Int × Nat → Int × Nat) :
    Picks (capsOf P opts t proj)
      (P.c.blocks.map fun k => (optsAt opts k).map fun b => proj (P.capRow (nodeSpot P opts) (optsAt opts) k b)) := by
  refine ⟨by simp [capsOf], ?_⟩
  intro q hq
  simp only [capsOf] at hq
  obtain ⟨k, _, rfl⟩ := mem_zip_map_same _ _ _ _ hq
  exact List.mem_map.2 ⟨t.look k, hopts k, rfl⟩

theorem cost_capsOf (p : Puzzle) (P : Plan) (hc : P.c = prepare p) (opts : List (List Building))
    (t : Solution) (proj : Int × Int × Nat → Int × Nat) (hproj : ∀ x, (proj x).2 = x.2.2) :
    ((capsOf P opts t proj).map (·.2)).sum = buildCost p t.build := by
  rw [buildCost_eq]
  simp only [capsOf, List.map_map, Function.comp_def, hproj]
  have hpz : P.c.puzzle = p := by rw [hc]; rfl
  unfold Context.blocks
  simp only [Plan.capRow, hpz, Solution.look]

theorem leastCost_le (c : Context) (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group) :
    P.L.leastCost ≤ transitCost T := by
  rw [hP.1]; exact leastOf_le transitCost P.group T hT

/-- With the costs of a valid layout that fits the node, the caps fit the
budget left after the cheapest transit. -/
theorem caps_fit_budget (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t)
    (proj : Int × Int × Nat → Int × Nat) (hproj : ∀ x, (proj x).2 = x.2.2) :
    ((capsOf P opts t proj).map (·.2)).sum ≤ p.budget - P.L.leastCost := by
  rw [cost_capsOf p P hc opts t proj hproj]
  have h1 := hv.2.1
  simp only [prepare_puzzle] at h1
  rw [costOf_eq] at h1
  have := leastCost_le P.c P hP _ hfit.1
  omega

theorem boundOne_ge (p : Puzzle) (P : Plan) (hc : P.c = prepare p) (vals : List (List (Int × Nat)))
    (xs : List (Int × Nat)) (hpicks : Picks xs vals) (hcost : (xs.map (·.2)).sum ≤ p.budget - P.L.leastCost) :
    (xs.map (·.1)).sum ≤ P.boundOne vals := by
  have hpz : P.c.puzzle = p := by rw [hc]; rfl
  unfold Plan.boundOne
  simp only [hpz]
  apply le_foldl_min
  · exact tradeBound_ge _ _ hpicks _ hcost 0
  · intro r _; exact tradeBound_ge _ _ hpicks _ hcost r

/-- **The quick bound is safe**: no valid layout that fits the node scores more. -/
theorem score_le_bound (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) :
    score p t ≤ P.bound opts := by
  unfold Plan.bound Plan.boundFrom
  rw [optionValues_eq]
  apply Int.le_min.2
  refine ⟨?_, ?_⟩
  · exact Int.le_trans (score_le_caps p P hP hc opts t hfit)
      (boundOne_ge p P hc _ _ (picks_capsOf P opts t hfit.2 first)
        (caps_fit_budget p P hP hc opts t hv hfit first (fun _ => rfl)))
  · exact Int.le_trans (score_le_capsW p P hP hc opts t hfit)
      (boundOne_ge p P hc _ _ (picks_capsOf P opts t hfit.2 second)
        (caps_fit_budget p P hP hc opts t hv hfit second (fun _ => rfl)))

theorem knapsack_bound_ge (p : Puzzle) (P : Plan) (hc : P.c = prepare p) (vals : List (List (Int × Nat)))
    (xs : List (Int × Nat)) (hpicks : Picks xs vals) (hcost : (xs.map (·.2)).sum ≤ p.budget - P.L.leastCost) :
    (xs.map (·.1)).sum ≤ knapsack vals ((P.c.puzzle.budget - P.L.leastCost) / 30) := by
  have hdiv := sum_div_le (fun x : Int × Nat => x.2) xs
  have hpz : P.c.puzzle = p := by rw [hc]; rfl
  unfold knapsack
  simp only [hpz]
  refine knapsack_ge _ _ _ _ hpicks (Nat.le_refl _) ?_
  exact Nat.le_trans hdiv (Nat.div_le_div_right hcost)

/-- **The knapsack bound is safe**: no valid layout that fits the node scores
more. -/
theorem score_le_knapsackBound (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) :
    score p t ≤ P.knapsackBound opts := by
  unfold Plan.knapsackBound Plan.knapsackFrom
  rw [optionValues_eq]
  apply Int.le_min.2
  refine ⟨?_, ?_⟩
  · exact Int.le_trans (score_le_caps p P hP hc opts t hfit)
      (knapsack_bound_ge p P hc _ _ (picks_capsOf P opts t hfit.2 first)
        (caps_fit_budget p P hP hc opts t hv hfit first (fun _ => rfl)))
  · exact Int.le_trans (score_le_capsW p P hP hc opts t hfit)
      (knapsack_bound_ge p P hc _ _ (picks_capsOf P opts t hfit.2 second)
        (caps_fit_budget p P hP hc opts t hv hfit second (fun _ => rfl)))

/-- **The cost cut is safe**: a layout that fits the node costs at least the
cheapest buildings plus the cheapest transit. -/
theorem leastBuildCost_le (p : Puzzle) (P : Plan) (hP : P.Sound) (opts : List (List Building))
    (t : Solution) (hfit : FitsNode P opts t) :
    leastBuildCost p opts + P.L.leastCost ≤ costOf p t := by
  rw [costOf_eq, buildCost_eq]
  have := leastCost_le P.c P hP _ hfit.1
  have : leastBuildCost p opts ≤ ((List.range p.blockCount).map fun k => buildCostAt p k (t.build.getD k .empty)).sum := by
    unfold leastBuildCost
    rw [foldl_add_nat]
    simp only [Nat.zero_add]
    apply sum_le_sum_nat
    intro k _
    exact leastOf_le _ _ _ (hfit.2 k)
  omega

end SevenBridges
