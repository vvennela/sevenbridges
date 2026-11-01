import SevenBridges.Bound

/-!
# The bound is safe

`score_le_knapsackBound` and `score_le_bound`: no valid layout that fits a
search node scores more than the node's bound. Also: the cost cut and the
station cut never throw away a valid layout.
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
  s.park.Covers b.isPark ∧ s.bar.Covers b.isBar ∧ s.shop.Covers b.isShop
  ∧ s.loud.Covers b.isLoud ∧ s.housing.Covers b.isHousing
  ∧ s.office.Covers b.isOffice ∧ b.residents ≤ s.residents

theorem Spot.admits_of (l : List Building) (b : Building) (hb : b ∈ l) : (Spot.of l).Admits b :=
  ⟨Maybe.covers_ofTest _ _ _ hb, Maybe.covers_ofTest _ _ _ hb, Maybe.covers_ofTest _ _ _ hb,
   Maybe.covers_ofTest _ _ _ hb, Maybe.covers_ofTest _ _ _ hb,
   Maybe.covers_ofTest _ _ _ hb, mem_le_foldl_max_nat Building.residents l 0 b hb⟩

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

theorem profile_lt (b : Building) : b.profile < 64 := by
  cases b <;> (try rename_i h; cases h) <;> decide

theorem profile_bits (b : Building) :
    b.profile.testBit 0 = b.isPark ∧ b.profile.testBit 1 = b.isBar ∧ b.profile.testBit 2 = b.isShop
    ∧ b.profile.testBit 3 = b.isLoud
    ∧ b.profile.testBit 4 = b.isHousing ∧ b.profile.testBit 5 = b.isOffice := by
  cases b <;> (try rename_i h; cases h) <;> decide

theorem or_lt_64 {a b : Nat} (ha : a < 64) (hb : b < 64) : a ||| b < 64 :=
  Nat.or_lt_two_pow (n := 6) ha hb

/-- What block `x.1` actually offers: its profile if it is an actual neighbor
(`sel`), else nothing. -/
def pick (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) : Nat :=
  if sel x.1 then (look x.1).profile else 0

theorem pick_lt (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) : pick look sel x < 64 := by
  unfold pick; split
  · exact profile_lt _
  · decide

theorem testBit_pick (look : Nat → Building) (sel : Nat → Bool) (x : Nat × Bool) (i : Nat) :
    (pick look sel x).testBit i = (sel x.1 && (look x.1).profile.testBit i) := by
  unfold pick; cases sel x.1 <;> simp

/-- The mix the blocks in `nbrs` that are actual neighbors (`sel`) offer. -/
def mixOf (look : Nat → Building) (sel : Nat → Bool) (nbrs : List (Nat × Bool)) (a : Nat := 0) : Nat :=
  nbrs.foldl (fun m x => m ||| pick look sel x) a

theorem testBit_mixOf (look : Nat → Building) (sel : Nat → Bool) (i : Nat) :
    ∀ (nbrs : List (Nat × Bool)) (a : Nat),
      (mixOf look sel nbrs a).testBit i
        = (a.testBit i || nbrs.any fun x => sel x.1 && (look x.1).profile.testBit i)
  | [], a => by simp [mixOf]
  | x :: xs, a => by
    simp only [mixOf, List.foldl_cons] at *
    rw [show List.foldl (fun m x => m ||| pick look sel x) (a ||| pick look sel x) xs
      = mixOf look sel xs (a ||| pick look sel x) from rfl, testBit_mixOf look sel i xs]
    simp [Nat.testBit_or, testBit_pick, Bool.or_assoc]

theorem mixOf_lt (look : Nat → Building) (sel : Nat → Bool) :
    ∀ (nbrs : List (Nat × Bool)) (a : Nat), a < 64 → mixOf look sel nbrs a < 64
  | [], _, h => h
  | x :: xs, a, h => mixOf_lt look sel xs _ (or_lt_64 h (pick_lt look sel x))

/-- The marks table is 64 long, every marked mix is listed, and every listed
mix is below 128. -/
def MarksOk (acc : Array Bool × List Nat) : Prop :=
  acc.1.size = 64 ∧ (∀ x, acc.1.getD x false = true → x ∈ acc.2) ∧ (∀ x ∈ acc.2, x < 64)

theorem getD_setIfInBounds (a : Array Bool) (i j : Nat) :
    (a.setIfInBounds i true).getD j false = if i = j ∧ i < a.size then true else a.getD j false := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < a.size <;> simp [h2]
  · simp [h1]

theorem markMix_ok (acc : Array Bool × List Nat) (x : Nat) (hx : x < 64) (h : MarksOk acc) :
    MarksOk (markMix acc x) := by
  obtain ⟨hs, hm, hl⟩ := h
  unfold markMix
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

theorem markMix_marked (acc : Array Bool × List Nat) (x : Nat) (hx : x < 64) (h : MarksOk acc) :
    (markMix acc x).1.getD x false = true := by
  unfold markMix
  split
  · assumption
  · simp [Array.set!_eq_setIfInBounds, getD_setIfInBounds, h.1, hx]

theorem markMix_mono (acc : Array Bool × List Nat) (x y : Nat) (h : acc.1.getD y false = true) :
    (markMix acc x).1.getD y false = true := by
  unfold markMix
  split
  · exact h
  · simp only [Array.set!_eq_setIfInBounds, getD_setIfInBounds]; split <;> simp_all

theorem addNeighbor_spec (mixes profiles : List Nat) (hm : ∀ m ∈ mixes, m < 64)
    (hp : ∀ q ∈ profiles, q < 64) :
    (∀ x ∈ addNeighbor mixes profiles, x < 64)
    ∧ ∀ m ∈ mixes, ∀ q ∈ profiles, m ||| q ∈ addNeighbor mixes profiles := by
  let inner (acc : Array Bool × List Nat) (m : Nat) :=
    profiles.foldl (fun acc q => markMix acc (m ||| q)) acc
  have hinner : ∀ acc m, m ∈ mixes → MarksOk acc → MarksOk (inner acc m) := fun acc m hmm hacc =>
    foldl_inv _ MarksOk profiles acc hacc fun b q hq hb => markMix_ok b _ (or_lt_64 (hm m hmm) (hp q hq)) hb
  have hinit : MarksOk (Array.replicate 64 false, []) := by
    refine ⟨by simp, ?_, by simp⟩
    intro x hx
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hx
    split at hx <;> simp at hx
  have hok : MarksOk (mixes.foldl inner (Array.replicate 64 false, [])) :=
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
    profiles b q hq hb (fun b' q' hq' hb' => markMix_ok b' _ (or_lt_64 (hm m hmm) (hp q' hq')) hb')
    (fun b' hb' => markMix_marked b' x (or_lt_64 (hm m hmm) (hp q hq)) hb')
    (fun b' q' _ _ hb' => markMix_mono b' _ x hb')

/-- The mix the actual neighbors offer is among the mixes considered, when
every sure neighbor is an actual one and every actual neighbor holds one of its
options. -/
theorem mixOf_mem_neighborMixes (opts : Nat → List Building) (look : Nat → Building) (sel : Nat → Bool)
    (nbrs : List (Nat × Bool)) (hsure : ∀ x ∈ nbrs, x.2 = true → sel x.1 = true)
    (hlook : ∀ x ∈ nbrs, sel x.1 = true → look x.1 ∈ opts x.1) :
    mixOf look sel nbrs ∈ neighborMixes nbrs opts := by
  unfold neighborMixes
  suffices ∀ (nbrs : List (Nat × Bool)) (mixes : List Nat) (a : Nat),
      (∀ x ∈ nbrs, x.2 = true → sel x.1 = true) → (∀ x ∈ nbrs, sel x.1 = true → look x.1 ∈ opts x.1) →
      a ∈ mixes → (∀ m ∈ mixes, m < 64) → a < 64 →
      mixOf look sel nbrs a ∈ nbrs.foldl (fun mixes x => addNeighbor mixes (offers opts x)) mixes by
    exact this _ [0] 0 hsure hlook (by simp) (by simp) (by decide)
  intro nbrs
  induction nbrs with
  | nil => intro mixes a _ _ ha _ _; simpa [mixOf] using ha
  | cons x xs ih =>
    intro mixes a hs hl ha hm halt
    simp only [List.foldl_cons]
    have hp : ∀ q ∈ offers opts x, q < 64 := by
      intro q hq
      simp only [offers, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨b, _, rfl⟩ | hq
      · exact profile_lt b
      · split at hq
        · simp at hq
        · simp only [List.mem_singleton] at hq; subst hq; decide
    have hq : pick look sel x ∈ offers opts x := by
      unfold pick offers
      by_cases hsel : sel x.1 = true
      · simp only [hsel, ite_true]
        exact List.mem_append_left _ (List.mem_map.2 ⟨look x.1, hl x (by simp) hsel, rfl⟩)
      · have h2 : x.2 = false := by
          cases h : x.2
          · rfl
          · exact absurd (hs x (by simp) h) hsel
        simp [hsel, h2]
    have spec := addNeighbor_spec mixes _ hm hp
    exact ih _ _ (fun y hy => hs y (by simp [hy])) (fun y hy => hl y (by simp [hy]))
      (spec.2 a ha _ hq) spec.1 (or_lt_64 halt (pick_lt look sel x))

/-- "A neighbor has it", read off the actual mix, is exactly right. -/
theorem ofMask_mixOf (look : Nat → Building) (sel : Nat → Bool) (nbrs : List (Nat × Bool)) :
    (Spot.ofMask (mixOf look sel nbrs)).park = .exact (nbrs.any fun x => sel x.1 && (look x.1).isPark)
    ∧ (Spot.ofMask (mixOf look sel nbrs)).bar = .exact (nbrs.any fun x => sel x.1 && (look x.1).isBar)
    ∧ (Spot.ofMask (mixOf look sel nbrs)).shop = .exact (nbrs.any fun x => sel x.1 && (look x.1).isShop)
    ∧ (Spot.ofMask (mixOf look sel nbrs)).loud = .exact (nbrs.any fun x => sel x.1 && (look x.1).isLoud)
    ∧ (Spot.ofMask (mixOf look sel nbrs)).housing = .exact (nbrs.any fun x => sel x.1 && (look x.1).isHousing)
    ∧ (Spot.ofMask (mixOf look sel nbrs)).office = .exact (nbrs.any fun x => sel x.1 && (look x.1).isOffice) := by
  simp only [Spot.ofMask, testBit_mixOf, Nat.zero_testBit, Bool.false_or]
  have := fun j => profile_bits (look j)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [this]

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
theorem factors_covered (c : Context) (T : Transit) (look : Nat → Building) (t : Personality) (h : Nat)
    (near : (Spot → Maybe) → Maybe) (tn : Maybe)
    (hpark : (near (·.park)).Covers ((T.neighborsOf c h).any fun j => (look j).isPark))
    (hbar : (near (·.bar)).Covers ((T.neighborsOf c h).any fun j => (look j).isBar))
    (hshop : (near (·.shop)).Covers ((T.neighborsOf c h).any fun j => (look j).isShop))
    (hloud : (near (·.loud)).Covers ((T.neighborsOf c h).any fun j => (look j).isLoud))
    (hhousing : (near (·.housing)).Covers ((T.neighborsOf c h).any fun j => (look j).isHousing))
    (hoffice : (near (·.office)).Covers ((T.neighborsOf c h).any fun j => (look j).isOffice))
    (htn : tn.Covers (T.served c h || T.nearStation c h)) :
    happinessPerPerson t (factorsHad c T look h) ≤ bestEach t (factorMaybe near tn) := by
  unfold factorsHad
  apply hpp_filter_le
  intro f
  cases f with
  | parks => exact hpark
  | nightlife => exact hbar
  | quiet => exact Maybe.covers_not hloud
  | transit => exact htn
  | shops => exact hshop
  | variety =>
    simp only [factorMaybe]
    have := Maybe.covers_atLeast 3
      [(near (·.housing), (T.neighborsOf c h).any fun j => (look j).isHousing),
       (near (·.office), (T.neighborsOf c h).any fun j => (look j).isOffice),
       (near (·.shop), (T.neighborsOf c h).any fun j => (look j).isShop),
       (near (·.park), (T.neighborsOf c h).any fun j => (look j).isPark),
       (near (·.bar), (T.neighborsOf c h).any fun j => (look j).isBar)]
      (by simp only [List.mem_cons, List.mem_nil_iff, or_false]
          rintro p (rfl | rfl | rfl | rfl | rfl) <;> assumption)
    simp only [List.map_cons, List.map_nil] at this
    rw [length_filter_eq_map]
    exact this

/-! ## Facts about the transit -/

/-- A plan is set up as `makePlan` sets it up. -/
def Plan.Sound (P : Plan) : Prop := P.L = Lines.make P.c P.group ∧ P.moods = moodTables P.c

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (k : Nat) (d : α) (hk : k < n) :
    (Array.ofFn f).getD k d = f ⟨k, hk⟩ := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem covers_any_all {α : Type} (Ts : List α) (F : α → Bool) (T : α) (hT : T ∈ Ts) :
    (⟨Ts.any F, Ts.all F⟩ : Maybe).Covers (F T) := by
  constructor
  · intro h; simp only [List.all_eq_true] at h; exact h T hT
  · intro h; simp only [List.any_eq_true]; exact ⟨T, hT, h⟩

theorem makePlan_sound (c : Context) (moods : Array (Array Int)) (Ts : List Transit)
    (h : moods = moodTables c) : (makePlan c moods Ts).Sound := ⟨rfl, h⟩

theorem moodTable_get (p : Personality) (m t : Nat) (hm : m < 64) (ht : t < 4) :
    (moodTable p).getD (4 * m + t) 0
      = bestEach p (factorMaybe (fun sel => sel (Spot.ofMask m)) (Maybe.ofCode t)) := by
  unfold moodTable
  rw [getD_ofFn _ _ _ (by omega)]
  have e1 : (4 * m + t) / 4 = m := by omega
  have e3 : (4 * m + t) % 4 = t := by omega
  simp only [e1, e3]

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
  | cons e es =>
    simp only [maxOver]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_foldl_max F es _
    · exact mem_le_foldl_max F es _ x hx

theorem length_filter_mono {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length
  | [], _ => by simp
  | x :: xs, h => by
    have ih := length_filter_mono p q xs (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    by_cases hp : p x = true
    · simp [hp, hx _]; omega
    · by_cases hq : q x = true <;> simp [hp, hq] <;> omega

/-! ## One block's value is at most its cap -/

theorem getD_map_range {α : Type} (f : Nat → α) (n i : Nat) (d : α) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, hi]

/-- The workers who can reach block `k` are at most the cap's workers. -/
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
  · intro h _; exact (hspot h).2.2.2.2.2.2

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

theorem covers_nbr (P : Plan) (hL : P.L = Lines.make P.c P.group) (T : Transit) (hT : T ∈ P.group)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) (test : Nat → Bool) :
    (Maybe.exact ((P.L.neighbors.getD k []).any fun x => T.isNeighbor P.c k x.1 && test x.1)).Covers
      ((T.neighborsOf P.c k).any test) := by
  rw [hL, any_neighbors P.c P.group T hT k hk test]
  exact Maybe.covers_exact _

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

/-- Happiness minus crime on block `k` is at most `bestMood`. -/
theorem mood_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (hopts : ∀ j, look j ∈ opts j)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockHappiness P.c T look k - (blockCrime P.c T look k : Int)
      ≤ bestMood P.c (P.blockInfo spot opts k) (look k) := by
  obtain ⟨hL, hM⟩ := hP
  have hreal : blockHappiness P.c T look k - (blockCrime P.c T look k : Int)
      = ((List.range P.c.typeCount).map fun ti => moodValue (typeResidents (look k) (P.c.residentType ti))
          (happinessPerPerson (P.c.residentType ti).personality (factorsHad P.c T look k))).sum := by
    unfold blockHappiness blockCrime
    rw [foldl_add_int, foldl_add_nat]
    simp only [Int.zero_add, Nat.zero_add]
    rw [sum_sub_sum]
    rfl
  rw [hreal]
  unfold bestMood
  split
  · rename_i h0
    apply Int.le_of_eq
    have : ∀ ti, typeResidents (look k) (P.c.residentType ti) = 0 := by
      intro ti; simp [typeResidents, h0]
    simp only [this, moodValue, Int.natCast_zero, Int.zero_mul, Nat.mul_zero, Int.sub_zero]
    induction (List.range P.c.typeCount) <;> simp_all
  · rename_i h0
    have hany : (opts k).any (·.residents > 0) = true :=
      List.any_eq_true.2 ⟨look k, hopts k, by simp; omega⟩
    let near := P.L.transitNear.getD k (.exact false)
    let M := mixOf look (T.isNeighbor P.c k) (P.L.neighbors.getD k [])
    have hM128 : M < 64 := mixOf_lt look _ _ 0 (by decide)
    let eachesM := (List.range P.c.typeCount).map fun ti =>
      (P.moods.getD ti #[]).getD (4 * M + near.code) 0
    have hmem : eachesM ∈ (P.blockInfo spot opts k).eaches := by
      simp only [Plan.blockInfo, hany, ite_true]
      exact List.mem_map.2 ⟨M, mixOf_mem_neighborMixes opts look _ _
        (sure_neighbor P hL T hT k hk) (fun x _ _ => hopts x.1), rfl⟩
    refine Int.le_trans ?_ (le_maxOver (moodWith P.c (look k)) _ eachesM hmem)
    unfold moodWith
    rw [foldl_add_int (fun ti => moodValue (typeResidents (look k) (P.c.residentType ti)) (eachesM.getD ti 0))]
    simp only [Int.zero_add]
    apply sum_le_sum_int
    intro gi hgi
    have hgi' : gi < P.c.typeCount := List.mem_range.1 hgi
    apply moodValue_mono
    simp only [eachesM]
    rw [getD_map_range _ _ _ _ hgi', hM, moodTables, getD_ofFn _ _ _ hgi',
      moodTable_get _ _ _ hM128 (Maybe.code_lt _), Maybe.ofCode_code]
    have hbits := ofMask_mixOf look (T.isNeighbor P.c k) (P.L.neighbors.getD k [])
    have hcov := covers_nbr P hL T hT k hk
    apply factors_covered
    · show (Spot.ofMask M).park.Covers _
      rw [hbits.1]; exact hcov fun j => (look j).isPark
    · show (Spot.ofMask M).bar.Covers _
      rw [hbits.2.1]; exact hcov fun j => (look j).isBar
    · show (Spot.ofMask M).shop.Covers _
      rw [hbits.2.2.1]; exact hcov fun j => (look j).isShop
    · show (Spot.ofMask M).loud.Covers _
      rw [hbits.2.2.2.1]; exact hcov fun j => (look j).isLoud
    · show (Spot.ofMask M).housing.Covers _
      rw [hbits.2.2.2.2.1]; exact hcov fun j => (look j).isHousing
    · show (Spot.ofMask M).office.Covers _
      rw [hbits.2.2.2.2.2]; exact hcov fun j => (look j).isOffice
    · simp only [near, hL, Lines.make]; rw [getD_ofFn _ _ _ hk]
      exact covers_any_all P.group (fun T => T.served P.c k || T.nearStation P.c k) T hT

theorem workers_le_info (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    workersFor P.c T look k ≤ (P.blockInfo spot opts k).workers := by
  simp only [Plan.blockInfo, hP.1]
  exact workers_le P.c P.group T hT spot look hspot k hk

/-- Productivity on block `k` is at most `jobsCap`. -/
theorem productivity_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockProductivity P.c T look k ≤ jobsCap (P.blockInfo spot opts k) (look k) := by
  have hW := workers_le_info P hP T hT spot opts look hspot k hk
  have hR : T.stationReaches P.c k = true → (P.blockInfo spot opts k).reached = true := by
    intro h
    simp only [Plan.blockInfo, hP.1, Lines.make]
    rw [getD_ofFn _ _ _ hk]
    exact (covers_any_all P.group (fun T => T.stationReaches P.c k) T hT).2 h
  have hfill : jobsFilled P.c T look k ≤
      (if (P.blockInfo spot opts k).reached then (look k).jobs
       else min (look k).jobs (P.blockInfo spot opts k).workers) := by
    unfold jobsFilled
    by_cases h : T.stationReaches P.c k = true
    · simp [h, hR h]
    · simp only [h, Bool.false_eq_true, ite_false]
      by_cases hr : (P.blockInfo spot opts k).reached = true <;> simp only [hr, ite_true, Bool.false_eq_true, ite_false] <;> omega
  have hoff : ((T.neighborsOf P.c k).filter fun j => (look j).isOffice).length
      ≤ (P.blockInfo spot opts k).offices := by
    simp only [Plan.blockInfo, hP.1, Lines.make]
    rw [getD_ofFn _ _ _ hk]
    simp only [Transit.neighborsOf, List.filter_filter, List.filter_map, List.length_map]
    apply length_filter_mono
    intro j _ h
    simp only [Bool.and_eq_true, Function.comp_apply] at h ⊢
    exact ⟨(hspot j).2.2.2.2.2.1.2 h.1, List.any_eq_true.2 ⟨T, hT, h.2⟩⟩
  have hbonus : officeBonus P.c T look k ≤
      (if (look k).isOffice then
        min officeBonusMax (officeBonusPerOffice * (P.blockInfo spot opts k).offices)
       else 0) := by
    unfold officeBonus
    split
    · have h1 : min officeBonusMax (officeBonusPerOffice * ((T.neighborsOf P.c k).filter fun j => (look j).isOffice).length)
          ≤ min officeBonusMax (officeBonusPerOffice * (P.blockInfo spot opts k).offices) :=
        by have := Nat.mul_le_mul_left officeBonusPerOffice hoff; omega
      omega
    · simp
  unfold blockProductivity jobsCap
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ hfill) (Nat.add_le_add_left hbonus _))

/-- Sales on block `k` are at most `salesCap`. -/
theorem sales_le (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockSales P.c T look k ≤ salesCap (P.blockInfo spot opts k) (look k) := by
  have hW := workers_le_info P hP T hT spot opts look hspot k hk
  unfold blockSales salesCap
  cases look k with
  | shop h => exact Nat.mul_le_mul_left _ (by omega)
  | _ => simp

/-- **One block's value is at most its cap.** -/
theorem blockValue_le_valueCap (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group)
    (spot : Nat → Spot) (opts : Nat → List Building) (look : Nat → Building)
    (hspot : ∀ j, (spot j).Admits (look j)) (hopts : ∀ j, look j ∈ opts j)
    (k : Nat) (hk : k < P.c.puzzle.blockCount) :
    blockValue P.c T look k ≤ valueCap P.c (P.blockInfo spot opts k) (look k) := by
  have h1 := mood_le P hP T hT spot opts look hspot hopts k hk
  have h2 := productivity_le P hP T hT spot opts look hspot k hk
  have h3 := sales_le P hP T hT spot opts look hspot k hk
  unfold blockValue valueCap
  omega

/-! ## A block's value only depends on the blocks it watches -/

theorem any_congr_mem {α : Type} (f g : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.any f = l.any g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.any_cons, h x (by simp), any_congr_mem f g xs (fun y hy => h y (by simp [hy]))]

theorem mem_watched_of_neighbor (c : Context) (T : Transit) (k j : Nat) (h : j ∈ T.neighborsOf c k) :
    j ∈ T.watched c k := by
  simp [Transit.watched, h]

theorem mem_watched_of_bus (c : Context) (T : Transit) (k j : Nat) (hj : j ∈ c.blocks)
    (h : T.busLinked c k j = true) : j ∈ T.watched c k := by
  simp [Transit.watched, hj, h]

theorem factorsHad_congr (c : Context) (T : Transit) (look look' : Nat → Building) (k : Nat)
    (h : ∀ j ∈ T.watched c k, look j = look' j) :
    factorsHad c T look k = factorsHad c T look' k := by
  have hn : ∀ (test : Building → Bool),
      ((T.neighborsOf c k).any fun j => test (look j)) = ((T.neighborsOf c k).any fun j => test (look' j)) :=
    fun test => any_congr_mem _ _ _ fun j hj => by rw [h j (mem_watched_of_neighbor c T k j hj)]
  have hloud : ((T.neighborsOf c k).any fun j => (look j).stories == 3 || (look j).isBar)
      = ((T.neighborsOf c k).any fun j => (look' j).stories == 3 || (look' j).isBar) :=
    hn (fun b => b.stories == 3 || b.isBar)
  have hkinds : (kindTests.filter fun test => (T.neighborsOf c k).any fun j => test (look j))
      = (kindTests.filter fun test => (T.neighborsOf c k).any fun j => test (look' j)) := by
    congr 1; funext test; exact hn test
  unfold factorsHad
  simp only [hn, hloud, hkinds]

theorem workersFor_congr (c : Context) (T : Transit) (look look' : Nat → Building) (k : Nat)
    (h : ∀ j ∈ T.watched c k, look j = look' j) :
    workersFor c T look k = workersFor c T look' k := by
  unfold workersFor
  rw [foldl_add_nat, foldl_add_nat]
  congr 2
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_filter, Transit.canReach, Bool.or_eq_true] at hj
  rcases hj.2 with hn | hl
  · rw [h j (mem_watched_of_neighbor c T k j (List.mem_filter.2 ⟨hj.1, hn⟩))]
  · rw [h j (mem_watched_of_bus c T k j hj.1 hl)]

/-- **A block's value depends only on the blocks it watches.** -/
theorem blockValue_congr (c : Context) (T : Transit) (look look' : Nat → Building) (k : Nat)
    (h : ∀ j ∈ T.watched c k, look j = look' j) :
    blockValue c T look k = blockValue c T look' k := by
  have hk : look k = look' k := h k (by simp [Transit.watched])
  have hf := factorsHad_congr c T look look' k h
  have hw := workersFor_congr c T look look' k h
  have hoff : officeBonus c T look k = officeBonus c T look' k := by
    unfold officeBonus
    have h1 : ((T.neighborsOf c k).filter fun j => (look j).isOffice)
        = ((T.neighborsOf c k).filter fun j => (look' j).isOffice) := by
      apply List.filter_congr
      intro j hj; rw [h j (mem_watched_of_neighbor c T k j hj)]
    rw [hk, h1]
  unfold blockValue blockHappiness blockProductivity blockSales blockCrime jobsFilled
  simp only [hk, hf, hw, hoff]

theorem seenFrom_agrees (c : Context) (T : Transit) (k : Nat) (look : Nat → Building) :
    ∀ j ∈ T.watched c k, seenFrom c T k look j = look j := by
  intro j hj
  simp [seenFrom, hj]

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
      (xs.map (·.2 / 10)).sum ≤ r →
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
    have ih := knapsack_ge units vals xs (r - x.2 / 10) hxs (by omega) (by omega)
    rw [List.foldr_cons]
    unfold knapsackRow
    rw [getD_ofFn _ _ _ (by omega)]
    refine Int.le_trans ?_ (mem_le_foldl_if_max
      (fun y => y.1 + (vals.foldr (knapsackRow units) (Array.replicate (units + 1) 0)).getD (r - y.2 / 10) impossible)
      (fun y => y.2 / 10 ≤ r) opts impossible x hx (by omega))
    omega

theorem sum_div_le {α : Type} (f : α → Nat) :
    ∀ l : List α, (l.map fun x => f x / 10).sum ≤ (l.map f).sum / 10
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

/-- Each block's cap and cost, for the building layout `t` puts on it. -/
def capsOf (P : Plan) (opts : List (List Building)) (t : Solution) : List (Int × Nat) :=
  P.c.blocks.map fun k =>
    (valueCap P.c (P.blockInfo (spotAt (spotTable P.c opts) opts) (optsAt opts) k) (t.look k),
     buildCostAt P.c.puzzle k (t.look k))

theorem score_le_caps (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hfit : FitsNode P opts t) :
    score p t ≤ ((capsOf P opts t).map (·.1)).sum := by
  obtain ⟨hT, hopts⟩ := hfit
  have hspot : ∀ j, (spotAt (spotTable P.c opts) opts j).Admits (t.look j) := fun j => by
    rw [spotAt_eq]; exact Spot.admits_of _ _ (hopts j)
  unfold score scoreWith
  rw [← hc, foldl_add_int]
  simp only [Int.zero_add, capsOf, List.map_map]
  have hle : ((P.c.blocks.map fun i => blockValue P.c t.transit (seenFrom P.c t.transit i t.look) i)).sum
      ≤ ((P.c.blocks.map ((·.1) ∘ fun k =>
          (valueCap P.c (P.blockInfo (spotAt (spotTable P.c opts) opts) (optsAt opts) k) (t.look k),
           buildCostAt P.c.puzzle k (t.look k))))).sum := by
    apply sum_le_sum_int
    intro k hk
    rw [blockValue_congr P.c t.transit _ t.look k (seenFrom_agrees P.c t.transit k t.look)]
    exact blockValue_le_valueCap P hP t.transit hT _ _ t.look hspot hopts k (List.mem_range.1 hk)
  omega

theorem picks_capsOf (P : Plan) (opts : List (List Building)) (t : Solution)
    (hopts : ∀ j, t.look j ∈ optsAt opts j) : Picks (capsOf P opts t) (P.optionValues opts) := by
  refine ⟨by simp [capsOf, Plan.optionValues], ?_⟩
  intro q hq
  simp only [capsOf, Plan.optionValues] at hq
  obtain ⟨k, _, rfl⟩ := mem_zip_map_same _ _ _ _ hq
  exact List.mem_map.2 ⟨t.look k, hopts k, rfl⟩

theorem cost_capsOf (p : Puzzle) (P : Plan) (hc : P.c = prepare p) (opts : List (List Building))
    (t : Solution) : ((capsOf P opts t).map (·.2)).sum = buildCost p t.build := by
  rw [buildCost_eq]
  simp only [capsOf, List.map_map, hc]
  rfl

theorem leastCost_le (c : Context) (P : Plan) (hP : P.Sound) (T : Transit) (hT : T ∈ P.group) :
    P.L.leastCost ≤ transitCost T := by
  rw [hP.1]; exact leastOf_le transitCost P.group T hT

/-- With the costs of a valid layout that fits the node, the caps fit the
budget left after the cheapest transit. -/
theorem caps_fit_budget (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) :
    ((capsOf P opts t).map (·.2)).sum ≤ p.budget - P.L.leastCost := by
  rw [cost_capsOf p P hc]
  have h1 := hv.2.1
  simp only [prepare_puzzle] at h1
  rw [costOf_eq] at h1
  have := leastCost_le P.c P hP _ hfit.1
  omega

/-- **The quick bound is safe**: no valid layout that fits the node scores more. -/
theorem score_le_bound (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) :
    score p t ≤ P.bound opts := by
  have h1 := score_le_caps p P hP hc opts t hfit
  have hpicks := picks_capsOf P opts t hfit.2
  have hcost := caps_fit_budget p P hP hc opts t hv hfit
  have hpz : P.c.puzzle = p := by rw [hc]; rfl
  unfold Plan.bound Plan.boundFrom
  simp only [hpz]
  apply le_foldl_min
  · exact Int.le_trans h1 (tradeBound_ge _ _ hpicks _ hcost 0)
  · intro r _; exact Int.le_trans h1 (tradeBound_ge _ _ hpicks _ hcost r)

/-- **The knapsack bound is safe**: no valid layout that fits the node scores
more. -/
theorem score_le_knapsackBound (p : Puzzle) (P : Plan) (hP : P.Sound) (hc : P.c = prepare p)
    (opts : List (List Building)) (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) :
    score p t ≤ P.knapsackBound opts := by
  have h1 := score_le_caps p P hP hc opts t hfit
  have hpicks := picks_capsOf P opts t hfit.2
  have hcost := caps_fit_budget p P hP hc opts t hv hfit
  have hdiv := sum_div_le (fun x : Int × Nat => x.2) (capsOf P opts t)
  have hpz : P.c.puzzle = p := by rw [hc]; rfl
  unfold Plan.knapsackBound Plan.knapsackFrom knapsack
  simp only [hpz]
  refine Int.le_trans h1 (knapsack_ge _ _ _ _ hpicks (Nat.le_refl _) ?_)
  exact Nat.le_trans hdiv (Nat.div_le_div_right hcost)

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

/-! ## The station cut -/

theorem foldl_if_add {α : Type} (r : α → Bool) (X : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun t j => if r j then t + X j else t) a = a + (l.map fun j => if r j then X j else 0).sum := by
  have : (fun t j => if r j = true then t + X j else t) = (fun t j => t + (if r j then X j else 0)) := by
    funext t j; split <;> simp
  rw [this, foldl_add_nat]

theorem foldl_if_add2 {α : Type} (r : α → Bool) (Y Z : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun t j => if r j then t + Y j + Z j else t) a
      = a + (l.map fun j => if r j then Y j + Z j else 0).sum := by
  have : (fun t j => if r j = true then t + Y j + Z j else t)
      = (fun t j => t + (if r j then Y j + Z j else 0)) := by
    funext t j; split <;> simp [Nat.add_assoc]
  rw [this, foldl_add_nat]

/-- The station's riders are at most `stationRidersCap`. -/
theorem stationRiders_le (c : Context) (T : Transit) (opts : List (List Building)) (look : Nat → Building)
    (hopts : ∀ j, look j ∈ optsAt opts j) :
    stationRiders c T look ≤ stationRidersCap c T opts := by
  unfold stationRiders stationRidersCap
  split
  · exact Nat.le_refl _
  · rw [foldl_if_add2, foldl_if_add]
    simp only [Nat.zero_add]
    apply sum_le_sum_nat
    intro j _
    split
    · rename_i hr
      have hW : (c.blocks.filter (T.canReach c j)).foldl
            (fun t h => t + leastOf Building.residents (opts.getD h [.empty])) 0
          ≤ workersFor c T look j := by
        unfold workersFor
        rw [foldl_add_nat, foldl_add_nat]
        simp only [Nat.zero_add]
        apply sum_filter_le _ _ _ _ _ (fun _ _ h => h)
        intro h _; exact leastOf_le _ _ _ (hopts h)
      have hsw : stationWorkersAt c T look j ≤ (look j).jobs -
          (c.blocks.filter (T.canReach c j)).foldl
            (fun t h => t + leastOf Building.residents (opts.getD h [.empty])) 0 := by
        unfold stationWorkersAt
        simp only [hr, ite_true]
        have := Nat.min_le_left (look j).jobs (workersFor c T look j)
        omega
      have hmem := hopts j
      generalize (c.blocks.filter (T.canReach c j)).foldl
            (fun t h => t + leastOf Building.residents (opts.getD h [.empty])) 0 = F at hsw ⊢
      generalize look j = b at hmem hsw ⊢
      refine Nat.le_trans ?_ (mem_le_foldl_max_nat (fun b => b.jobs - F + shoppersAt b) _ 0 b hmem)
      omega
    · exact Nat.le_refl _

/-- **The station cut is safe**: a valid layout that fits the node passes
`mayPass`. -/
theorem mayPass_of_valid (p : Puzzle) (P : Plan) (hc : P.c = prepare p) (opts : List (List Building))
    (t : Solution) (hv : Valid p t) (hfit : FitsNode P opts t) : P.mayPass opts = true := by
  unfold Plan.mayPass
  split
  · rename_i T hg
    have hT : t.transit = T := by have := hfit.1; rw [hg] at this; simpa using this
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hs : T.station.isNone = true
    · exact Or.inl hs
    · right
      have hsome : t.station.isSome = true := by
        have : t.station = T.station := by rw [← hT]; rfl
        rw [this]; cases h : T.station <;> simp_all
      have h1 := hv.2.2.2 hsome
      have h2 := stationRiders_le (prepare p) t.transit opts t.look hfit.2
      rw [hc, ← hT]
      exact Nat.le_trans h1 h2
  · rfl

end SevenBridges
