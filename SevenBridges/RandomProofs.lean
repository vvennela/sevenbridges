import SevenBridges.Generator
import SevenBridges.DayProofs

/-!
# Facts about the random numbers

The generator draws all its random numbers from `Rng.next`: a 64-bit linear
congruential generator. One step takes the state `s` to
`(s * 6364136223846793005 + 1442695040888963407) % 2^64`, and gives out the
top 31 bits of the new state.

What is proven here:

1. **No collisions** (`next_injective`, `prevState_next`, `streams_differ`):
   two different states always step to two different states. A step can be
   undone. So two different seeds give two different streams of states, and
   they differ at every step.
2. **Full period** (`lcg_full_period`, `rng_full_period`): for any modulus
   `2^k`, a step `x ↦ (x * a + c) % 2^k` with `c` odd and `a % 4 = 1` goes
   through every one of the `2^k` states before it repeats. Our constants meet
   both conditions, so from any start the generator visits all `2^64` states
   in its first `2^64` steps, with no repeats, and then comes back to the
   start. Every output `0 … 2^31 - 1` comes up (`every_output_reached`).
3. **Near-fair picks** (`below_fair`, `pick_mem`): `below n` takes an output
   `v < 2^31` and returns `v % n`. Every result `k < n` comes from either
   `2^31 / n` or `2^31 / n + 1` of the possible outputs. `pick` returns an
   item of the list.
4. **Choosing** (`choose_spec`, `choose_length`, `choose_mem`, `choose_nodup`):
   `choose l k` is the first `k` items of a reordering of `l`. So it has
   `min k l.length` items, all from `l`, each position of `l` used at most
   once (no repeats if `l` has none).
5. **Replay** (`catTraits_same`, `population_traits`): a cat's traits
   depend only on the puzzle's simulation seed, its groups, its home block
   and its number on that block. The simulation uses exactly those traits,
   drawn from the seed stored in the puzzle. (The generator itself is a plain
   Lean function of the map, routes, name and seed, so the same inputs give
   the same level by construction.)

What is **not** proven (the trust boundary):

- The starting seed comes from the browser's cryptographic random generator
  (`crypto.getRandomValues`). We trust it; nothing here is about it.
- The generator keeps the first random level that passes its quality checks
  (`Verdict.accepted`). So levels are random among the levels that pass, not
  uniform over all maps or layouts.
- A linear congruential generator is not a cryptographic generator. The
  facts above are about collisions, period and how evenly results are spread,
  not about how hard the numbers are to predict.
-/

namespace SevenBridges
namespace Generator

/-! ## The step, in general form -/

/-- One step of a linear congruential generator: `x ↦ (x * a + c) % m`. -/
def lcgStep (a c m x : Nat) : Nat := (x * a + c) % m

/-- The state after `n` steps from `x`. -/
def lcgIter (a c m : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => lcgStep a c m (lcgIter a c m n x)

example : lcgIter 5 3 8 3 1 = 2 := by decide

/-- The multiplier of `Rng.next`. -/
abbrev rngA : Nat := 6364136223846793005
/-- The increment of `Rng.next`. -/
abbrev rngC : Nat := 1442695040888963407

/-- `Rng.next` makes one step of the general form with our constants and
modulus `2^64`. -/
theorem next_state (r : Rng) : r.next.2.state = lcgStep rngA rngC (2 ^ 64) r.state := rfl

/-- The generator after `n` steps. -/
def Rng.after (r : Rng) : Nat → Rng
  | 0 => r
  | n + 1 => (r.after n).next.2

theorem after_state (r : Rng) : ∀ n, (r.after n).state = lcgIter rngA rngC (2 ^ 64) n r.state
  | 0 => rfl
  | n + 1 => by simp only [Rng.after, lcgIter, next_state, after_state r n]

theorem after_state_lt (r : Rng) (h : r.state < 2 ^ 64) : ∀ n, (r.after n).state < 2 ^ 64
  | 0 => h
  | n + 1 => by simp only [Rng.after, next_state, lcgStep]; exact Nat.mod_lt _ (by decide)

/-! ## 1. No collisions -/

/-- The inverse of `rngA` modulo `2^64`. -/
abbrev rngAInv : Nat := 13877824140714322085

/-- Undo one step: the state before `x`. -/
def prevState (x : Nat) : Nat := ((x + (2 ^ 64 - rngC)) * rngAInv) % 2 ^ 64

theorem mod_step (y a c m : Nat) : (y % m * a + c) % m = (y * a + c) % m := by
  rw [Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]

theorem mod_add_mul (y d e m : Nat) : ((y % m + d) * e) % m = ((y + d) * e) % m := by
  rw [Nat.mul_mod, Nat.mod_add_mod, ← Nat.mul_mod]

/-- **A step can be undone**: `prevState` gives back the state before any
step. -/
theorem prevState_next (r : Rng) (h : r.state < 2 ^ 64) : prevState r.next.2.state = r.state := by
  rw [next_state]
  unfold prevState lcgStep
  rw [mod_add_mul]
  have hc : rngC ≤ 2 ^ 64 := by decide
  have hinv : rngA * rngAInv = 1 + 4787856489426250814 * 2 ^ 64 := by decide
  have : (r.state * rngA + rngC + (2 ^ 64 - rngC)) * rngAInv
      = r.state + (r.state * 4787856489426250814 + rngAInv) * 2 ^ 64 := by
    have e : r.state * rngA + rngC + (2 ^ 64 - rngC) = r.state * rngA + 2 ^ 64 := by
      rw [Nat.add_assoc, Nat.add_sub_of_le hc]
    rw [e, Nat.add_mul, Nat.mul_assoc, hinv]
    grind
  rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

/-- **No collisions**: two different states (below `2^64`) step to two
different states. -/
theorem next_injective (r s : Rng) (hr : r.state < 2 ^ 64) (hs : s.state < 2 ^ 64)
    (h : r.next.2 = s.next.2) : r = s := by
  have := prevState_next r hr
  rw [h, prevState_next s hs] at this
  cases r; cases s; simp_all

/-- **Different seeds, different streams**: if two seeds (below `2^64`)
differ, their states differ after every number of steps. -/
theorem streams_differ (r s : Rng) (hr : r.state < 2 ^ 64) (hs : s.state < 2 ^ 64)
    (hne : r.state ≠ s.state) : ∀ n, (r.after n).state ≠ (s.after n).state
  | 0 => hne
  | n + 1 => by
    intro h
    have hrs := next_injective (r.after n) (s.after n) (after_state_lt r hr n)
      (after_state_lt s hs n) (by cases hx : (r.after n).next.2; cases hy : (s.after n).next.2
                                  simp only [Rng.after, hx, hy] at h; subst h; rfl)
    exact streams_differ r s hr hs hne n (by rw [hrs])

example : (Rng.after ⟨1⟩ 3).state ≠ (Rng.after ⟨2⟩ 3).state :=
  streams_differ ⟨1⟩ ⟨2⟩ (by decide) (by decide) (by decide) 3

/-! ## 2. Full period -/

/-- `1 + a + a^2 + … + a^(n-1)`. -/
def geomSum (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => geomSum a n + a ^ n

theorem geomSum_succ' (a : Nat) : ∀ n, geomSum a (n + 1) = 1 + a * geomSum a n
  | 0 => by simp [geomSum]
  | n + 1 => by
    have ih := geomSum_succ' a n
    simp only [geomSum] at ih ⊢
    rw [ih, Nat.pow_succ]; grind

theorem geomSum_add (a x : Nat) : ∀ y, geomSum a (x + y) = geomSum a x + a ^ x * geomSum a y
  | 0 => by simp [geomSum]
  | y + 1 => by
    rw [← Nat.add_assoc]; simp only [geomSum]; rw [geomSum_add a x y, Nat.pow_add]; grind

theorem geomSum_mul (a p : Nat) : ∀ m, geomSum a (p * m) = geomSum a p * geomSum (a ^ p) m
  | 0 => by simp [geomSum]
  | m + 1 => by
    rw [Nat.mul_succ, geomSum_add, geomSum_mul a p m]; simp only [geomSum]
    rw [← Nat.pow_mul]; grind

/-- `(b+1)^n = 1 + b * (1 + (b+1) + … + (b+1)^(n-1))`. -/
theorem pow_eq_geomSum (b : Nat) : ∀ n, (b + 1) ^ n = 1 + b * geomSum (b + 1) n
  | 0 => by simp [geomSum]
  | n + 1 => by rw [Nat.pow_succ, pow_eq_geomSum b n, geomSum_succ']; grind

theorem pow_mod_four (a : Nat) (ha : a % 4 = 1) : ∀ n, a ^ n % 4 = 1
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow_mod_four a ha n, ha]

theorem pow_mod_two (a : Nat) (ha : a % 2 = 1) : ∀ n, a ^ n % 2 = 1
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow_mod_two a ha n, ha]

theorem geomSum_mod_two (a : Nat) (ha : a % 2 = 1) : ∀ m, geomSum a m % 2 = m % 2
  | 0 => rfl
  | m + 1 => by
    simp only [geomSum]
    have := geomSum_mod_two a ha m
    have := pow_mod_two a ha m
    omega

/-- `1 + a + … + a^(2^k - 1)` is `2^k` times an odd number when `a % 4 = 1`. -/
theorem geomSum_two_pow (a : Nat) (ha : a % 4 = 1) :
    ∀ k, ∃ o, o % 2 = 1 ∧ geomSum a (2 ^ k) = 2 ^ k * o
  | 0 => ⟨1, rfl, by simp [geomSum]⟩
  | k + 1 => by
    obtain ⟨o, ho, h⟩ := geomSum_two_pow a ha k
    have e : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have h4 := pow_mod_four a ha (2 ^ k)
    obtain ⟨q, hq⟩ : ∃ q, 1 + a ^ 2 ^ k = 2 * q := ⟨(1 + a ^ 2 ^ k) / 2, by omega⟩
    have hq2 : q % 2 = 1 := by omega
    refine ⟨o * q, ?_, ?_⟩
    · rw [Nat.mul_mod, ho, hq2]
    · rw [e, geomSum_add, h]
      calc 2 ^ k * o + a ^ 2 ^ k * (2 ^ k * o) = 2 ^ k * o * (1 + a ^ 2 ^ k) := by grind
        _ = (2 ^ k + 2 ^ k) * (o * q) := by rw [hq]; grind

/-- If `2^k` divides `y` times an odd number, it divides `y`. -/
theorem two_pow_dvd_of_mul_odd (o : Nat) (ho : o % 2 = 1) :
    ∀ k y, 2 ^ k ∣ y * o → 2 ^ k ∣ y
  | 0, _, _ => by simp
  | k + 1, y, h => by
    have h2 : 2 ∣ y * o := Nat.dvd_trans (Nat.dvd_of_pow_dvd (by omega) (Nat.dvd_refl _)) h
    have hy : y % 2 = 0 := by
      have := Nat.mod_eq_zero_of_dvd h2
      rw [Nat.mul_mod, ho] at this; omega
    obtain ⟨z, rfl⟩ : 2 ∣ y := Nat.dvd_of_mod_eq_zero hy
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc] at h
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact Nat.mul_dvd_mul_left 2
      (two_pow_dvd_of_mul_odd o ho k z (Nat.dvd_of_mul_dvd_mul_left (by omega) h))

/-- When `a % 4 = 1`, `2^k` divides `1 + a + … + a^(n-1)` only if it divides
`n`. -/
theorem dvd_of_dvd_geomSum (a : Nat) (ha : a % 4 = 1) :
    ∀ k n, 2 ^ k ∣ geomSum a n → 2 ^ k ∣ n
  | 0, _, _ => by simp
  | k + 1, n, h => by
    have hk : 2 ^ k ∣ geomSum a n :=
      Nat.dvd_trans (Nat.pow_dvd_pow 2 (Nat.le_succ k)) h
    obtain ⟨m, rfl⟩ := dvd_of_dvd_geomSum a ha k n hk
    obtain ⟨o, ho, hs⟩ := geomSum_two_pow a ha k
    rw [geomSum_mul, hs, Nat.mul_assoc, Nat.pow_succ] at h
    have h2 : 2 ∣ o * geomSum (a ^ 2 ^ k) m :=
      Nat.dvd_of_mul_dvd_mul_left (Nat.two_pow_pos k) h
    have hodd : a ^ 2 ^ k % 2 = 1 := by have := pow_mod_four a ha (2 ^ k); omega
    have hm := geomSum_mod_two _ hodd m
    have := Nat.mod_eq_zero_of_dvd h2
    rw [Nat.mul_mod, ho, hm] at this
    obtain ⟨j, rfl⟩ : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    rw [Nat.pow_succ]
    exact Nat.mul_dvd_mul_left _ (Nat.dvd_mul_right 2 j)

/-- The state after `n` steps, in closed form. -/
theorem lcgIter_eq (a c m x : Nat) (hx : x < m) :
    ∀ n, lcgIter a c m n x = (x * a ^ n + c * geomSum a n) % m
  | 0 => by simp [lcgIter, geomSum, Nat.mod_eq_of_lt hx]
  | n + 1 => by
    rw [lcgIter, lcgIter_eq a c m x hx n, lcgStep, mod_step, geomSum_succ', Nat.pow_succ]
    congr 1; grind

theorem lcgIter_add (a c m x : Nat) : ∀ i j, lcgIter a c m (i + j) x = lcgIter a c m i (lcgIter a c m j x)
  | 0, j => by simp [lcgIter]
  | i + 1, j => by rw [Nat.add_right_comm, lcgIter, lcgIter_add a c m x i j, lcgIter]

theorem lcgIter_lt (a c m x : Nat) (hm : 0 < m) (hx : x < m) : ∀ n, lcgIter a c m n x < m
  | 0 => hx
  | _ + 1 => Nat.mod_lt _ hm

/-- **When the state comes back** (modulus `2^k`, `c` odd, `a % 4 = 1`):
from any state `x`, the state after `n` steps is `x` again exactly when `n`
is a multiple of `2^k`. -/
theorem lcg_returns_iff (a c k x n : Nat) (ha : a % 4 = 1) (hc : c % 2 = 1) (hx : x < 2 ^ k) :
    lcgIter a c (2 ^ k) n x = x ↔ 2 ^ k ∣ n := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  rw [lcgIter_eq _ _ _ _ hx, pow_eq_geomSum]
  have e : x * (1 + b * geomSum (b + 1) n) + c * geomSum (b + 1) n
      = x + geomSum (b + 1) n * (x * b + c) := by grind
  have hodd : (x * b + c) % 2 = 1 := by
    have : b % 2 = 0 := by omega
    rw [Nat.add_mod, Nat.mul_mod, this]; omega
  rw [e]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  constructor
  · intro h
    have h1 : (x + geomSum (b + 1) n * (x * b + c)) % 2 ^ k = x % 2 ^ k := by
      rw [h, Nat.mod_eq_of_lt hx]
    have h2 := Nat.sub_mod_eq_zero_of_mod_eq h1
    rw [Nat.add_sub_cancel_left] at h2
    exact dvd_of_dvd_geomSum _ ha k n
      (two_pow_dvd_of_mul_odd _ hodd k _ (Nat.dvd_of_mod_eq_zero h2))
  · rintro ⟨j, rfl⟩
    obtain ⟨o, _, hs⟩ := geomSum_two_pow _ ha k
    rw [geomSum_mul, hs, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hx]

theorem nodup_length_le : ∀ (N : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < N) → l.length ≤ N
  | 0, [], _, _ => Nat.le_refl 0
  | 0, x :: _, _, h => absurd (h x (by simp)) (by omega)
  | N + 1, l, hl, h => by
    by_cases hN : N ∈ l
    · have := nodup_length_le N (l.erase N) (hl.erase N) (fun x hx => by
        rw [hl.mem_erase_iff] at hx
        have := h x hx.2; omega)
      rw [List.length_erase_of_mem hN] at this; omega
    · have := nodup_length_le N l hl (fun x hx => by
        have := h x hx
        have : x ≠ N := fun e => hN (e ▸ hx)
        omega)
      omega

/-- Pigeonhole: a list of `N` different numbers, all below `N`, holds every
number below `N`. -/
theorem mem_of_nodup_length (N : Nat) (l : List Nat) (hl : l.Nodup) (h : ∀ x ∈ l, x < N)
    (hlen : l.length = N) (y : Nat) (hy : y < N) : y ∈ l := by
  apply Classical.byContradiction
  intro hny
  have := nodup_length_le N (y :: l) (List.nodup_cons.mpr ⟨hny, hl⟩)
    (fun x hx => by simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact hy; exact h x hx)
  simp at this; omega

/-- **Full period** (Hull–Dobell, for modulus `2^k`): with `c` odd and
`a % 4 = 1`, from any start `x < 2^k`,
- the first `2^k` states are all different,
- they include every state below `2^k`,
- and after `2^k` steps the state is `x` again. -/
theorem lcg_full_period (a c k x : Nat) (ha : a % 4 = 1) (hc : c % 2 = 1) (hx : x < 2 ^ k) :
    (∀ i j, i < j → j < 2 ^ k → lcgIter a c (2 ^ k) i x ≠ lcgIter a c (2 ^ k) j x) ∧
    (∀ y, y < 2 ^ k → ∃ n, n < 2 ^ k ∧ lcgIter a c (2 ^ k) n x = y) ∧
    lcgIter a c (2 ^ k) (2 ^ k) x = x := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have distinct : ∀ i j, i < j → j < 2 ^ k → lcgIter a c (2 ^ k) i x ≠ lcgIter a c (2 ^ k) j x := by
    intro i j hij hj heq
    have e : j = (j - i) + i := by omega
    rw [e, lcgIter_add] at heq
    have := (lcg_returns_iff a c k _ (j - i) ha hc (lcgIter_lt a c _ x hpos hx i)).mp heq.symm
    have := Nat.le_of_dvd (by omega) this
    omega
  refine ⟨distinct, ?_, (lcg_returns_iff a c k x _ ha hc hx).mpr (Nat.dvd_refl _)⟩
  intro y hy
  have hmem := mem_of_nodup_length (2 ^ k) ((List.range (2 ^ k)).map (lcgIter a c (2 ^ k) · x))
    (nodup_map_range' _ distinct) (by
      intro z hz
      simp only [List.mem_map] at hz
      obtain ⟨n, _, rfl⟩ := hz
      exact lcgIter_lt a c _ x hpos hx n) (by simp) y hy
  simp only [List.mem_map, List.mem_range] at hmem
  exact hmem
where
  nodup_map_range' (f : Nat → Nat) (hf : ∀ i j, i < j → j < 2 ^ k → f i ≠ f j) :
      ((List.range (2 ^ k)).map f).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map, List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.length_range] at hi hj
    simp only [List.getElem_range]
    exact hf i j hij hj

/-- The hypotheses can be met: a small generator modulo `2^3 = 8`. -/
example : (∀ y, y < 2 ^ 3 → ∃ n, n < 2 ^ 3 ∧ lcgIter 5 3 (2 ^ 3) n 0 = y) :=
  (lcg_full_period 5 3 3 0 (by decide) (by decide) (by decide)).2.1

/-- The condition `a % 4 = 1` matters: with `a = 3`, the state comes back to
`0` after only 4 of the 8 states. -/
example : lcgIter 3 1 8 4 0 = 0 := by decide

/-- Our constants meet the full-period conditions. -/
theorem rng_constants : rngA % 4 = 1 ∧ rngC % 2 = 1 := by decide

/-- **The generator has full period**: from any seed below `2^64`, the
first `2^64` states are all different, they include every state below
`2^64`, and after `2^64` steps the generator is back at the seed. -/
theorem rng_full_period (r : Rng) (hr : r.state < 2 ^ 64) :
    (∀ i j, i < j → j < 2 ^ 64 → (r.after i).state ≠ (r.after j).state) ∧
    (∀ t, t < 2 ^ 64 → ∃ n, n < 2 ^ 64 ∧ (r.after n).state = t) ∧
    (r.after (2 ^ 64)).state = r.state := by
  simp only [after_state]
  exact lcg_full_period rngA rngC 64 r.state rng_constants.1 rng_constants.2 hr

/-- Every output of `next` is below `2^31`. -/
theorem next_output_lt (r : Rng) : r.next.1 < 2 ^ 31 := by
  have : (r.state * rngA + rngC) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  show (r.state * rngA + rngC) % 2 ^ 64 / 2 ^ 33 < 2 ^ 31
  omega

/-- **Every output comes up**: from any seed below `2^64`, every number
below `2^31` is given out within the first `2^64` steps. -/
theorem every_output_reached (r : Rng) (hr : r.state < 2 ^ 64) (v : Nat) (hv : v < 2 ^ 31) :
    ∃ n, n < 2 ^ 64 ∧ (r.after n).next.1 = v := by
  obtain ⟨n, hn, hs⟩ := (rng_full_period r hr).2.1 (prevState (v * 2 ^ 33)) (Nat.mod_lt _ (by decide))
  refine ⟨n, hn, ?_⟩
  have hlt : v * 2 ^ 33 < 2 ^ 64 := by omega
  -- The step after `prevState t` lands on `t`.
  have key : ∀ t, t < 2 ^ 64 → lcgStep rngA rngC (2 ^ 64) (prevState t) = t := by
    intro t ht
    unfold prevState lcgStep
    rw [mod_step]
    have hinv : rngAInv * rngA = 1 + 4787856489426250814 * 2 ^ 64 := by decide
    have hc : rngC ≤ 2 ^ 64 := by decide
    rw [Nat.mul_assoc, hinv, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
      Nat.add_right_comm, Nat.add_assoc t, Nat.sub_add_cancel hc]
    rw [show t + 2 ^ 64 + (t + (2 ^ 64 - rngC)) * 4787856489426250814 * 2 ^ 64
        = t + (1 + (t + (2 ^ 64 - rngC)) * 4787856489426250814) * 2 ^ 64 by grind,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  show (lcgStep rngA rngC (2 ^ 64) (r.after n).state) / 2 ^ 33 = v
  rw [hs, key _ hlt]; omega

/-! ## 3. Near-fair picks -/

/-- `below n` is the next output modulo `n` (for `n > 0`). -/
theorem below_eq (r : Rng) (n : Nat) (hn : 0 < n) : (r.below n).1 = r.next.1 % n := by
  simp [Rng.below, Nat.pos_iff_ne_zero.mp hn]

theorem below_lt (r : Rng) (n : Nat) (hn : 0 < n) : (r.below n).1 < n := by
  rw [below_eq r n hn]; exact Nat.mod_lt _ hn

/-- How many numbers `v < N` have `v % n = k`. -/
theorem count_mod (n k : Nat) (hn : 0 < n) (hk : k < n) : ∀ N,
    ((List.range N).filter (fun v => v % n == k)).length = N / n + if k < N % n then 1 else 0
  | 0 => by simp
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, count_mod n k hn hk N]
    have hq := Nat.div_add_mod N n
    have hr := Nat.mod_lt N hn
    by_cases hlast : N % n + 1 < n
    · have : (N + 1) / n = N / n ∧ (N + 1) % n = N % n + 1 :=
        (Nat.div_mod_unique hn).mpr ⟨by omega, hlast⟩
      rw [this.1, this.2]
      by_cases e : N % n = k <;> by_cases e2 : k < N % n <;> by_cases e3 : k < N % n + 1 <;>
        simp [e, e2, e3] <;> omega
    · have : (N + 1) / n = N / n + 1 ∧ (N + 1) % n = 0 :=
        (Nat.div_mod_unique hn).mpr ⟨by rw [Nat.mul_succ]; omega, hn⟩
      rw [this.1, this.2]
      by_cases e : N % n = k <;> by_cases e2 : k < N % n <;> simp [e, e2] <;> omega

/-- **Near-fair picks**: of the `2^31` possible outputs `v` of `next`, the
number with `v % n = k` is `2^31 / n` or `2^31 / n + 1`, for every result
`k < n`. So no result of `below n` is more than one output more likely than
another. -/
theorem below_fair (n k : Nat) (hn : 0 < n) (hk : k < n) :
    ((List.range (2 ^ 31)).filter (fun v => v % n == k)).length = 2 ^ 31 / n ∨
    ((List.range (2 ^ 31)).filter (fun v => v % n == k)).length = 2 ^ 31 / n + 1 := by
  rw [count_mod n k hn hk]; split <;> simp

example : ((List.range 10).filter (fun v => v % 3 == 0)).length = 10 / 3 + 1 := by decide
example : ((List.range 10).filter (fun v => v % 3 == 2)).length = 10 / 3 := by decide

/-- **`pick` returns an item of the list** (when the list is not empty). -/
theorem pick_mem {α : Type} [Inhabited α] (r : Rng) (l : List α) (hl : l ≠ []) :
    (r.pick l).1 ∈ l := by
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl
  have hi := below_lt r l.length hlen
  show l.getD (r.below l.length).1 default ∈ l
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

/-! ## 4. Choosing -/

theorem choose_fold {α : Type} (l : List α) :
    ∀ (acc : List (Nat × α)) (r : Rng),
      ((l.foldl (fun (acc, r) x => let (v, r) := r.next; (acc ++ [(v, x)], r)) (acc, r)).1.map (·.2))
        = acc.map (·.2) ++ l := by
  induction l with
  | nil => intro acc r; simp
  | cons x xs ih => intro acc r; simp only [List.foldl_cons]; rw [ih]; simp

/-- **`choose l k` is the first `k` items of a reordering of `l`.** -/
theorem choose_spec {α : Type} (r : Rng) (l : List α) (k : Nat) :
    ∃ shuffled : List α, shuffled.Perm l ∧ (r.choose l k).1 = shuffled.take k := by
  refine ⟨((l.foldl (fun (acc, r) x => let (v, r) := r.next; (acc ++ [(v, x)], r)) ([], r)).1.mergeSort
      (fun a b => a.1 ≤ b.1)).map (·.2), ?_, ?_⟩
  · have := (List.mergeSort_perm ((l.foldl (fun (acc, r) x => let (v, r) := r.next;
      (acc ++ [(v, x)], r)) ([], r)).1) (fun a b => decide (a.1 ≤ b.1))).map (·.2)
    rw [choose_fold] at this; simpa using this
  · simp only [Rng.choose, List.map_take]

/-- `choose l k` has `min k l.length` items. -/
theorem choose_length {α : Type} (r : Rng) (l : List α) (k : Nat) :
    (r.choose l k).1.length = min k l.length := by
  obtain ⟨s, hp, h⟩ := choose_spec r l k
  rw [h, List.length_take, hp.length_eq]

/-- Every item `choose` returns is in the list. -/
theorem choose_mem {α : Type} (r : Rng) (l : List α) (k : Nat) (x : α)
    (hx : x ∈ (r.choose l k).1) : x ∈ l := by
  obtain ⟨s, hp, h⟩ := choose_spec r l k
  rw [h] at hx
  exact hp.mem_iff.mp ((List.take_sublist k s).subset hx)

/-- If the list has no repeats, neither does what `choose` returns. -/
theorem choose_nodup {α : Type} (r : Rng) (l : List α) (k : Nat) (hl : l.Nodup) :
    (r.choose l k).1.Nodup := by
  obtain ⟨s, hp, h⟩ := choose_spec r l k
  rw [h]
  exact (List.take_sublist k s).nodup (hp.nodup_iff.mpr hl)

example : (Rng.choose ⟨7⟩ [1, 2, 3, 4, 5] 3).1.length = 3 := by
  rw [choose_length]; rfl

-- `choose` keeps the items of the list, and never repeats one.
#guard (Rng.choose ⟨7⟩ [1, 2, 3, 4, 5] 3).1.all ([1, 2, 3, 4, 5].contains ·)
#guard ((Rng.choose ⟨7⟩ [1, 2, 3, 4, 5] 5).1.mergeSort (· ≤ ·)) == [1, 2, 3, 4, 5]
#guard (Rng.pick ⟨42⟩ ["a", "b", "c"]).1 ∈ ["a", "b", "c"]

/-! ## 5. Replay -/

/-- **A cat's traits depend only on the seed and the groups**: two puzzles
with the same simulation seed and the same resident groups give every cat
(block `h`, number `i`) the same traits, whatever their maps, routes,
buildings or budgets. -/
theorem catTraits_same (p q : Puzzle) (hs : p.simSeed = q.simSeed) (hg : p.groups = q.groups)
    (h i : Nat) : catTraits p h i = catTraits q h i := by
  unfold catTraits residentTypesOf
  rw [hs, hg]

/-- Every building has at most `maxCatsPerBlock` cats. -/
theorem cats_le_max (b : Building) : b.cats ≤ maxCatsPerBlock := by
  cases b <;> (try rename_i h; cases h) <;> decide

/-- **The simulation uses the seed's traits**: every cat in the simulated
town (any layout) has exactly the traits `catTraits` draws from the
puzzle's own `simSeed` for its home block and number. -/
theorem population_traits (p : Puzzle) (look : Nat → Building) (r : Resident)
    (hr : r ∈ population (prepare p) look) : r.traits = catTraits p r.home r.index := by
  rw [mem_population] at hr
  obtain ⟨hh, hr⟩ := hr
  simp only [residentsOn, List.mem_map, List.mem_range] at hr
  obtain ⟨i, hi, e⟩ := hr
  have hi' : i < maxCatsPerBlock := Nat.lt_of_lt_of_le hi (cats_le_max _)
  have hh' : r.home < p.blockCount := by simpa [Context.blocks, prepare] using hh
  rw [← e]
  simp [Context.traitsAt, prepare, Array.getD, hh', hi']

end Generator
end SevenBridges
