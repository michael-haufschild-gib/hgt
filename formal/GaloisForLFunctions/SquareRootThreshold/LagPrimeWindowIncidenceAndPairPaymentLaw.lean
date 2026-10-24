import GaloisForLFunctions.ArithmeticIncidencePositivity.DyadicWindowIncidence
import GaloisForLFunctions.SquareRootThreshold.DyadicWindowMultiplicativeIndependence

/-!
# Window Incidence on `lagPrimeWindow` and the Lag-Side Prime-Pair Payment Law

The single-window criteria of the Square-Root Threshold programme evaluate the explicit-formula
functional `lagPrimeWindowRHS v w k` on the window `lagPrimeWindow v w` of integers `n` with
`|log n − v| ≤ 2w`. When `2w < log 2`, this window has multiplicative ratio `e^{4w} < 4` and lies
inside both the centered dyadic window `(e^v/2, 2e^v)` (`ArithmeticIncidencePositivity.InDyadicWindow`)
and the left-anchored ratio-`4` window `[e^{v−2w}, 4e^{v−2w})`
(`SquareRootThreshold.InDyadicWindow`).

This module turns the dyadic window incidence structure of `ArithmeticIncidencePositivity` into
explicit lag-side laws on `lagPrimeWindow v w`:

1. **Prime-Power Support, Tower Occupancy, and Divisor-Poset Height `1` on `lagPrimeWindow`
   (`lagPrimePowWindow`, `lagPrimeWindowRHS_eq_sum_lagPrimePowWindow`,
   `lagPrimeWindow_exponent_sub_le_one`, `not_three_powers_in_lagPrimeWindow`,
   `lagPrimeWindow_exponent_eq_of_five_le`, `not_dvd_chain_in_lagPrimeWindow`):**
   - Only prime powers `n ∈ lagPrimePowWindow v w := (lagPrimeWindow v w).filter IsPrimePow`
     contribute to `lagPrimeWindowRHS v w k` (`lagPrimeWindowRHS_eq_sum_lagPrimePowWindow`), and
     every such `n` satisfies `2 ≤ n` and `e^{v−2w} ≤ n ≤ e^{v+2w}`.
   - For `2w < log 2`, any prime `p` has at most two consecutive powers `p^i, p^{i+1}` in
     `lagPrimeWindow v w` (`lagPrimeWindow_exponent_sub_le_one`, `not_three_powers_in_lagPrimeWindow`),
     any prime `p ≥ 5` has at most **one** power in `lagPrimeWindow v w`
     (`lagPrimeWindow_exponent_eq_of_five_le`), and the divisor relation on `lagPrimeWindow v w`
     has height at most `1` (`not_dvd_chain_in_lagPrimeWindow`: no `1 ≤ a < b < c` in
     `lagPrimeWindow v w` can satisfy `a ∣ b` and `b ∣ c`).

2. **Exact Classification and Uniqueness of Same-Side and Crossing Pairs in `lagPrimeWindow`
   (`ratioAtom_of_mem_lagPrimeWindow`, `consecutive_powers_of_mem_lagPrimeWindow_isPrimePow_mul`,
   `unique_crossing_pair_in_lagPrimeWindow`, `productAtom_le_exp_neg_mul_ratioAtom_of_mem_lagPrimeWindow`):**
   - Every same-side atom `ratioAtom a b` on `lagPrimeWindow v w` (`1 ≤ a < b`, `2w < log 2`) is
     `0`, `vonMangoldtAtom 2 = log 2 / √2` (a doubling `b = 2a`), or
     `vonMangoldtAtom 3 = log 3 / √3` (a tripling `b = 3a`).
   - Every crossing prime-power pair `IsPrimePow (a * b)` in `lagPrimeWindow v w` (`1 ≤ a < b`) is
     a consecutive power pair `(p^i, p^{i+1})` with `p ∈ {2, 3}`, and for each `p ∈ {2, 3}` **at
     most one such pair exists in `lagPrimeWindow v w`** (`unique_crossing_pair_in_lagPrimeWindow`).
   - Every crossing atom in `lagPrimeWindow v w` equals `ratioAtom a b / a` and is therefore
     exponentially suppressed in the lag relative to its own same-side atom:
     `productAtom a b ≤ e^{−(v − 2w)} ratioAtom a b` and
     `(1 − e^{−(v − 2w)}) ratioAtom a b ≤ netAtom a b`.

3. **Lag-Side Pair-Payment Ledger (`lagDoublingEnergy`, `lagTriplingEnergy`,
   `ratioEnergy_eq_lagDoublingEnergy_add_lagTriplingEnergy`,
   `productEnergy_le_exp_neg_mul_of_subset_lagPrimeWindow`,
   `skeletonEnergy_ge_one_sub_exp_neg_mul_of_subset_lagPrimeWindow`,
   `ratioEnergy_le_four_mul_atom_two_add_three_mul_sum_sq`):**
   - On any `S ⊆ lagPrimeWindow v w` (`∀ a ∈ S, 1 ≤ a`, `2w < log 2`), the same-side ratio energy
     is exhausted by the doubling and tripling energies alone:
     `ratioEnergy S c = lagDoublingEnergy S c + lagTriplingEnergy S c`.
   - The crossing prime-pair energy on `S` is paid by the doubling and tripling energies with an
     exponential lag discount `e^{−(v − 2w)}`:
     `productEnergy S c ≤ e^{−(v − 2w)} (lagDoublingEnergy S c + lagTriplingEnergy S c)` and
     `(1 − e^{−(v − 2w)}) (lagDoublingEnergy S c + lagTriplingEnergy S c) ≤ skeletonEnergy S c`.
   - Because `b = 2a` and `b = 3a` are degree-`1` partial matchings, the doubling and tripling
     energies are bounded by `4 (vonMangoldtAtom 2 + vonMangoldtAtom 3) ∑_{a ∈ S} c(a)²`.

4. **Inter-Lag Window Decoupling Across Two Lags `v₁ ≤ v₂`
   (`div_bounds_of_mem_lagPrimeWindows_dvd`,
   `four_le_div_of_mem_lagPrimeWindows_of_log_twelve_le`):**
   - For `1 ≤ a ∈ lagPrimeWindow v₁ w` and `1 ≤ b ∈ lagPrimeWindow v₂ w` (`2w < log 2`) with `a ∣ b`,
     the multiplier `m = b / a` satisfies `e^{v₂ − v₁} / 4 < m < 4 e^{v₂ − v₁}`, so when
     `12 e^{v₁} ≤ e^{v₂}`, the intra-window multipliers `2` and `3` completely decouple between
     `lagPrimeWindow v₁ w` and `lagPrimeWindow v₂ w` (`4 ≤ b / a`).
-/

open Finset ArithmeticFunction MeasureTheory Complex
open scoped Real ComplexConjugate BigOperators

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### 1. Prime-power support, prime-tower occupancy, and divisor-poset height `1` -/

/-- The prime-power subset of `lagPrimeWindow v w`: the exact arithmetic support of
`lagPrimeWindowRHS v w k`. -/
def lagPrimePowWindow (v w : ℝ) : Finset ℕ :=
  (lagPrimeWindow v w).filter IsPrimePow

theorem mem_lagPrimePowWindow_iff {v w : ℝ} {n : ℕ} :
    n ∈ lagPrimePowWindow v w ↔ n ∈ lagPrimeWindow v w ∧ IsPrimePow n :=
  Finset.mem_filter

/-- Every member of `lagPrimePowWindow v w` is at least `2`. -/
theorem two_le_of_mem_lagPrimePowWindow {v w : ℝ} {n : ℕ} (hn : n ∈ lagPrimePowWindow v w) :
    2 ≤ n := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp (mem_lagPrimePowWindow_iff.mp hn).2
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    _ = n := hpk

theorem one_le_of_mem_lagPrimePowWindow {v w : ℝ} {n : ℕ} (hn : n ∈ lagPrimePowWindow v w) :
    1 ≤ n := by
  have := two_le_of_mem_lagPrimePowWindow hn
  omega

/-- Every positive integer `n ∈ lagPrimeWindow v w` satisfies `e^{v − 2w} ≤ n ≤ e^{v + 2w}`. -/
theorem exp_sub_le_and_le_exp_add_of_mem_lagPrimeWindow {v w : ℝ} {n : ℕ} (hn1 : 1 ≤ n)
    (hn : n ∈ lagPrimeWindow v w) :
    Real.exp (v - 2 * w) ≤ n ∧ (n : ℝ) ≤ Real.exp (v + 2 * w) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hlo, hhi⟩ := abs_le.mp (Finset.mem_filter.mp hn).2
  constructor
  · calc Real.exp (v - 2 * w) ≤ Real.exp (Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = n := Real.exp_log hn0
  · calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (v + 2 * w) := Real.exp_le_exp.mpr (by linarith)

/-- Every `n ∈ lagPrimePowWindow v w` (`2w < log 2`) lies in the centered dyadic window
`(e^v/2, 2e^v)`. -/
theorem inDyadicWindow_of_mem_lagPrimePowWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {n : ℕ}
    (hn : n ∈ lagPrimePowWindow v w) :
    ArithmeticIncidencePositivity.InDyadicWindow (Real.exp v) n :=
  inDyadicWindow_of_mem_lagPrimeWindow hw (one_le_of_mem_lagPrimePowWindow hn)
    (mem_lagPrimePowWindow_iff.mp hn).1

/-- **Exact prime-power reduction of `lagPrimeWindowRHS`.** Restricting the window sum from
`lagPrimeWindow v w` to `lagPrimePowWindow v w` leaves `lagPrimeWindowRHS v w k` unchanged. -/
theorem lagPrimeWindowRHS_eq_sum_lagPrimePowWindow (v w : ℝ) (k : ℝ → ℂ) :
    lagPrimeWindowRHS v w k =
      paperFT k (I / 2) + paperFT k (-I / 2)
      - ∑ n ∈ lagPrimePowWindow v w, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
          * (k (Real.log n) + k (-Real.log n))
      + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
  unfold lagPrimeWindowRHS lagPrimePowWindow
  congr 2
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun n hn hnot => ?_).symm
  have hnp : ¬ IsPrimePow n := fun hp => hnot (Finset.mem_filter.mpr ⟨hn, hp⟩)
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp]
  simp

/-- **At most two consecutive powers of any prime in `lagPrimeWindow`.** For `2w < log 2` and any
prime `p`, if `p^i ∈ lagPrimeWindow v w` and `p^j ∈ lagPrimeWindow v w`, then `j ≤ i + 1`. -/
theorem lagPrimeWindow_exponent_sub_le_one {v w : ℝ} (hw : 2 * w < Real.log 2) {p i j : ℕ}
    (hp : p.Prime) (hi : p ^ i ∈ lagPrimeWindow v w) (hj : p ^ j ∈ lagPrimeWindow v w) :
    j ≤ i + 1 :=
  exponent_sub_le_one_of_inDyadicWindow hp
    (inDyadicWindow_of_mem_lagPrimeWindow hw (Nat.one_le_pow i p hp.pos) hi)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (Nat.one_le_pow j p hp.pos) hj)

/-- **No three powers of one prime fit in `lagPrimeWindow`.** For `2w < log 2` and any prime `p`,
no three exponents `i < j < k` can all have `p^i, p^j, p^k ∈ lagPrimeWindow v w`. -/
theorem not_three_powers_in_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {p i j k : ℕ}
    (hp : p.Prime) (hij : i < j) (hjk : j < k)
    (hi : p ^ i ∈ lagPrimeWindow v w) (_hj : p ^ j ∈ lagPrimeWindow v w)
    (hk : p ^ k ∈ lagPrimeWindow v w) : False := by
  have hle := lagPrimeWindow_exponent_sub_le_one hw hp hi hk
  omega

/-- **Primes `p ≥ 5` have at most one power in `lagPrimeWindow`.** For `2w < log 2` and any prime
`p ≥ 5`, if `p^i ∈ lagPrimeWindow v w` and `p^j ∈ lagPrimeWindow v w`, then `i = j`. -/
theorem lagPrimeWindow_exponent_eq_of_five_le {v w : ℝ} (hw : 2 * w < Real.log 2) {p i j : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hi : p ^ i ∈ lagPrimeWindow v w)
    (hj : p ^ j ∈ lagPrimeWindow v w) :
    i = j :=
  exponent_eq_of_inDyadicWindow_of_five_le hp hp5
    (inDyadicWindow_of_mem_lagPrimeWindow hw (Nat.one_le_pow i p hp.pos) hi)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (Nat.one_le_pow j p hp.pos) hj)

/-- **The divisor poset on `lagPrimeWindow` has height at most `1`.** For `2w < log 2`, no three
positive integers `a < b < c` in `lagPrimeWindow v w` can form a divisor chain `a ∣ b` and `b ∣ c`. -/
theorem not_dvd_chain_in_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {a b c : ℕ}
    (ha1 : 1 ≤ a) (ha : a ∈ lagPrimeWindow v w) (hb : b ∈ lagPrimeWindow v w)
    (hc : c ∈ lagPrimeWindow v w) (hab : a < b) (hbc : b < c) (hd1 : a ∣ b) (hd2 : b ∣ c) :
    False := by
  have hlt := lt_four_mul_of_inDyadicWindow
    (inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (by omega) hc)
  have hlt_nat : c < 4 * a := by exact_mod_cast hlt
  rcases eq_two_mul_or_three_mul_of_mem_lagPrimeWindow hw ha1 ha hb hab hd1 with rfl | rfl <;>
    rcases eq_two_mul_or_three_mul_of_mem_lagPrimeWindow hw (by omega) hb hc hbc hd2 with rfl | rfl <;>
    omega

/-! ### 2. Exact classification and uniqueness of same-side and crossing pairs in `lagPrimeWindow` -/

/-- **Same-side atoms in `lagPrimeWindow` are only doublings and triplings.** For `2w < log 2` and
`a, b ∈ lagPrimeWindow v w` with `1 ≤ a < b`, `ratioAtom a b` is `0`, `vonMangoldtAtom 2`, or
`vonMangoldtAtom 3`. -/
theorem ratioAtom_of_mem_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {a b : ℕ}
    (ha1 : 1 ≤ a) (ha : a ∈ lagPrimeWindow v w) (hb : b ∈ lagPrimeWindow v w) (hab : a < b) :
    ratioAtom a b = 0 ∨ ratioAtom a b = vonMangoldtAtom 2 ∨ ratioAtom a b = vonMangoldtAtom 3 :=
  ratioAtom_inDyadicWindow (inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (by omega) hb) hab

/-- **Crossing prime-power pairs in `lagPrimeWindow` are consecutive powers of `2` or `3`.** For
`2w < log 2` and `a, b ∈ lagPrimeWindow v w` with `1 ≤ a < b` and `IsPrimePow (a * b)`, we have
`(a, b) = (p^i, p^{i+1})` with `p = 2` or `p = 3`. -/
theorem consecutive_powers_of_mem_lagPrimeWindow_isPrimePow_mul {v w : ℝ} (hw : 2 * w < Real.log 2)
    {a b : ℕ} (ha1 : 1 ≤ a) (ha : a ∈ lagPrimeWindow v w) (hb : b ∈ lagPrimeWindow v w)
    (hab : a < b) (h : IsPrimePow (a * b)) :
    ∃ p i : ℕ, (p = 2 ∨ p = 3) ∧ a = p ^ i ∧ b = p ^ (i + 1) :=
  consecutive_powers_of_isPrimePow_mul (inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha)
    (inDyadicWindow_of_mem_lagPrimeWindow hw (by omega) hb) hab h

/-- **Uniqueness of the crossing pair per prime `p ∈ {2, 3}` in `lagPrimeWindow`.** For `2w < log 2`
and any prime `p`, at most one consecutive power pair `(p^i, p^{i+1})` can lie in
`lagPrimeWindow v w`: if `p^i, p^{i+1}, p^j, p^{j+1} ∈ lagPrimeWindow v w`, then `i = j`. -/
theorem unique_crossing_pair_in_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2) {p i j : ℕ}
    (hp : p.Prime) (hi : p ^ i ∈ lagPrimeWindow v w) (hi1 : p ^ (i + 1) ∈ lagPrimeWindow v w)
    (hj : p ^ j ∈ lagPrimeWindow v w) (hj1 : p ^ (j + 1) ∈ lagPrimeWindow v w) :
    i = j := by
  have h1 := lagPrimeWindow_exponent_sub_le_one hw hp hi hj1
  have h2 := lagPrimeWindow_exponent_sub_le_one hw hp hj hi1
  omega

/-- **Exact crossing-to-ratio factorization (`productAtom a b = ratioAtom a b / a`).** Whenever
`a < b` and `IsPrimePow (a * b)`, the crossing atom equals the same-side ratio atom divided by `a`. -/
theorem productAtom_eq_ratioAtom_div_of_isPrimePow {a b : ℕ} (hab : a < b)
    (h : IsPrimePow (a * b)) :
    productAtom a b = ratioAtom a b / a := by
  obtain ⟨p, i, j, hp, rfl, rfl, hij⟩ := exists_prime_pow_of_isPrimePow_mul h
  have hlt : i < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hab
  rw [productAtom_pow_pow hp hij, ratioAtom_pow_pow hp hlt, div_div]
  congr 1
  have hexp : i + j = (j - i) + 2 * i := by omega
  have hpow : ((p ^ (i + j) : ℕ) : ℝ) = ((p ^ (j - i) : ℕ) : ℝ) * (((p ^ i : ℕ) : ℝ) ^ 2) := by
    rw [hexp, pow_add, pow_mul']
    push_cast
    ring
  rw [hpow, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- For all `1 ≤ a < b`, `productAtom a b ≤ ratioAtom a b / a`. -/
theorem productAtom_le_ratioAtom_div {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    productAtom a b ≤ ratioAtom a b / a := by
  by_cases h : IsPrimePow (a * b)
  · rw [productAtom_eq_ratioAtom_div_of_isPrimePow hab h]
  · rw [productAtom_eq_zero_of_not_isPrimePow h]
    exact div_nonneg (ratioAtom_nonneg a b) (by positivity)

/-- **Exponential lag suppression of crossing atoms in `lagPrimeWindow`.** For `a ∈ lagPrimeWindow v w`
with `1 ≤ a < b`, `productAtom a b ≤ e^{−(v − 2w)} ratioAtom a b` and
`(1 − e^{−(v − 2w)}) ratioAtom a b ≤ netAtom a b`. -/
theorem productAtom_le_exp_neg_mul_ratioAtom_of_mem_lagPrimeWindow {v w : ℝ} {a b : ℕ}
    (ha1 : 1 ≤ a) (ha : a ∈ lagPrimeWindow v w) (hab : a < b) :
    productAtom a b ≤ Real.exp (-(v - 2 * w)) * ratioAtom a b ∧
      (1 - Real.exp (-(v - 2 * w))) * ratioAtom a b ≤ netAtom a b := by
  have halo := (exp_sub_le_and_le_exp_add_of_mem_lagPrimeWindow ha1 ha).1
  have h1 : productAtom a b ≤ Real.exp (-(v - 2 * w)) * ratioAtom a b := by
    calc productAtom a b ≤ ratioAtom a b / a := productAtom_le_ratioAtom_div ha1 hab
      _ ≤ ratioAtom a b / Real.exp (v - 2 * w) :=
          div_le_div_of_nonneg_left (ratioAtom_nonneg a b) (Real.exp_pos _) halo
      _ = Real.exp (-(v - 2 * w)) * ratioAtom a b := by
          rw [Real.exp_neg, div_eq_inv_mul]
  refine ⟨h1, ?_⟩
  unfold netAtom
  linarith

/-! ### 3. Lag-side pair-payment ledger on `lagPrimeWindow` -/

/-- The doubling energy `vonMangoldtAtom 2 · ∑_{a, b ∈ S, b = 2a} (c a − c b)²` of a profile `c`
on a support `S`. -/
def lagDoublingEnergy (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if b = 2 * a then vonMangoldtAtom 2 * (c a - c b) ^ 2 else 0

/-- The tripling energy `vonMangoldtAtom 3 · ∑_{a, b ∈ S, b = 3a} (c a − c b)²` of a profile `c`
on a support `S`. -/
def lagTriplingEnergy (S : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ a ∈ S, ∑ b ∈ S, if b = 3 * a then vonMangoldtAtom 3 * (c a - c b) ^ 2 else 0

theorem lagDoublingEnergy_nonneg (S : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ lagDoublingEnergy S c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg (vonMangoldtAtom_nonneg 2) (sq_nonneg _)
    · exact le_rfl

theorem lagTriplingEnergy_nonneg (S : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ lagTriplingEnergy S c :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · exact mul_nonneg (vonMangoldtAtom_nonneg 3) (sq_nonneg _)
    · exact le_rfl

/-- **Exact Doubling–Tripling Exhaustion of Same-Side Window Energy.** For `2w < log 2` and any
`S ⊆ lagPrimeWindow v w` with `∀ a ∈ S, 1 ≤ a`, the same-side ratio energy on `S` equals the sum
of the doubling and tripling energies:
`ratioEnergy S c = lagDoublingEnergy S c + lagTriplingEnergy S c`. -/
theorem ratioEnergy_eq_lagDoublingEnergy_add_lagTriplingEnergy {v w : ℝ} (hw : 2 * w < Real.log 2)
    {S : Finset ℕ} (hSw : S ⊆ lagPrimeWindow v w) (hS1 : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    ratioEnergy S c = lagDoublingEnergy S c + lagTriplingEnergy S c := by
  unfold ratioEnergy lagDoublingEnergy lagTriplingEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  have ha1 : 1 ≤ a := hS1 a ha
  by_cases h2 : b = 2 * a
  · have hab : a < b := by omega
    have h3 : b ≠ 3 * a := by omega
    have hdvd : a ∣ b := ⟨2, by omega⟩
    have hdiv : b / a = 2 := by rw [h2, Nat.mul_div_cancel 2 (by omega)]
    rw [if_pos hab, if_pos h2, if_neg h3, ratioAtom, if_pos hdvd, hdiv, add_zero]
  · by_cases h3 : b = 3 * a
    · have hab : a < b := by omega
      have hdvd : a ∣ b := ⟨3, by omega⟩
      have hdiv : b / a = 3 := by rw [h3, Nat.mul_div_cancel 3 (by omega)]
      rw [if_pos hab, if_neg h2, if_pos h3, ratioAtom, if_pos hdvd, hdiv, zero_add]
    · rw [if_neg h2, if_neg h3, add_zero]
      split_ifs with hab
      · unfold ratioAtom
        split_ifs with hdvd
        · rcases eq_two_mul_or_three_mul_of_mem_lagPrimeWindow hw ha1 (hSw ha) (hSw hb) hab hdvd
            with h2' | h3'
          · exact False.elim (h2 h2')
          · exact False.elim (h3 h3')
        · simp
      · rfl

/-- **Exponential Payment of Crossing Prime Pairs by Doublings and Triplings.** For `2w < log 2`
and any `S ⊆ lagPrimeWindow v w` with `∀ a ∈ S, 1 ≤ a`, the crossing prime-pair energy is paid by
the doubling and tripling energies with an exponential lag discount `e^{−(v − 2w)}`:
`productEnergy S c ≤ e^{−(v − 2w)} (lagDoublingEnergy S c + lagTriplingEnergy S c)`. -/
theorem productEnergy_le_exp_neg_mul_of_subset_lagPrimeWindow {v w : ℝ} (hw : 2 * w < Real.log 2)
    {S : Finset ℕ} (hSw : S ⊆ lagPrimeWindow v w) (hS1 : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    productEnergy S c ≤
      Real.exp (-(v - 2 * w)) * (lagDoublingEnergy S c + lagTriplingEnergy S c) := by
  rw [← ratioEnergy_eq_lagDoublingEnergy_add_lagTriplingEnergy hw hSw hS1 c]
  unfold productEnergy ratioEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  split_ifs with hab
  · have h := (productAtom_le_exp_neg_mul_ratioAtom_of_mem_lagPrimeWindow
      (hS1 a ha) (hSw ha) hab).1
    calc productAtom a b * (c a - c b) ^ 2
        ≤ (Real.exp (-(v - 2 * w)) * ratioAtom a b) * (c a - c b) ^ 2 :=
          mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = Real.exp (-(v - 2 * w)) * (ratioAtom a b * (c a - c b) ^ 2) := by ring
  · simp

/-- **Net Skeleton Coercivity on `lagPrimeWindow`.** For `2w < log 2` and `S ⊆ lagPrimeWindow v w`
(`∀ a ∈ S, 1 ≤ a`), the net skeleton energy retains at least `1 − e^{−(v − 2w)}` of the doubling
and tripling energies:
`(1 − e^{−(v − 2w)}) (lagDoublingEnergy S c + lagTriplingEnergy S c) ≤ skeletonEnergy S c`. -/
theorem skeletonEnergy_ge_one_sub_exp_neg_mul_of_subset_lagPrimeWindow {v w : ℝ}
    (hw : 2 * w < Real.log 2) {S : Finset ℕ} (hSw : S ⊆ lagPrimeWindow v w)
    (hS1 : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    (1 - Real.exp (-(v - 2 * w))) * (lagDoublingEnergy S c + lagTriplingEnergy S c) ≤
      skeletonEnergy S c := by
  rw [skeletonEnergy_eq_sub,
    ratioEnergy_eq_lagDoublingEnergy_add_lagTriplingEnergy hw hSw hS1 c]
  have h := productEnergy_le_exp_neg_mul_of_subset_lagPrimeWindow hw hSw hS1 c
  linarith

/-- Degree-`1` partial-matching bound for a multiplier `m ≥ 1` on a finite support `S`:
`∑_{a, b ∈ S, b = m a} (c a − c b)² ≤ 4 ∑_{a ∈ S} c(a)²`. -/
theorem sum_sq_sub_eq_mul_le_four_mul_sum_sq {m : ℕ} (hm : 1 ≤ m) (S : Finset ℕ) (c : ℕ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ S, if b = m * a then (c a - c b) ^ 2 else 0) ≤
      4 * ∑ a ∈ S, c a ^ 2 := by
  have hpt : ∑ a ∈ S, ∑ b ∈ S, (if b = m * a then (c a - c b) ^ 2 else 0) ≤
      ∑ a ∈ S, ∑ b ∈ S, (if b = m * a then 2 * c a ^ 2 + 2 * c b ^ 2 else 0) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    split_ifs
    · have : 0 ≤ (c a + c b) ^ 2 := sq_nonneg _
      linarith
    · exact le_rfl
  have hsplit : ∑ a ∈ S, ∑ b ∈ S, (if b = m * a then 2 * c a ^ 2 + 2 * c b ^ 2 else 0) =
      2 * (∑ a ∈ S, ∑ b ∈ S, if b = m * a then c a ^ 2 else 0) +
      2 * (∑ a ∈ S, ∑ b ∈ S, if b = m * a then c b ^ 2 else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  have hrow : (∑ a ∈ S, ∑ b ∈ S, if b = m * a then c a ^ 2 else 0) ≤ ∑ a ∈ S, c a ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hcol : (∑ a ∈ S, ∑ b ∈ S, if b = m * a then c b ^ 2 else 0) ≤ ∑ b ∈ S, c b ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b _ => ?_
    by_cases hdiv : ∃ a ∈ S, b = m * a
    · obtain ⟨a₀, ha₀, rfl⟩ := hdiv
      have heq : ∀ a ∈ S, (if m * a₀ = m * a then c (m * a₀) ^ 2 else 0) =
          if a = a₀ then c (m * a₀) ^ 2 else 0 := by
        intro a _
        have hiff : m * a₀ = m * a ↔ a = a₀ := by
          rw [mul_eq_mul_left_iff, or_iff_left (by omega), eq_comm]
        simp only [hiff]
      rw [Finset.sum_congr rfl heq, Finset.sum_ite_eq', if_pos ha₀]
    · push Not at hdiv
      rw [Finset.sum_eq_zero fun a ha => if_neg (hdiv a ha)]
      exact sq_nonneg _
  linarith

/-- Degree-`1` partial-matching bound on the doubling energy:
`lagDoublingEnergy S c ≤ 4 * vonMangoldtAtom 2 * ∑_{a ∈ S} c(a)²`. -/
theorem lagDoublingEnergy_le_four_mul_sum_sq (S : Finset ℕ) (c : ℕ → ℝ) :
    lagDoublingEnergy S c ≤ 4 * vonMangoldtAtom 2 * ∑ a ∈ S, c a ^ 2 := by
  have heq : lagDoublingEnergy S c =
      vonMangoldtAtom 2 * ∑ a ∈ S, ∑ b ∈ S, if b = 2 * a then (c a - c b) ^ 2 else 0 := by
    unfold lagDoublingEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left
    (sum_sq_sub_eq_mul_le_four_mul_sum_sq (m := 2) (by omega) S c)
    (vonMangoldtAtom_nonneg 2)
  linarith

/-- Degree-`1` partial-matching bound on the tripling energy:
`lagTriplingEnergy S c ≤ 4 * vonMangoldtAtom 3 * ∑_{a ∈ S} c(a)²`. -/
theorem lagTriplingEnergy_le_four_mul_sum_sq (S : Finset ℕ) (c : ℕ → ℝ) :
    lagTriplingEnergy S c ≤ 4 * vonMangoldtAtom 3 * ∑ a ∈ S, c a ^ 2 := by
  have heq : lagTriplingEnergy S c =
      vonMangoldtAtom 3 * ∑ a ∈ S, ∑ b ∈ S, if b = 3 * a then (c a - c b) ^ 2 else 0 := by
    unfold lagTriplingEnergy
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left
    (sum_sq_sub_eq_mul_le_four_mul_sum_sq (m := 3) (by omega) S c)
    (vonMangoldtAtom_nonneg 3)
  linarith

/-- **Same-Side Window Energy Bound by Doubling and Tripling Atoms.** For `2w < log 2` and
`S ⊆ lagPrimeWindow v w` (`∀ a ∈ S, 1 ≤ a`),
`ratioEnergy S c ≤ 4 * (vonMangoldtAtom 2 + vonMangoldtAtom 3) * ∑_{a ∈ S} c(a)²`. -/
theorem ratioEnergy_le_four_mul_atom_two_add_three_mul_sum_sq {v w : ℝ} (hw : 2 * w < Real.log 2)
    {S : Finset ℕ} (hSw : S ⊆ lagPrimeWindow v w) (hS1 : ∀ a ∈ S, 1 ≤ a) (c : ℕ → ℝ) :
    ratioEnergy S c ≤
      4 * (vonMangoldtAtom 2 + vonMangoldtAtom 3) * ∑ a ∈ S, c a ^ 2 := by
  rw [ratioEnergy_eq_lagDoublingEnergy_add_lagTriplingEnergy hw hSw hS1 c]
  have h2 := lagDoublingEnergy_le_four_mul_sum_sq S c
  have h3 := lagTriplingEnergy_le_four_mul_sum_sq S c
  linarith

/-! ### 4. Inter-lag window decoupling across two lags `v₁ ≤ v₂` -/

/-- **Inter-lag multiplier band.** If `2w < log 2`, `1 ≤ a ∈ lagPrimeWindow v₁ w`,
`1 ≤ b ∈ lagPrimeWindow v₂ w`, and `a ∣ b`, then the multiplier `m = b / a` satisfies
`e^{v₂} < 4 e^{v₁} m` and `m e^{v₁} < 4 e^{v₂}` (`e^{v₂ − v₁} / 4 < m < 4 e^{v₂ − v₁}`). -/
theorem div_bounds_of_mem_lagPrimeWindows_dvd {v₁ v₂ w : ℝ} (hw : 2 * w < Real.log 2) {a b : ℕ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (ha : a ∈ lagPrimeWindow v₁ w) (hb : b ∈ lagPrimeWindow v₂ w)
    (hdvd : a ∣ b) :
    Real.exp v₂ < 4 * Real.exp v₁ * (b / a : ℕ) ∧
      ((b / a : ℕ) : ℝ) * Real.exp v₁ < 4 * Real.exp v₂ := by
  have haw := inDyadicWindow_of_mem_lagPrimeWindow hw ha1 ha
  have hbw := inDyadicWindow_of_mem_lagPrimeWindow hw hb1 hb
  set m := b / a
  have hba : b = m * a := (Nat.div_mul_cancel hdvd).symm
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · rw [hm0, zero_mul] at hba; omega
    · exact hpos
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm1
  have hbR : (b : ℝ) = (m : ℝ) * (a : ℝ) := by exact_mod_cast hba
  constructor
  · have h1 : Real.exp v₂ / 2 < (m : ℝ) * (a : ℝ) := by linarith [hbw.1]
    have h2 : (m : ℝ) * (a : ℝ) < (m : ℝ) * (2 * Real.exp v₁) := mul_lt_mul_of_pos_left haw.2 hm_pos
    linarith
  · have h1 : (m : ℝ) * (Real.exp v₁ / 2) < (m : ℝ) * (a : ℝ) :=
      mul_lt_mul_of_pos_left haw.1 hm_pos
    have h2 : (m : ℝ) * (a : ℝ) < 2 * Real.exp v₂ := by linarith [hbw.2]
    linarith

/-- **Complete decoupling of doublings and triplings across separated lag windows.** When
`12 e^{v₁} ≤ e^{v₂}` (`v₂ − v₁ ≥ log 12`) and `2w < log 2`, every divisor relation `a ∣ b`
between `a ∈ lagPrimeWindow v₁ w` (`1 ≤ a`) and `b ∈ lagPrimeWindow v₂ w` (`1 ≤ b`) has
`4 ≤ b / a`. -/
theorem four_le_div_of_mem_lagPrimeWindows_of_twelve_mul_exp_le {v₁ v₂ w : ℝ}
    (hw : 2 * w < Real.log 2) (hv : 12 * Real.exp v₁ ≤ Real.exp v₂) {a b : ℕ}
    (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) (ha : a ∈ lagPrimeWindow v₁ w) (hb : b ∈ lagPrimeWindow v₂ w)
    (hdvd : a ∣ b) :
    4 ≤ b / a := by
  have hband := (div_bounds_of_mem_lagPrimeWindows_dvd hw ha1 hb1 ha hb hdvd).1
  have hlt : 3 * (4 * Real.exp v₁) < ((b / a : ℕ) : ℝ) * (4 * Real.exp v₁) := by linarith
  have h3 : (3 : ℝ) < ((b / a : ℕ) : ℝ) := lt_of_mul_lt_mul_right hlt (by positivity)
  have h3_nat : 3 < b / a := by exact_mod_cast h3
  omega

end GaloisForLFunctions.SquareRootThreshold
