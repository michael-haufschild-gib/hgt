import GaloisForLFunctions.RHTower.MarkovSecantNumeratorAndCubicOriginPositivityPBAP

/-!
# The Combined Secant-Secular Counterterm Weight, Exact Quadratic-Minus-Cubic Cancellation, and the Unconditional `(43√2 - 56) / 6 > 4 / 5` Positive $L^2$ Surplus

In Module 46 and Module 47, we decomposed `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
in two stages:
1. Trapezoidal endpoint averaging extracted `2 * (√2 - 1) * ∫ ‖f.1‖²` at `n = 1` plus
   `primeBlindCounterterm trapezoidalSecularDiffWeight f` plus `trapezoidalNumeratorCellDefect f.1 N`.
2. Upgrading the midpoint average to the linear secant `cellSecant (weilSymmetricLogNumerator f.1) n x`
   extracted the cubic slope sum `∑_{n=2}^N -(1 / 3) * (√n - √(n - 1)) ^ 3 * (C_f(n) - C_f(n - 1))`
   plus `secantNumeratorCellDefect f.1 N`.

In this module, we combine the quadratic secular counterterm from Stage 1 and the cubic slope
counterterm from Stage 2 into a **Single Nonnegative Counterterm Weight** `secantCombinedSecularWeight`:

1. **Section 1 (The Combined Secant-Secular Weight `secantCombinedSecularWeight` and Its Exact
   Nonnegativity via `(a - b) ^ 2 * (a + 2 * b) ≥ 0`):**
   - We define `secantCubicCountertermWeight n := if 2 ≤ n then ((√n - √(n - 1)) ^ 3 - (√(n + 1) - √n) ^ 3) * √n / 3 else 0`
     and `secantCombinedSecularWeight n := trapezoidalSecularDiffWeight n - secantCubicCountertermWeight n`.
   - Using the exact polynomial identity
     `a * (a ^ 2 - b ^ 2) / 2 - (a ^ 3 - b ^ 3) / 3 = (a - b) ^ 2 * (a + 2 * b) / 6 ≥ 0`
     (`cube_sub_cube_div_three_le_mul_sq_sub_sq_div_two`) together with `(√n - √(n - 1)) * √n ≤ 1`
     (`sqrt_sub_sqrt_pred_mul_sqrt_le_one`), we prove that the quadratic term strictly dominates the
     cubic term on every cell, so `0 ≤ secantCombinedSecularWeight n` for all `n : ℕ`
     (`secantCombinedSecularWeight_nonneg`)!

2. **Section 2 (Exact Decomposition of `rightCellQuadratureDefect` into `((16√2 - 20) / 3) ∫ ‖f.1‖²` +
   `primeBlindCounterterm secantCombinedSecularWeight` + `secantNumeratorCellDefect`):**
   - Summing the cubic slope term by parts (`sum_cubic_diff_weilSymmetricLogNumerator_eq_origin_sub_counterterm`)
     adds `+(2 / 3) * (√2 - 1) ^ 3 * ∫ ‖f.1‖²` to the `n = 1` origin term and subtracts
     `primeBlindCounterterm secantCubicCountertermWeight f` from the `n ≥ 2` counterterm.
   - Combining with Module 46 yields the exact decomposition
     (`rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator`):
     `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = ((16 * √2 - 20) / 3) * ∫ ‖f.1‖² + primeBlindCounterterm secantCombinedSecularWeight f + secantNumeratorCellDefect f.1 N`.

3. **Section 3 (The `(16 - 11√2) / 6 < 3 / 40` Counterterm Bound and the Unconditional
   `(43√2 - 56) / 6 > 4 / 5` Positive $L^2$ Surplus):**
   - Because `0 ≤ secantCombinedSecularWeight n`, the cubic counterterm **subtracts directly** from
     the quadratic counterterm inside the absolute value without triangle-inequality loss:
     `|primeBlindCounterterm secantCombinedSecularWeight f| ≤ ((16 - 11 * √2) / 6) * ∫ ‖f.1‖² ≤ (3 / 40) * ∫ ‖f.1‖²`
     (`abs_primeBlindCounterterm_secantCombinedSecularWeight_le`).
   - Subtracting `(16 - 11√2) / 6` from the origin surplus `(16√2 - 20) / 3` yields the
     **Unconditional `(43√2 - 56) / 6 > 4 / 5 = 0.8` Positive $L^2$ Surplus**
     (`four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect`):
     `(4 / 5) * ∫ ‖f.1‖² + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Combined Secant-Secular Weight `secantCombinedSecularWeight` and Its Exact Nonnegativity via `(a - b) ^ 2 * (a + 2 * b) ≥ 0` -/

/-- The **Secant Cubic Slope Counterterm Weight**:
`secantCubicCountertermWeight n = ((√n - √(n - 1)) ^ 3 - (√(n + 1) - √n) ^ 3) * √n / 3` for `n ≥ 2`,
and `0` for `n < 2`. -/
def secantCubicCountertermWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then
    ((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
      (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3) * Real.sqrt n / 3
  else 0

/-- The **Combined Secant-Secular Counterterm Weight**:
`secantCombinedSecularWeight n = trapezoidalSecularDiffWeight n - secantCubicCountertermWeight n`. -/
def secantCombinedSecularWeight (n : ℕ) : ℝ :=
  trapezoidalSecularDiffWeight n - secantCubicCountertermWeight n

/-- For every `n : ℕ`, `0 ≤ secantCubicCountertermWeight n`. -/
theorem secantCubicCountertermWeight_nonneg (n : ℕ) :
    0 ≤ secantCubicCountertermWeight n := by
  unfold secantCubicCountertermWeight
  split_ifs with hn
  · have hle := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred (by omega : 1 ≤ n)
    have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hcube : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3 ≤
        (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 :=
      pow_le_pow_left₀ hnonneg hle 3
    have hsub : 0 ≤ (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
        (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3 :=
      sub_nonneg.mpr hcube
    exact div_nonneg (mul_nonneg hsub (Real.sqrt_nonneg n)) (by norm_num)
  · exact le_rfl

/-- **Exact Cubic-vs-Quadratic Dominance Inequality**:
for any `a b : ℝ` with `0 ≤ a` and `0 ≤ b`,
`(a ^ 3 - b ^ 3) / 3 ≤ a * (a ^ 2 - b ^ 2) / 2` because
`a * (a ^ 2 - b ^ 2) / 2 - (a ^ 3 - b ^ 3) / 3 = (a - b) ^ 2 * (a + 2 * b) / 6 ≥ 0`. -/
theorem cube_sub_cube_div_three_le_mul_sq_sub_sq_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ 3 - b ^ 3) / 3 ≤ a * (a ^ 2 - b ^ 2) / 2 := by
  have hpos : 0 ≤ (a - b) ^ 2 * (a + 2 * b) :=
    mul_nonneg (sq_nonneg (a - b)) (by linarith [ha, hb])
  linarith

/-- For every `1 ≤ n`, `(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * Real.sqrt n ≤ 1`. -/
theorem sqrt_sub_sqrt_pred_mul_sqrt_le_one {n : ℕ} (hn : 1 ≤ n) :
    (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * Real.sqrt n ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsq1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1
  have hconj : (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) *
      (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
    linear_combination hsq0 - hsq1
  have hdiff_nonneg : 0 ≤ Real.sqrt n - Real.sqrt ((n : ℝ) - 1) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hpred_nonneg : 0 ≤ Real.sqrt ((n : ℝ) - 1) := Real.sqrt_nonneg _
  have hprod_nonneg : 0 ≤ (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * Real.sqrt ((n : ℝ) - 1) :=
    mul_nonneg hdiff_nonneg hpred_nonneg
  linarith

/-- **Pointwise Nonnegativity of `secantCombinedSecularWeight`**:
for every `n : ℕ`, `0 ≤ secantCombinedSecularWeight n`. -/
theorem secantCombinedSecularWeight_nonneg (n : ℕ) :
    0 ≤ secantCombinedSecularWeight n := by
  unfold secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
  split_ifs with hn
  · set a := Real.sqrt n - Real.sqrt ((n : ℝ) - 1)
    set b := Real.sqrt ((n : ℝ) + 1) - Real.sqrt n
    have ha : 0 ≤ a := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hb : 0 ≤ b := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hba : b ≤ a := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred (by omega : 1 ≤ n)
    have hsq_nonneg : 0 ≤ a ^ 2 - b ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hb hba 2)
    have hcube := cube_sub_cube_div_three_le_mul_sq_sub_sq_div_two ha hb
    have hmul_sqrt := mul_le_mul_of_nonneg_right hcube (Real.sqrt_nonneg n)
    have ha_sqrt : a * Real.sqrt n ≤ 1 := sqrt_sub_sqrt_pred_mul_sqrt_le_one (by omega : 1 ≤ n)
    have hbound : a * (a ^ 2 - b ^ 2) / 2 * Real.sqrt n ≤ (a ^ 2 - b ^ 2) / 2 := by
      have h1 := mul_le_mul_of_nonneg_left ha_sqrt (div_nonneg hsq_nonneg (by norm_num : (0 : ℝ) ≤ 2))
      linarith
    linarith
  · linarith

/-! ## Section 2: Exact Decomposition of `rightCellQuadratureDefect` with `secantCombinedSecularWeight` and `secantNumeratorCellDefect` -/

/-- Finite-cutoff formula for `primeBlindCounterterm secantCubicCountertermWeight f`: -/
theorem primeBlindCounterterm_secantCubicCountertermWeight_eq_sum_Icc (f : WeilTestFn) {N : ℕ}
     (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm secantCubicCountertermWeight f =
      ∑ n ∈ Finset.Icc 2 N,
        (((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
            (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3) / 3) *
          weilSymmetricLogNumerator f.1 (n : ℝ) := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCubicCountertermWeight f hN]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn1 : 1 ≤ n := by omega
  simp only [secantCubicCountertermWeight, if_pos hn.1]
  rw [weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue f.1 hn1]
  ring

/-- **Exact Summation-by-Parts Identity for the Cubic Square-Root Slope Sum**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`∑ n ∈ Finset.Icc 2 N, -(1 / 3) * (√n - √(n - 1)) ^ 3 * (C_f(n) - C_f(n - 1)) = (2 / 3) * (√2 - 1) ^ 3 * (∫ u, ‖f.1 u‖ ^ 2) - primeBlindCounterterm secantCubicCountertermWeight f`. -/
theorem sum_cubic_diff_weilSymmetricLogNumerator_eq_origin_sub_counterterm
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (∑ n ∈ Finset.Icc 2 N,
        -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 *
          (weilSymmetricLogNumerator f.1 (n : ℝ) -
            weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))) =
      (2 / 3) * (Real.sqrt 2 - 1) ^ 3 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        primeBlindCounterterm secantCubicCountertermWeight f := by
  let w : ℕ → ℝ := fun n => (1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3
  let v : ℕ → ℝ := fun n => weilSymmetricLogNumerator f.1 (n : ℝ)
  have hcongr : (∑ n ∈ Finset.Icc 2 N,
        -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 *
          (weilSymmetricLogNumerator f.1 (n : ℝ) -
            weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))) =
      -(∑ n ∈ Finset.Icc 2 N, w n * (v n - v (n - 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    dsimp [w, v]
    rw [hcast]
    ring
  rw [hcongr, sum_Icc_two_mul_sub_pred w v hN1]
  have hvN : v N = 0 := by
    dsimp [v]
    rw [weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue f.1 hN1]
    simp [logValue, hN0.1, hN0.2]
  have hv1 : v 1 = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    dsimp [v]
    rw [Nat.cast_one]
    exact weilSymmetricLogNumerator_one_eq_two_mul_integral_norm_sq f
  have hw2 : w 2 = (1 / 3) * (Real.sqrt 2 - 1) ^ 3 := by
    dsimp [w]
    norm_num
  have hsum_eq : (∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * v n) =
      primeBlindCounterterm secantCubicCountertermWeight f := by
    rw [primeBlindCounterterm_secantCubicCountertermWeight_eq_sum_Icc f hN]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [w, v]
    push_cast
    rw [add_sub_cancel_right]
    ring
  rw [hvN, mul_zero, zero_sub, hw2, hv1, hsum_eq]
  ring

/-- Difference linearity of `primeBlindCounterterm` for `secantCombinedSecularWeight`: -/
theorem primeBlindCounterterm_secantCombinedSecularWeight_eq_sub (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm secantCombinedSecularWeight f =
      primeBlindCounterterm trapezoidalSecularDiffWeight f -
        primeBlindCounterterm secantCubicCountertermWeight f := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN,
    primeBlindCounterterm_eq_sum_Icc trapezoidalSecularDiffWeight f hN,
    primeBlindCounterterm_eq_sum_Icc secantCubicCountertermWeight f hN,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold secantCombinedSecularWeight
  ring

/-- **Exact Secant-Numerator Decomposition of `rightCellQuadratureDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = ((16 * Real.sqrt 2 - 20) / 3) * (∫ u, ‖f.1 u‖ ^ 2) + primeBlindCounterterm secantCombinedSecularWeight f + secantNumeratorCellDefect f.1 N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      ((16 * Real.sqrt 2 - 20) / 3) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        primeBlindCounterterm secantCombinedSecularWeight f +
        secantNumeratorCellDefect f.1 N := by
  rw [rightCellQuadratureDefect_weilContinuumLogProfile_eq_two_sqrt_two_sub_two_add_counterterm_add_trapezoidalNumerator f hN1 hN0 hN,
    trapezoidalNumeratorCellDefect_eq_cubic_diff_add_secantNumerator,
    sum_cubic_diff_weilSymmetricLogNumerator_eq_origin_sub_counterterm f hN1 hN0 hN,
    primeBlindCounterterm_secantCombinedSecularWeight_eq_sub f hN]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination ((2 * Real.sqrt 2 / 3 - 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) * hsq2

/-! ## Section 3: The `(16 - 11√2) / 6 < 3 / 40` Counterterm Bound and the Unconditional `(43√2 - 56) / 6 > 4 / 5` Positive $L^2$ Surplus -/

/-- For every `2 ≤ n`,
`secantCombinedSecularWeight n * (2 / √n) ≤ ((√n - √(n - 1)) ^ 2 - (√(n + 1) - √n) ^ 2) / √2 - 2 * ((√n - √(n - 1)) ^ 3 - (√(n + 1) - √n) ^ 3) / 3`. -/
theorem secantCombinedSecularWeight_mul_two_div_sqrt_le {n : ℕ} (hn : 2 ≤ n) :
    secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤
      ((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
          (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2) / Real.sqrt 2 -
        2 * ((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
          (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3) / 3 := by
  unfold secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
  simp only [if_pos hn]
  have hn_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hne : Real.sqrt n ≠ 0 := ne_of_gt hn_pos
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hinv_le : (Real.sqrt n)⁻¹ ≤ (Real.sqrt 2)⁻¹ := inv_anti₀ hsqrt2_pos hsqrt_le
  set Δ2 := (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
    (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2
  set Δ3 := (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
    (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3
  have hΔ2_nonneg : 0 ≤ Δ2 := by
    have hle := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred (by omega : 1 ≤ n)
    have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    exact sub_nonneg.mpr (pow_le_pow_left₀ hnonneg hle 2)
  have hterm1 : (Δ2 / 2) * (2 / Real.sqrt n) ≤ Δ2 / Real.sqrt 2 := by
    rw [div_mul_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv_le hΔ2_nonneg
  have hterm2 : (Δ3 * Real.sqrt n / 3) * (2 / Real.sqrt n) = 2 * Δ3 / 3 := by
    rw [div_eq_mul_inv (Δ3 * Real.sqrt n) 3, div_eq_mul_inv 2 (Real.sqrt n)]
    calc
      Δ3 * Real.sqrt n * 3⁻¹ * (2 * (Real.sqrt n)⁻¹) =
          (2 * Δ3 / 3) * (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
      _ = 2 * Δ3 / 3 := by rw [mul_inv_cancel₀ hne, mul_one]
  rw [sub_mul, hterm2]
  linarith

/-- **Telescoping Upper Bound on `∑_{n=2}^N secantCombinedSecularWeight n * (2 / √n)`**:
for every `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ (16 - 11 * Real.sqrt 2) / 6`. -/
theorem sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
      (16 - 11 * Real.sqrt 2) / 6 := by
  let g : ℕ → ℝ := fun n =>
    (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 / Real.sqrt 2 -
      2 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 / 3
  have hle_sum : (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
      ∑ n ∈ Finset.Icc 2 N, (g n - g (n + 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    refine (secantCombinedSecularWeight_mul_two_div_sqrt_le hn.1).trans_eq ?_
    dsimp [g]
    push_cast
    rw [add_sub_cancel_right]
    ring
  rw [sum_Icc_two_sub_succ_nat g hN] at hle_sum
  have hg2 : g 2 = (16 - 11 * Real.sqrt 2) / 6 := by
    dsimp [g]
    norm_num
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hne2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hdiv : (Real.sqrt 2 - 1) ^ 2 / Real.sqrt 2 = (3 * Real.sqrt 2 - 4) / 2 := by
      apply mul_right_cancel₀ hne2
      rw [div_mul_cancel₀ _ hne2]
      linear_combination -(1 / 2 : ℝ) * hsq2
    rw [hdiv]
    linear_combination (2 - (2 / 3) * Real.sqrt 2) * hsq2
  have hgN_nonneg : 0 ≤ g (N + 1) := by
    dsimp [g]
    push_cast
    rw [add_sub_cancel_right]
    set d := Real.sqrt ((N : ℝ) + 1) - Real.sqrt N
    have hd_nonneg : 0 ≤ d := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hd_le_one : d ≤ 1 := by
      have hconj : d * (Real.sqrt ((N : ℝ) + 1) + Real.sqrt N) = 1 := by
        have h1 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
        have h0 : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
        dsimp [d]
        linear_combination h1 - h0
      have hsum_ge : 1 ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt N := by
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hsqrt1 : Real.sqrt (1 ^ 2) ≤ Real.sqrt ((N : ℝ) + 1) :=
          Real.sqrt_le_sqrt (by linarith)
        rw [Real.sqrt_sq zero_le_one] at hsqrt1
        linarith [Real.sqrt_nonneg N]
      nlinarith
    have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hinv_ge : (2 / 3 : ℝ) ≤ 1 / Real.sqrt 2 := by
      rw [le_div_iff₀ hsqrt2_pos]
      linarith
    have hd_factor : d ^ 2 / Real.sqrt 2 - 2 * d ^ 3 / 3 =
        d ^ 2 * (1 / Real.sqrt 2 - (2 / 3) * d) := by ring
    rw [hd_factor]
    exact mul_nonneg (sq_nonneg d) (by linarith)
  linarith

/-- Rational upper bound `(16 - 11 * Real.sqrt 2) / 6 ≤ 3 / 40`. -/
theorem sixteen_sub_eleven_sqrt_two_div_six_le_three_fortieths :
    (16 - 11 * Real.sqrt 2) / 6 ≤ 3 / 40 := by
  have h : (311 / 220 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 311 / 220)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Unconditional Uniform Bound on `primeBlindCounterterm secantCombinedSecularWeight f`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`|primeBlindCounterterm secantCombinedSecularWeight f| ≤ ((16 - 11 * Real.sqrt 2) / 6) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_secantCombinedSecularWeight_le (f : WeilTestFn) {N : ℕ}
    (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm secantCombinedSecularWeight f| ≤
      ((16 - 11 * Real.sqrt 2) / 6) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      |secantCombinedSecularWeight n * logValue f.1 n| ≤
        (secantCombinedSecularWeight n * (2 / Real.sqrt n)) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [abs_mul, abs_of_nonneg (secantCombinedSecularWeight_nonneg n), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f (by omega : 1 ≤ n))
      (secantCombinedSecularWeight_nonneg n)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le hN1) hnorm_nonneg

/-- Rational lower bound `4 / 5 ≤ (43 * Real.sqrt 2 - 56) / 6`. -/
theorem four_fifths_le_forty_three_sqrt_two_sub_fifty_six_div_six :
    (4 / 5 : ℝ) ≤ (43 * Real.sqrt 2 - 56) / 6 := by
  have h : (304 / 215 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 304 / 215)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Unconditional `(43√2 - 56) / 6` Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`((43 * Real.sqrt 2 - 56) / 6) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem forty_three_sqrt_two_sub_fifty_six_div_six_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    ((43 * Real.sqrt 2 - 56) / 6) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have habs := (abs_le.mp (abs_primeBlindCounterterm_secantCombinedSecularWeight_le f hN1 hN)).1
  linarith

/-- **Unconditional `4 / 5` Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(4 / 5) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (4 / 5) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 :=
    forty_three_sqrt_two_sub_fifty_six_div_six_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_right
    four_fifths_le_forty_three_sqrt_two_sub_fifty_six_div_six hnorm_nonneg
  linarith

/-- **Upgraded `4 / 5`-Slope Coercive Lower Bound on `markovEnergy` in Terms of
`secantNumeratorCellDefect` (Primitive Hyperplane)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, if `θ ≥ max (5 / 2) (Real.log N)`
and `0 ≤ iteratedForwardDiff m (logValue F) n` on `[2, N]`, then `(4 / 5) * θ ≥ 2`, and
`(1 / 100 + (4 / 5) * θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * secantNumeratorCellDefect F N ≤ markovEnergy F`. -/
theorem four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero (m : ℕ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log (N : ℝ) ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100 + (4 / 5) * θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * secantNumeratorCellDefect (realWeilTestFn f hf hfc).1 N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have hquad := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have hθquad := mul_le_mul_of_nonneg_left hquad hθ0
  linarith

end RHTower

end
