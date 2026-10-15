import GaloisForLFunctions.RHTower.MarkovSqrtMatchedCombAndNumeratorQuadraturePBAP

/-!
# Trapezoidal Secular Cancellation, Summation-by-Parts Origin Extraction, and the Unconditional `√2 / 2 > 7 / 10` Positive $L^2$ Surplus in `rightCellQuadratureDefect`

In Module 45, we decomposed `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N` using
right-endpoint numerator differences on each unit cell `[n - 1, n]`, where the secular drift term
`primeBlindCounterterm secularSqrtSqWeight f` was bounded below by `-(1 - 1 / √N) ∫ ‖f.1‖²`.

In this module, we combine the **left-endpoint** and **right-endpoint** secular decompositions on
each unit cell `[n - 1, n]` to form the **Trapezoidal Secular-Plus-Numerator Decomposition**:

1. **Section 1 (Left-Endpoint and Trapezoidal Secular Drift Identities on `[n - 1, n]` and
   `trapezoidalNumeratorCellDefect`):**
   - At the left endpoint `n - 1` of `[n - 1, n]` (`n ≥ 2`), the secular weight integral has the
     **opposite sign** to the right endpoint:
     `2 * √(n - 1) * (√n - √(n - 1)) - 1 = -(√n - √(n - 1)) ^ 2`
     (`two_mul_sqrt_pred_mul_sqrt_sub_sub_one_eq_neg_sq`).
   - Consequently (`intervalIntegral_const_pred_div_sqrt_sub_logValue_eq`),
     `∫ x in (n - 1)..n, (C_f(n - 1) / √x - logValue f (n - 1)) = -(√n - √(n - 1)) ^ 2 * logValue f (n - 1)`.
   - Averaging the left- and right-endpoint decompositions cancels the secular `1 / √x` drift to
     second order on every cell (`trueTrapezoidalCellDefect_weilContinuumLogProfile_eq_secular_diff_add_trapezoidalNumerator`):
     `trueTrapezoidalCellDefect (weilContinuumLogProfile f.1) N = ∑ n ∈ Finset.Icc 2 N, (1 / 2) * (√n - √(n - 1)) ^ 2 * (logValue f.1 n - logValue f.1 (n - 1)) + trapezoidalNumeratorCellDefect f.1 N`.

2. **Section 2 (Summation-by-Parts Extraction of the $n = 1$ Origin Term from the Trapezoidal
   Secular Drift and the Positive Telescoping Weight `trapezoidalSecularDiffWeight`):**
   - We prove the general summation-by-parts identity (`sum_Icc_two_mul_sub_pred`) on `Finset.Icc 2 N`:
     `∑ n ∈ Finset.Icc 2 N, w n * (v n - v (n - 1)) = w (N + 1) * v N - w 2 * v 1 + ∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * v n`.
   - Defining `trapezoidalSecularDiffWeight n := if 2 ≤ n then ((√n - √(n - 1)) ^ 2 - (√(n + 1) - √n) ^ 2) / 2 else 0`,
     we prove `0 ≤ trapezoidalSecularDiffWeight n` for all `n : ℕ` and the exact identity
     (`rightCellQuadratureDefect_weilContinuumLogProfile_eq_two_sqrt_two_sub_two_add_counterterm_add_trapezoidalNumerator`):
     `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = 2 * (√2 - 1) * ∫ u, ‖f.1 u‖ ^ 2 + primeBlindCounterterm trapezoidalSecularDiffWeight f + trapezoidalNumeratorCellDefect f.1 N`.

3. **Section 3 (Unconditional `√2 / 2 > 7 / 10` Positive $L^2$ Surplus in
   `rightCellQuadratureDefect` and Pure Trapezoidal Numerator Coercivity):**
   - Since `∑_{n=2}^N trapezoidalSecularDiffWeight n = ((√2 - 1) ^ 2 - (√(N + 1) - √N) ^ 2) / 2 ≤ (√2 - 1) ^ 2 / 2`
     and `|logValue f.1 n| ≤ √2 * ∫ ‖f.1‖²` for all `n ≥ 2`, we prove the unconditional bound
     (`abs_primeBlindCounterterm_trapezoidalSecularDiffWeight_le`):
     `|primeBlindCounterterm trapezoidalSecularDiffWeight f| ≤ (√2 / 2) * (√2 - 1) ^ 2 * ∫ u, ‖f.1 u‖ ^ 2 = ((3 * √2 - 4) / 2) * ∫ u, ‖f.1 u‖ ^ 2`.
   - Subtracting this from the origin surplus `2 * (√2 - 1) * ∫ ‖f.1‖²` leaves the **Strictly
     Positive Unconditional $L^2$ Surplus**
     `2 * (√2 - 1) - (3 * √2 - 4) / 2 = √2 / 2 > 7 / 10`:
     `(√2 / 2) * ∫ ‖f.1‖² + trapezoidalNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     and `(7 / 10) * ∫ ‖f.1‖² + trapezoidalNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`!
   - Consequently, on the primitive hyperplane and odd sector, for any slope `θ ≥ 20 / 7` (since
     `(20 / 7) * (7 / 10) = 2`), `θ * rightCellQuadratureDefect ℓ_F N` unconditionally absorbs
     both `-atomPairRe k_F` and all secular `1 / √x` drift, leaving only `θ * trapezoidalNumeratorCellDefect F N`.
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

/-! ## Section 1: Left-Endpoint and Trapezoidal Secular Drift Identities on `[n - 1, n]` and `trapezoidalNumeratorCellDefect` -/

/-- The **Left-Endpoint Pure Numerator Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n ((weilSymmetricLogNumerator f x - weilSymmetricLogNumerator f (n - 1)) / √x) dx`. -/
def leftNumeratorCellDefect (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∫ x in ((n : ℝ) - 1)..(n : ℝ),
      ((weilSymmetricLogNumerator f x - weilSymmetricLogNumerator f ((n : ℝ) - 1)) / Real.sqrt x)

/-- The **Trapezoidal Pure Numerator Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n ((weilSymmetricLogNumerator f x - (weilSymmetricLogNumerator f (n - 1) + weilSymmetricLogNumerator f n) / 2) / √x) dx`. -/
def trapezoidalNumeratorCellDefect (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∫ x in ((n : ℝ) - 1)..(n : ℝ),
      ((weilSymmetricLogNumerator f x -
          (weilSymmetricLogNumerator f ((n : ℝ) - 1) + weilSymmetricLogNumerator f (n : ℝ)) / 2) /
        Real.sqrt x)

/-- **Exact Left-Endpoint Square-Root Algebraic Identity for `1 ≤ n`**:
`2 * Real.sqrt ((n : ℝ) - 1) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) - 1 = -(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2`. -/
theorem two_mul_sqrt_pred_mul_sqrt_sub_sub_one_eq_neg_sq {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.sqrt ((n : ℝ) - 1) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) - 1 =
      -(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hsq_n : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsq_n1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1
  linear_combination hsq_n - hsq_n1

/-- **Exact Unit-Cell Left-Endpoint Secular Drift Integral Identity**:
for any `f : ℝ → ℂ` and `2 ≤ n`,
`∫ x in ((n : ℝ) - 1)..(n : ℝ), (weilSymmetricLogNumerator f ((n : ℝ) - 1) / Real.sqrt x - logValue f (n - 1)) = -(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f (n - 1)`. -/
theorem intervalIntegral_const_pred_div_sqrt_sub_logValue_eq (f : ℝ → ℂ) {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (weilSymmetricLogNumerator f ((n : ℝ) - 1) / Real.sqrt x - logValue f (n - 1))) =
      -(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f (n - 1) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hpred1 : 1 ≤ n - 1 := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hint_inv : IntervalIntegrable (fun x : ℝ => (Real.sqrt x)⁻¹) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hint_div : IntervalIntegrable
      (fun x : ℝ => weilSymmetricLogNumerator f ((n : ℝ) - 1) * (Real.sqrt x)⁻¹)
      volume ((n : ℝ) - 1) (n : ℝ) :=
    hint_inv.const_mul (weilSymmetricLogNumerator f ((n : ℝ) - 1))
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_sub hint_div intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral_inv_sqrt_cell hn,
    intervalIntegral.integral_const, sub_sub_cancel, one_smul, ← hcast,
    weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue f hpred1, hcast]
  have hsq := two_mul_sqrt_pred_mul_sqrt_sub_sub_one_eq_neg_sq hn1
  linear_combination (logValue f (n - 1)) * hsq

/-- **Exact Unit-Cell Trapezoidal Secular Drift Integral Identity**:
for any `f : ℝ → ℂ` and `2 ≤ n`,
`∫ x in ((n : ℝ) - 1)..(n : ℝ), (((weilSymmetricLogNumerator f ((n : ℝ) - 1) + weilSymmetricLogNumerator f (n : ℝ)) / 2) / Real.sqrt x - (logValue f (n - 1) + logValue f n) / 2) = (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (logValue f n - logValue f (n - 1))`. -/
theorem intervalIntegral_trapezoidal_secular_drift_eq (f : ℝ → ℂ) {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (((weilSymmetricLogNumerator f ((n : ℝ) - 1) + weilSymmetricLogNumerator f (n : ℝ)) / 2) /
          Real.sqrt x - (logValue f (n - 1) + logValue f n) / 2)) =
      (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 *
        (logValue f n - logValue f (n - 1)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
    refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hI_right : IntervalIntegrable
      (fun x : ℝ => weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt x - logValue f n)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    simp_rw [div_eq_mul_inv]
    exact ((continuousOn_const.mul hinv).sub continuousOn_const).intervalIntegrable
  have hI_left : IntervalIntegrable
      (fun x : ℝ => weilSymmetricLogNumerator f ((n : ℝ) - 1) / Real.sqrt x - logValue f (n - 1))
      volume ((n : ℝ) - 1) (n : ℝ) := by
    simp_rw [div_eq_mul_inv]
    exact ((continuousOn_const.mul hinv).sub continuousOn_const).intervalIntegrable
  have hcongr : (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (((weilSymmetricLogNumerator f ((n : ℝ) - 1) + weilSymmetricLogNumerator f (n : ℝ)) / 2) /
          Real.sqrt x - (logValue f (n - 1) + logValue f n) / 2)) =
      ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        ((1 / 2) * (weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt x - logValue f n) +
          (1 / 2) * (weilSymmetricLogNumerator f ((n : ℝ) - 1) / Real.sqrt x - logValue f (n - 1))) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [hcongr, intervalIntegral.integral_add (hI_right.const_mul (1 / 2)) (hI_left.const_mul (1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral_const_div_sqrt_sub_logValue_eq f hn,
    intervalIntegral_const_pred_div_sqrt_sub_logValue_eq f hn]
  ring

/-- **Exact Trapezoidal Secular-Plus-Numerator Decomposition of `trueTrapezoidalCellDefect`**:
for every `f : WeilTestFn` and `N : ℕ`,
`trueTrapezoidalCellDefect (weilContinuumLogProfile f.1) N = (∑ n ∈ Finset.Icc 2 N, (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (logValue f.1 n - logValue f.1 (n - 1))) + trapezoidalNumeratorCellDefect f.1 N`. -/
theorem trueTrapezoidalCellDefect_weilContinuumLogProfile_eq_secular_diff_add_trapezoidalNumerator
    (f : WeilTestFn) (N : ℕ) :
    trueTrapezoidalCellDefect (weilContinuumLogProfile f.1) N =
      (∑ n ∈ Finset.Icc 2 N,
        (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 *
          (logValue f.1 n - logValue f.1 (n - 1))) +
        trapezoidalNumeratorCellDefect f.1 N := by
  rw [trueTrapezoidalCellDefect_eq_sum_Icc, trapezoidalNumeratorCellDefect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hn1 : 1 ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  rw [← intervalIntegral_trapezoidal_secular_drift_eq f.1 hn.1]
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
    refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hI1 : IntervalIntegrable
      (fun x : ℝ =>
        ((weilSymmetricLogNumerator f.1 ((n : ℝ) - 1) + weilSymmetricLogNumerator f.1 (n : ℝ)) / 2) /
          Real.sqrt x - (logValue f.1 (n - 1) + logValue f.1 n) / 2)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    simp_rw [div_eq_mul_inv]
    exact ((continuousOn_const.mul hinv).sub continuousOn_const).intervalIntegrable
  have hI2 : IntervalIntegrable
      (fun x : ℝ =>
        (weilSymmetricLogNumerator f.1 x -
          (weilSymmetricLogNumerator f.1 ((n : ℝ) - 1) + weilSymmetricLogNumerator f.1 (n : ℝ)) / 2) /
          Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    have hnum : ContinuousOn (fun x : ℝ =>
        weilSymmetricLogNumerator f.1 x -
          (weilSymmetricLogNumerator f.1 ((n : ℝ) - 1) + weilSymmetricLogNumerator f.1 (n : ℝ)) / 2)
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ((continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_).sub continuousOn_const
      rw [uIcc_of_le (by linarith)] at hx
      rw [mem_Ici]
      linarith [hx.1]
    simp_rw [div_eq_mul_inv]
    exact (hnum.mul hinv).intervalIntegrable
  rw [← intervalIntegral.integral_add hI1 hI2]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← hcast, weilContinuumLogProfile_natCast_eq_logValue,
    weilContinuumLogProfile_natCast_eq_logValue, hcast,
    weilContinuumLogProfile_eq_weilSymmetricLogNumerator_div_sqrt]
  ring

/-! ## Section 2: Summation-by-Parts Extraction of the $n = 1$ Origin Term from the Trapezoidal Secular Drift and the Positive Telescoping Weight `trapezoidalSecularDiffWeight` -/

/-- **General Summation-by-Parts Identity on `Finset.Icc 2 N`**:
for any sequences `w v : ℕ → ℝ` and any `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, w n * (v n - v (n - 1)) = w (N + 1) * v N - w 2 * v 1 + ∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * v n`. -/
theorem sum_Icc_two_mul_sub_pred (w v : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, w n * (v n - v (n - 1))) =
      w (N + 1) * v N - w 2 * v 1 +
        ∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * v n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have h2 : 2 ≤ 1 + k + 1 := by omega
    have hpred : 1 + k + 1 - 1 = 1 + k := by omega
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, Finset.sum_Icc_succ_top h2,
      Finset.sum_Icc_succ_top h2, ih hk1, hpred]
    ring

/-- **Telescoping Sum of Forward Differences on `Finset.Icc 2 N`**:
for any sequence `w : ℕ → ℝ` and `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) = w 2 - w (N + 1)`. -/
theorem sum_Icc_two_sub_succ_nat (w : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1))) = w 2 - w (N + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero => simp
  | succ k ih =>
    have hk1 : 1 ≤ 1 + k := by omega
    have h2 : 2 ≤ 1 + k + 1 := by omega
    rw [show 1 + (k + 1) = 1 + k + 1 by omega, Finset.sum_Icc_succ_top h2, ih hk1]
    ring

/-- The **Trapezoidal Secular Second-Difference Counterterm Weight**:
`trapezoidalSecularDiffWeight n = ((√n - √(n - 1)) ^ 2 - (√(n + 1) - √n) ^ 2) / 2` for `n ≥ 2`,
and `0` for `n < 2`. -/
def trapezoidalSecularDiffWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then
    ((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
      (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2) / 2
  else 0

/-- For every `n ≥ 1`, `Real.sqrt ((n : ℝ) + 1) - Real.sqrt n ≤ Real.sqrt n - Real.sqrt ((n : ℝ) - 1)`. -/
theorem sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) - Real.sqrt n ≤ Real.sqrt n - Real.sqrt ((n : ℝ) - 1) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hn_succ : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) * (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
    have hsq1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt hn_succ
    have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
    linear_combination hsq1 - hsq0
  have h2 : (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
    have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
    have hsq_1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1
    linear_combination hsq0 - hsq_1
  have hsum_le : Real.sqrt n + Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt ((n : ℝ) + 1) + Real.sqrt n := by
    linarith [Real.sqrt_le_sqrt (by linarith : (n : ℝ) - 1 ≤ (n : ℝ) + 1)]
  have hdiff_nonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hpos : 0 < Real.sqrt n + Real.sqrt ((n : ℝ) - 1) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by exact_mod_cast hn)) (Real.sqrt_nonneg _)
  nlinarith

/-- For every `n : ℕ`, `0 ≤ trapezoidalSecularDiffWeight n`. -/
theorem trapezoidalSecularDiffWeight_nonneg (n : ℕ) :
    0 ≤ trapezoidalSecularDiffWeight n := by
  unfold trapezoidalSecularDiffWeight
  split_ifs with hn
  · have hle := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred (by omega : 1 ≤ n)
    have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hsq : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2 ≤
        (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 :=
      pow_le_pow_left₀ hnonneg hle 2
    linarith
  · exact le_rfl

/-- Finite-cutoff formula for `primeBlindCounterterm trapezoidalSecularDiffWeight f`: -/
theorem primeBlindCounterterm_trapezoidalSecularDiffWeight_eq_sum_Icc (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm trapezoidalSecularDiffWeight f =
      ∑ n ∈ Finset.Icc 2 N,
        (((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
            (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2) / 2) *
          logValue f.1 n := by
  rw [primeBlindCounterterm_eq_sum_Icc trapezoidalSecularDiffWeight f hN]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  simp [trapezoidalSecularDiffWeight, hn.1]

/-- **Summation-by-Parts Identity for the Trapezoidal Secular Drift**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`∑ n ∈ Finset.Icc 2 N, (1 / 2) * (√n - √(n - 1)) ^ 2 * (logValue f.1 n - logValue f.1 (n - 1)) = -(√2 - 1) ^ 2 * (∫ u, ‖f.1 u‖ ^ 2) + primeBlindCounterterm trapezoidalSecularDiffWeight f`. -/
theorem sum_trapezoidal_secular_drift_eq_origin_add_counterterm (f : WeilTestFn) {N : ℕ}
    (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (∑ n ∈ Finset.Icc 2 N,
        (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 *
          (logValue f.1 n - logValue f.1 (n - 1))) =
      -(Real.sqrt 2 - 1) ^ 2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        primeBlindCounterterm trapezoidalSecularDiffWeight f := by
  let w : ℕ → ℝ := fun n => (1 / 2) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2
  have hsbp := sum_Icc_two_mul_sub_pred w (logValue f.1) hN1
  have hlogN : logValue f.1 N = 0 := by
    simp [logValue, hN0.1, hN0.2]
  have hw2 : w 2 = (1 / 2) * (Real.sqrt 2 - 1) ^ 2 := by
    dsimp [w]
    norm_num
  have hsum_eq : (∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * logValue f.1 n) =
      primeBlindCounterterm trapezoidalSecularDiffWeight f := by
    rw [primeBlindCounterterm_trapezoidalSecularDiffWeight_eq_sum_Icc f hN]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [w]
    push_cast
    rw [add_sub_cancel_right]
    ring
  change (∑ n ∈ Finset.Icc 2 N, w n * (logValue f.1 n - logValue f.1 (n - 1))) = _
  rw [hsbp, hlogN, mul_zero, zero_sub, hw2, logValue_one_eq_two_mul_integral_norm_sq, hsum_eq]
  ring

/-- **Exact Decomposition of `rightCellQuadratureDefect` into `2(√2 - 1) ∫ ‖f.1‖²` +
`primeBlindCounterterm trapezoidalSecularDiffWeight` + `trapezoidalNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = 2 * (Real.sqrt 2 - 1) * (∫ u, ‖f.1 u‖ ^ 2) + primeBlindCounterterm trapezoidalSecularDiffWeight f + trapezoidalNumeratorCellDefect f.1 N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_two_sqrt_two_sub_two_add_counterterm_add_trapezoidalNumerator
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      2 * (Real.sqrt 2 - 1) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        primeBlindCounterterm trapezoidalSecularDiffWeight f +
        trapezoidalNumeratorCellDefect f.1 N := by
  rw [rightCellQuadratureDefect_weilContinuumLogProfile_eq_trueTrapezoidal f hN1 hN0,
    trueTrapezoidalCellDefect_weilContinuumLogProfile_eq_secular_diff_add_trapezoidalNumerator,
    sum_trapezoidal_secular_drift_eq_origin_add_counterterm f hN1 hN0 hN]
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination -(∫ u : ℝ, ‖f.1 u‖ ^ 2) * hsq2

/-! ## Section 3: Unconditional `√2 / 2 > 7 / 10` Positive $L^2$ Surplus in `rightCellQuadratureDefect` and Pure Trapezoidal Numerator Coercivity -/

/-- **Exact Telescoping Sum of `trapezoidalSecularDiffWeight` on `Finset.Icc 2 N`**:
for every `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, trapezoidalSecularDiffWeight n = ((Real.sqrt 2 - 1) ^ 2 - (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 2) / 2 ≤ (Real.sqrt 2 - 1) ^ 2 / 2`. -/
theorem sum_Icc_trapezoidalSecularDiffWeight_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, trapezoidalSecularDiffWeight n) ≤
      (Real.sqrt 2 - 1) ^ 2 / 2 := by
  let w : ℕ → ℝ := fun n => (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 / 2
  have hcongr : (∑ n ∈ Finset.Icc 2 N, trapezoidalSecularDiffWeight n) =
      ∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    simp only [trapezoidalSecularDiffWeight, if_pos hn.1, w]
    push_cast
    rw [add_sub_cancel_right]
    ring
  rw [hcongr, sum_Icc_two_sub_succ_nat w hN]
  have hw2 : w 2 = (Real.sqrt 2 - 1) ^ 2 / 2 := by
    dsimp [w]
    norm_num
  have hwN : 0 ≤ w (N + 1) := by
    dsimp [w]
    positivity
  linarith

/-- For every `f : WeilTestFn` and `n ≥ 2`, `|logValue f.1 n| ≤ Real.sqrt 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_logValue_le_sqrt_two_mul_integral_norm_sq_of_two_le (f : WeilTestFn) {n : ℕ}
    (hn : 2 ≤ n) :
    |logValue f.1 n| ≤ Real.sqrt 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have h1 := abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f (by omega : 1 ≤ n)
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdiv : 2 / Real.sqrt n ≤ Real.sqrt 2 := by
    rw [div_le_iff₀ ( lt_of_lt_of_le hsqrt2_pos hsqrt_le )]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_right hdiv hnorm_nonneg)

/-- **Unconditional Uniform Bound on `primeBlindCounterterm trapezoidalSecularDiffWeight f`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`|primeBlindCounterterm trapezoidalSecularDiffWeight f| ≤ ((3 * Real.sqrt 2 - 4) / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_trapezoidalSecularDiffWeight_le (f : WeilTestFn) {N : ℕ}
    (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm trapezoidalSecularDiffWeight f| ≤
      ((3 * Real.sqrt 2 - 4) / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [primeBlindCounterterm_eq_sum_Icc trapezoidalSecularDiffWeight f hN]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      |trapezoidalSecularDiffWeight n * logValue f.1 n| ≤
        (trapezoidalSecularDiffWeight n * Real.sqrt 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [abs_mul, abs_of_nonneg (trapezoidalSecularDiffWeight_nonneg n), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_logValue_le_sqrt_two_mul_integral_norm_sq_of_two_le f hn.1)
      (trapezoidalSecularDiffWeight_nonneg n)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum := sum_Icc_trapezoidalSecularDiffWeight_le hN1
  have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsum hsqrt2_nonneg) hnorm_nonneg
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have halg : (Real.sqrt 2 - 1) ^ 2 / 2 * Real.sqrt 2 = (3 * Real.sqrt 2 - 4) / 2 := by
    linear_combination (Real.sqrt 2 / 2 - 1) * hsq2
  rwa [halg] at hmul

/-- Rational lower bound `7 / 10 ≤ Real.sqrt 2 / 2`. -/
theorem seven_tenths_le_sqrt_two_div_two :
    (7 / 10 : ℝ) ≤ Real.sqrt 2 / 2 := by
  have h : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 7 / 5)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Unconditional `√2 / 2` Positive $L^2$ Surplus in `rightCellQuadratureDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`2 * (√2 - 1) - (3 * √2 - 4) / 2 = √2 / 2`, so
`(Real.sqrt 2 / 2) * (∫ u, ‖f.1 u‖ ^ 2) + trapezoidalNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem sqrt_two_div_two_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (Real.sqrt 2 / 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        trapezoidalNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_two_sqrt_two_sub_two_add_counterterm_add_trapezoidalNumerator
      f hN1 hN0 hN
  have habs := (abs_le.mp (abs_primeBlindCounterterm_trapezoidalSecularDiffWeight_le f hN1 hN)).1
  linarith

/-- **Unconditional `7 / 10` Positive $L^2$ Surplus in `rightCellQuadratureDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(7 / 10) * (∫ u, ‖f.1 u‖ ^ 2) + trapezoidalNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem seven_tenths_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (7 / 10) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + trapezoidalNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := sqrt_two_div_two_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_right seven_tenths_le_sqrt_two_div_two hnorm_nonneg
  linarith

/-- **`atomPairRe`-Free and Secular-Drift-Free Coercive Lower Bound on `markovEnergy` in Terms of
`trapezoidalNumeratorCellDefect` (Primitive Hyperplane)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, if `θ ≥ max (20 / 7) (Real.log N)`
and `0 ≤ iteratedForwardDiff m (logValue F) n` on `[2, N]`, then `(7 / 10) * θ ≥ 2`, so both
`-atomPairRe k_F` and all secular `1 / √x` drift are unconditionally absorbed by the $n = 1$
origin surplus:
`(1 / 100 + (7 / 10) * θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * trapezoidalNumeratorCellDefect F N ≤ markovEnergy F`. -/
theorem trapezoidalNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero (m : ℕ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N) (hθlog : Real.log (N : ℝ) ≤ θ)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n) :
    (1 / 100 + (7 / 10) * θ - 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        (θ - 1) * bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * θ * sinhHalfMoment f ^ 2 +
        θ * trapezoidalNumeratorCellDefect (realWeilTestFn f hf hfc).1 N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have hquad := seven_tenths_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have hθquad := mul_le_mul_of_nonneg_left hquad hθ0
  linarith

end RHTower

end
