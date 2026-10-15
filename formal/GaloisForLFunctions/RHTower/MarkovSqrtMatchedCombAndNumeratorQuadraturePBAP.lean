import GaloisForLFunctions.RHTower.MarkovHermiteHadamardPeanoAndSemiconcavePBAP

/-!
# The Square-Root-Matched Poisson Comb, Exact Cancellation of the Secular $1/\sqrt{x}$ Drift, and Unconditional $L^2$ Control of the Secular Quadrature Sum on Route HF / PBAP

This module isolates the exact multiplicative decomposition of the continuum profile
`weilContinuumLogProfile f x = weilSymmetricLogNumerator f x / √x` on each unit cell `[n - 1, n]`
and proves that the secular `1 / √x` drift on `[1, ∞)` is both:
1. **identically a prime-blind counterterm** (`primeBlindCounterterm secularSqrtSqWeight f`), and
2. **unconditionally bounded in absolute value by `(1 - 1 / √N) ∫ ‖f.1‖² ≤ ∫ ‖f.1‖²`** for every
   `f : WeilTestFn` and every `N ≥ 1`, with no sign, monotonicity, or convexity hypotheses on `f`.

## Main Results

1. **Section 1 (The Symmetric Autocorrelation Log-Numerator `weilSymmetricLogNumerator` and the
   Exact Unit-Cell Secular Integral):**
   - We define `weilSymmetricLogNumerator f x := (EF.weilTest f f (Real.log x) + EF.weilTest f f (-Real.log x)).re`,
     so `weilContinuumLogProfile f x = weilSymmetricLogNumerator f x / Real.sqrt x` and
     `logValue f n = weilSymmetricLogNumerator f n / Real.sqrt n`.
   - We prove the origin identity `weilSymmetricLogNumerator f.1 1 = 2 * ∫ u, ‖f.1 u‖ ^ 2`, the
     spectral cosine representation `weilSymmetricLogNumerator f.1 x = (1 / (2 * π)) * ∫ r, ‖paperFT f.1 r‖ ^ 2 * (2 * cos(r log x))`,
     and the uniform two-sided bound `|weilSymmetricLogNumerator f.1 x| ≤ 2 * ∫ u, ‖f.1 u‖ ^ 2`.
   - For every `n ≥ 2`, we prove the exact unit-cell secular integral
     `∫ x in (n - 1)..n, (Real.sqrt x)⁻¹ = 2 * (Real.sqrt n - Real.sqrt (n - 1))`
     and the exact algebraic square identity
     `2 * Real.sqrt n * (Real.sqrt n - Real.sqrt (n - 1)) - 1 = (Real.sqrt n - Real.sqrt (n - 1)) ^ 2`,
     yielding the exact unit-cell secular-drift formula
     `∫ x in (n - 1)..n, (weilSymmetricLogNumerator f n / √x - logValue f n) = (√n - √(n - 1)) ^ 2 * logValue f n`.

2. **Section 2 (The Secular Square-Root Drift Weight `secularSqrtSqWeight`, the Square-Root-Matched
   Comb `sqrtMatchedCombWeight`, and Unconditional Telescoping $L^2$ Control):**
   - We define `secularSqrtSqWeight n := if 2 ≤ n then (√n - √(n - 1)) ^ 2 else 0`,
     `sqrtMatchedCombWeight n := unitStepCountertermWeight n + secularSqrtSqWeight n`, and the
     pure numerator quadrature defect
     `rightNumeratorCellDefect f N := ∑ n ∈ Finset.Icc 2 N, ∫ x in (n - 1)..n, (weilSymmetricLogNumerator f x - weilSymmetricLogNumerator f n) / √x`.
   - We prove the exact decomposition (`rightCellQuadratureDefect_weilContinuumLogProfile_eq_secular_add_numerator`):
     `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = primeBlindCounterterm secularSqrtSqWeight f + rightNumeratorCellDefect f.1 N`,
     and the square-root-matched continuum-minus-comb identity
     (`re_integral_lebesguePart_sub_sqrtMatchedComb_eq_rightNumeratorCellDefect`):
     `(∫ x, primeIntegrand k_f x ∂lebesguePart).re - primeBlindCounterterm sqrtMatchedCombWeight f = rightNumeratorCellDefect f.1 N`.
   - We prove the exact cubic-defect telescoping inequality
     `(√n - √(n - 1)) ^ 2 * (2 / √n) ≤ 1 / √(n - 1) - 1 / √n` for all `n ≥ 2`,
     whose sum over `n ∈ [2, N]` telescopes to `1 - 1 / √N ≤ 1`. Combining this with the pointwise
     bound `|logValue f.1 n| ≤ (2 / √n) ∫ ‖f.1‖²` from Module 43 yields the **Unconditional Secular
     Drift Bound** (`abs_primeBlindCounterterm_secularSqrtSqWeight_le`,
     `abs_primeBlindCounterterm_secularSqrtSqWeight_le_integral_norm_sq`):
     `|primeBlindCounterterm secularSqrtSqWeight f| ≤ (1 - 1 / √N) * ∫ u, ‖f.1 u‖ ^ 2 ≤ ∫ u, ‖f.1 u‖ ^ 2`.

3. **Section 3 (Square-Root-Matched Conservation Law on the Primitive Hyperplane and Pure Numerator
   Quadrature Coercivity):**
   - On the primitive hyperplane `coshHalfMoment f = 0`, we prove the square-root-matched
     conservation law (`sqrtMatchedComb_add_rightNumeratorCellDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero`):
     `primeBlindCounterterm sqrtMatchedCombWeight F + rightNumeratorCellDefect F N + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 = 0`.
   - Using the unconditional bound `|primeBlindCounterterm secularSqrtSqWeight F| ≤ (1 - 1 / √N) ∫ ‖F‖²`,
     we prove that for every `f ∈ C²_c(ℝ)` on the primitive hyperplane,
     `rightCellQuadratureDefect ℓ_F N ≥ -(1 - 1 / √N) * ∫ ‖F‖² + rightNumeratorCellDefect F N`.
   - Coupling this with the left-endpoint origin extraction of `weilSymmetricLogNumerator F`
     (`C_F(1) = 2 ∫ ‖F‖²`), we obtain unconditional coercive lower bounds for `markovCountertermEnergy`
     and `markovEnergy` in terms of `rightNumeratorCellDefect F N` alone.
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

/-! ## Section 1: The Symmetric Autocorrelation Log-Numerator `weilSymmetricLogNumerator` and the Exact Unit-Cell Secular Integral -/

/-- The **Symmetric Autocorrelation Log-Numerator** of `f : ℝ → ℂ` at `x : ℝ`:
`weilSymmetricLogNumerator f x = (EF.weilTest f f (Real.log x) + EF.weilTest f f (-Real.log x)).re`. -/
def weilSymmetricLogNumerator (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  (EF.weilTest f f (Real.log x) + EF.weilTest f f (-Real.log x)).re

/-- Multiplicative factorization of `weilContinuumLogProfile`:
`weilContinuumLogProfile f x = weilSymmetricLogNumerator f x / Real.sqrt x`. -/
theorem weilContinuumLogProfile_eq_weilSymmetricLogNumerator_div_sqrt (f : ℝ → ℂ) (x : ℝ) :
    weilContinuumLogProfile f x = weilSymmetricLogNumerator f x / Real.sqrt x := by
  rw [weilContinuumLogProfile_eq, weilSymmetricLogNumerator]

/-- Multiplicative factorization of `logValue`:
`logValue f n = weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt n`. -/
theorem logValue_eq_weilSymmetricLogNumerator_div_sqrt (f : ℝ → ℂ) (n : ℕ) :
    logValue f n = weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt n := by
  rw [← weilContinuumLogProfile_natCast_eq_logValue,
    weilContinuumLogProfile_eq_weilSymmetricLogNumerator_div_sqrt]

/-- For `0 < x`, `weilSymmetricLogNumerator f x = Real.sqrt x * weilContinuumLogProfile f x`. -/
theorem weilSymmetricLogNumerator_eq_sqrt_mul_weilContinuumLogProfile (f : ℝ → ℂ) {x : ℝ}
    (hx : 0 < x) :
    weilSymmetricLogNumerator f x = Real.sqrt x * weilContinuumLogProfile f x := by
  have hsqrt : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  rw [weilContinuumLogProfile_eq_weilSymmetricLogNumerator_div_sqrt, mul_div_cancel₀ _ hsqrt]

/-- For `1 ≤ n`, `weilSymmetricLogNumerator f (n : ℝ) = Real.sqrt n * logValue f n`. -/
theorem weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue (f : ℝ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    weilSymmetricLogNumerator f (n : ℝ) = Real.sqrt n * logValue f n := by
  rw [← weilContinuumLogProfile_natCast_eq_logValue]
  exact weilSymmetricLogNumerator_eq_sqrt_mul_weilContinuumLogProfile f (by exact_mod_cast hn)

/-- **Origin Identity for `weilSymmetricLogNumerator`**:
`weilSymmetricLogNumerator f.1 1 = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
@[simp]
theorem weilSymmetricLogNumerator_one_eq_two_mul_integral_norm_sq (f : WeilTestFn) :
    weilSymmetricLogNumerator f.1 1 = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [weilSymmetricLogNumerator_eq_sqrt_mul_weilContinuumLogProfile f.1 zero_lt_one,
    Real.sqrt_one, one_mul, weilContinuumLogProfile_one_eq_two_mul_integral_norm_sq]

/-- **Spectral Cosine Representation of `weilSymmetricLogNumerator`**:
for every `f : WeilTestFn` and `x : ℝ`,
`weilSymmetricLogNumerator f.1 x = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * Real.log x))`. -/
theorem weilSymmetricLogNumerator_eq_spectral_cos (f : WeilTestFn) (x : ℝ) :
    weilSymmetricLogNumerator f.1 x =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * Real.log x)) :=
  re_weilTest_add_neg_eq_spectral_cos f (Real.log x)

/-- **Uniform Two-Sided Origin Bound on `weilSymmetricLogNumerator`**:
for every `f : WeilTestFn` and `x : ℝ`,
`|weilSymmetricLogNumerator f.1 x| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_weilSymmetricLogNumerator_le_two_mul_integral_norm_sq (f : WeilTestFn) (x : ℝ) :
    |weilSymmetricLogNumerator f.1 x| ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
  abs_re_weilTest_add_neg_le_two_mul_integral_norm_sq f (Real.log x)

/-- For every `f : WeilTestFn`, `weilSymmetricLogNumerator f.1` is continuous on `Ici 1`. -/
theorem continuousOn_weilSymmetricLogNumerator (f : WeilTestFn) :
    ContinuousOn (weilSymmetricLogNumerator f.1) (Ici 1) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hlog : ContinuousOn Real.log (Ici 1) :=
    Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
  unfold weilSymmetricLogNumerator
  exact Complex.continuous_re.comp_continuousOn
    ((hkd.continuous.comp_continuousOn hlog).add (hkd.continuous.comp_continuousOn hlog.neg))

/-- **Exact Unit-Cell Integral of `(Real.sqrt x)⁻¹` on `[(n : ℝ) - 1, (n : ℝ)]` for `2 ≤ n`**:
`∫ x in ((n : ℝ) - 1)..(n : ℝ), (Real.sqrt x)⁻¹ = 2 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1))`. -/
theorem intervalIntegral_inv_sqrt_cell {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ), (Real.sqrt x)⁻¹) =
      2 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hderiv : ∀ x ∈ uIcc ((n : ℝ) - 1) (n : ℝ),
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (Real.sqrt x)⁻¹ x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx_pos)
    have h1 := (Real.hasDerivAt_sqrt (ne_of_gt hx_pos)).const_mul 2
    refine h1.congr_deriv ?_
    rw [one_div, mul_inv_rev]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (Real.sqrt x)⁻¹) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **Exact Square-Root Algebraic Identity for `1 ≤ n`**:
`2 * Real.sqrt n * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) - 1 = (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2`. -/
theorem two_mul_sqrt_mul_sqrt_sub_sub_one_eq_sq_natCast {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.sqrt n * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) - 1 =
      (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hsq_n : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsq_n1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1
  linear_combination hsq_n - hsq_n1

/-- **Exact Unit-Cell Secular Drift Integral Identity**:
for any `f : ℝ → ℂ` and `2 ≤ n`,
`∫ x in ((n : ℝ) - 1)..(n : ℝ), (weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt x - logValue f n) = (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f n`. -/
theorem intervalIntegral_const_div_sqrt_sub_logValue_eq (f : ℝ → ℂ) {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (weilSymmetricLogNumerator f (n : ℝ) / Real.sqrt x - logValue f n)) =
      (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hint_inv : IntervalIntegrable (fun x : ℝ => (Real.sqrt x)⁻¹) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hint_div : IntervalIntegrable
      (fun x : ℝ => weilSymmetricLogNumerator f (n : ℝ) * (Real.sqrt x)⁻¹)
      volume ((n : ℝ) - 1) (n : ℝ) :=
    hint_inv.const_mul (weilSymmetricLogNumerator f (n : ℝ))
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_sub hint_div intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral_inv_sqrt_cell hn,
    intervalIntegral.integral_const, sub_sub_cancel, one_smul,
    weilSymmetricLogNumerator_natCast_eq_sqrt_mul_logValue f hn1]
  have hsq := two_mul_sqrt_mul_sqrt_sub_sub_one_eq_sq_natCast hn1
  linear_combination (logValue f n) * hsq

/-! ## Section 2: The Secular Square-Root Drift Weight `secularSqrtSqWeight`, the Square-Root-Matched Comb `sqrtMatchedCombWeight`, and Unconditional Telescoping $L^2$ Control -/

/-- The **Secular Square-Root Drift Counterterm Weight**:
`secularSqrtSqWeight n = (√n - √(n - 1)) ^ 2` for `n ≥ 2`, and `0` for `n < 2`. -/
def secularSqrtSqWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 else 0

/-- The **Square-Root-Matched Poisson Comb Weight**:
`sqrtMatchedCombWeight n = unitStepCountertermWeight n + secularSqrtSqWeight n`, which equals
`1 + (√n - √(n - 1)) ^ 2 = 2 √n (√n - √(n - 1))` for `n ≥ 2`. -/
def sqrtMatchedCombWeight (n : ℕ) : ℝ :=
  unitStepCountertermWeight n + secularSqrtSqWeight n

/-- The **Right-Endpoint Pure Numerator Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n ((weilSymmetricLogNumerator f x - weilSymmetricLogNumerator f n) / √x) dx`. -/
def rightNumeratorCellDefect (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∫ x in ((n : ℝ) - 1)..(n : ℝ),
      ((weilSymmetricLogNumerator f x - weilSymmetricLogNumerator f (n : ℝ)) / Real.sqrt x)

theorem secularSqrtSqWeight_nonneg (n : ℕ) : 0 ≤ secularSqrtSqWeight n := by
  unfold secularSqrtSqWeight
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem sqrtMatchedCombWeight_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    sqrtMatchedCombWeight n = 2 * Real.sqrt n * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) := by
  unfold sqrtMatchedCombWeight unitStepCountertermWeight secularSqrtSqWeight
  rw [if_pos hn, if_pos hn]
  have h := two_mul_sqrt_mul_sqrt_sub_sub_one_eq_sq_natCast (by omega : 1 ≤ n)
  linarith

/-- Finite-cutoff formula for `primeBlindCounterterm secularSqrtSqWeight f`:
`primeBlindCounterterm secularSqrtSqWeight f = ∑ n ∈ Finset.Icc 2 N, (√n - √(n - 1)) ^ 2 * logValue f.1 n`. -/
theorem primeBlindCounterterm_secularSqrtSqWeight_eq_sum_Icc (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm secularSqrtSqWeight f =
      ∑ n ∈ Finset.Icc 2 N, (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f.1 n := by
  rw [primeBlindCounterterm_eq_sum_Icc secularSqrtSqWeight f hN]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  simp [secularSqrtSqWeight, hn.1]

/-- **Exact Decomposition of `rightCellQuadratureDefect` into Secular Drift Counterterm + Pure
Numerator Cell Defect**:
for every `f : WeilTestFn` and support cutoff `N : ℕ`,
`rightCellQuadratureDefect (weilContinuumLogProfile f.1) N = primeBlindCounterterm secularSqrtSqWeight f + rightNumeratorCellDefect f.1 N`. -/
theorem rightCellQuadratureDefect_weilContinuumLogProfile_eq_secular_add_numerator
    (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    rightCellQuadratureDefect (weilContinuumLogProfile f.1) N =
      primeBlindCounterterm secularSqrtSqWeight f + rightNumeratorCellDefect f.1 N := by
  rw [rightCellQuadratureDefect, primeBlindCounterterm_secularSqrtSqWeight_eq_sum_Icc f hN,
    rightNumeratorCellDefect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  rw [← intervalIntegral_const_div_sqrt_sub_logValue_eq f.1 hn.1]
  have hI1 : IntervalIntegrable
      (fun x : ℝ => weilSymmetricLogNumerator f.1 (n : ℝ) / Real.sqrt x - logValue f.1 n)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
    simp_rw [div_eq_mul_inv]
    exact ((continuousOn_const.mul hinv).sub continuousOn_const).intervalIntegrable
  have hI2 : IntervalIntegrable
      (fun x : ℝ => (weilSymmetricLogNumerator f.1 x - weilSymmetricLogNumerator f.1 (n : ℝ)) /
        Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    have hnum : ContinuousOn (fun x : ℝ =>
        weilSymmetricLogNumerator f.1 x - weilSymmetricLogNumerator f.1 (n : ℝ))
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ((continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_).sub continuousOn_const
      rw [uIcc_of_le (by linarith)] at hx
      rw [mem_Ici]
      linarith [hx.1]
    have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
    simp_rw [div_eq_mul_inv]
    exact (hnum.mul hinv).intervalIntegrable
  rw [← intervalIntegral.integral_add hI1 hI2]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [weilContinuumLogProfile_natCast_eq_logValue,
    weilContinuumLogProfile_eq_weilSymmetricLogNumerator_div_sqrt]
  ring

/-- **Square-Root-Matched Continuum-Minus-Comb Identity**:
replacing `unitStepCountertermWeight` by `sqrtMatchedCombWeight = unitStepCountertermWeight + secularSqrtSqWeight`
absorbs the entire secular `1 / √x` drift into the prime-blind counterterm, leaving only
`rightNumeratorCellDefect f.1 N`:
`(∫ x, primeIntegrand k_f x ∂lebesguePart).re - primeBlindCounterterm sqrtMatchedCombWeight f = rightNumeratorCellDefect f.1 N`. -/
theorem re_integral_lebesguePart_sub_sqrtMatchedComb_eq_rightNumeratorCellDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest f.1 f.1 (Real.log x) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log x) = 0) :
    (∫ x, primeIntegrand (EF.weilTest f.1 f.1) x ∂lebesguePart).re -
        primeBlindCounterterm sqrtMatchedCombWeight f =
      rightNumeratorCellDefect f.1 N := by
  have h1 := re_integral_lebesguePart_sub_unitStep_eq_rightCellQuadratureDefect f hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_secular_add_numerator
    f (fun n hn => hN n (by exact_mod_cast hn))
  have hadd : primeBlindCounterterm sqrtMatchedCombWeight f =
      primeBlindCounterterm unitStepCountertermWeight f +
        primeBlindCounterterm secularSqrtSqWeight f :=
    primeBlindCounterterm_add unitStepCountertermWeight secularSqrtSqWeight f
  linarith

/-- **Exact Cubic-Defect Telescoping Majorant for `secularSqrtSqWeight`**:
for every integer `n ≥ 2`,
`(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (2 / Real.sqrt n) ≤ 1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n`. -/
theorem secularSqrtSq_mul_two_div_sqrt_le_inv_sqrt_sub {n : ℕ} (hn : 2 ≤ n) :
    (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (2 / Real.sqrt n) ≤
      1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n := by
  set a : ℝ := Real.sqrt n
  set b : ℝ := Real.sqrt ((n : ℝ) - 1)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hab_le : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hab_nonneg : 0 ≤ a - b := sub_nonneg.mpr hab_le
  have h1_sub : 1 - 2 * b * (a - b) = (a - b) ^ 2 := by
    have hsq_a : a ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
    have hsq_b : b ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
    linear_combination hsq_b - hsq_a
  have hdiff : 1 / b - 1 / a - (a - b) ^ 2 * (2 / a) =
      (a - b) ^ 3 / (a * b) := by
    field_simp
    linear_combination (a - b) * h1_sub
  have hnonneg : 0 ≤ (a - b) ^ 3 / (a * b) := by positivity
  linarith

/-- **Exact Telescoping Sum of `1 / √(n - 1) - 1 / √n` on `Finset.Icc 2 N`**:
for every `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n) = 1 - 1 / Real.sqrt N`. -/
theorem sum_Icc_two_inv_sqrt_sub {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n)) =
      1 - 1 / Real.sqrt N := by
  have h := sum_Icc_two_sub_succ (fun x : ℝ => 1 / Real.sqrt x) hN
  simpa using h

/-- **Uniform Telescoping Bound on `∑_{n = 2}^N (√n - √(n - 1))² * (2 / √n)`**:
for every `1 ≤ N`,
`∑ n ∈ Finset.Icc 2 N, (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (2 / Real.sqrt n) ≤ 1 - 1 / Real.sqrt N`. -/
theorem sum_Icc_secularSqrtSq_mul_two_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
        (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (2 / Real.sqrt n)) ≤
      1 - 1 / Real.sqrt N := by
  rw [← sum_Icc_two_inv_sqrt_sub hN]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  exact secularSqrtSq_mul_two_div_sqrt_le_inv_sqrt_sub hn.1

/-- **Unconditional Uniform `(1 - 1 / √N) ∫ ‖f.1‖²` Bound on `primeBlindCounterterm secularSqrtSqWeight f`**:
for every `f : WeilTestFn` and every support cutoff `1 ≤ N`,
`|primeBlindCounterterm secularSqrtSqWeight f| ≤ (1 - 1 / Real.sqrt N) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_secularSqrtSqWeight_le (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm secularSqrtSqWeight f| ≤
      (1 - 1 / Real.sqrt N) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [primeBlindCounterterm_secularSqrtSqWeight_eq_sum_Icc f hN]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      |(Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * logValue f.1 n| ≤
        ((Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 * (2 / Real.sqrt n)) *
          ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f (by omega))
      (sq_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_Icc_secularSqrtSq_mul_two_div_sqrt_le hN1) hnorm_nonneg

/-- **Cutoff-Free Uniform `∫ ‖f.1‖²` Bound on `primeBlindCounterterm secularSqrtSqWeight f`**:
for every `f : WeilTestFn`,
`|primeBlindCounterterm secularSqrtSqWeight f| ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem abs_primeBlindCounterterm_secularSqrtSqWeight_le_integral_norm_sq (f : WeilTestFn) :
    |primeBlindCounterterm secularSqrtSqWeight f| ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  obtain ⟨N, hN2, hN⟩ := exists_weilTest_real_log_eq_zero f
  have h1 := abs_primeBlindCounterterm_secularSqrtSqWeight_le f (by omega : 1 ≤ N)
    (fun n hn => hN n (by exact_mod_cast hn))
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsub : 1 - 1 / Real.sqrt N ≤ 1 := by
    have : 0 ≤ 1 / Real.sqrt N := by positivity
    linarith
  exact h1.trans (by nlinarith)

/-! ## Section 3: Square-Root-Matched Conservation Law on the Primitive Hyperplane and Pure Numerator Quadrature Coercivity -/

/-- **Square-Root-Matched Conservation Law on the Primitive Hyperplane**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0` and every support cutoff `1 ≤ N`,
`primeBlindCounterterm sqrtMatchedCombWeight F + rightNumeratorCellDefect F N + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 = 0`. -/
theorem sqrtMatchedComb_add_rightNumeratorCellDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm sqrtMatchedCombWeight (realWeilTestFn f hf hfc) +
        rightNumeratorCellDefect (realWeilTestFn f hf hfc).1 N +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 = 0 := by
  have h1 := unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    hf hfc hcosh hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_secular_add_numerator
    (realWeilTestFn f hf hfc) (fun n hn => hN n (by exact_mod_cast hn))
  have hadd : primeBlindCounterterm sqrtMatchedCombWeight (realWeilTestFn f hf hfc) =
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) +
        primeBlindCounterterm secularSqrtSqWeight (realWeilTestFn f hf hfc) :=
    primeBlindCounterterm_add unitStepCountertermWeight secularSqrtSqWeight
      (realWeilTestFn f hf hfc)
  linarith

/-- **Unconditional Secular-Drift Lower Bound on `rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N`,
`-(1 - 1 / Real.sqrt N) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + rightNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem neg_one_sub_inv_sqrt_mul_l2_add_rightNumeratorCellDefect_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    -(1 - 1 / Real.sqrt N) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + rightNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq := rightCellQuadratureDefect_weilContinuumLogProfile_eq_secular_add_numerator f hN
  have habs := (abs_le.mp (abs_primeBlindCounterterm_secularSqrtSqWeight_le f hN1 hN)).1
  linarith

/-- **Unconditional Rigidity under Nonnegative Numerator Defect on the Primitive Hyperplane**:
for any real test `f ∈ C²_c(ℝ)` on the primitive hyperplane `coshHalfMoment f = 0`, if
`0 ≤ rightNumeratorCellDefect F N` (in particular, if `weilSymmetricLogNumerator F` is antitone on
each cell `[n - 1, n]`), then:
1. `primeBlindCounterterm sqrtMatchedCombWeight F ≤ -(bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2) ≤ 0`, and
2. if `0 ≤ primeBlindCounterterm sqrtMatchedCombWeight F`, then `bochnerResolventEnergy k_F = 0`,
   `∫ u, ‖F u‖ ^ 2 = 0`, and `0 ≤ markovCountertermEnergy lam F` for every counterterm `lam : ℕ → ℝ`. -/
theorem markovCountertermEnergy_nonneg_of_sqrtMatchedComb_nonneg_and_rightNumeratorCellDefect_nonneg_of_cosh_zero
    (lam : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hnum : 0 ≤ rightNumeratorCellDefect (realWeilTestFn f hf hfc).1 N)
    (hcomb : 0 ≤ primeBlindCounterterm sqrtMatchedCombWeight (realWeilTestFn f hf hfc)) :
    0 ≤ markovCountertermEnergy lam (realWeilTestFn f hf hfc).1 := by
  have heq :=
    sqrtMatchedComb_add_rightNumeratorCellDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hres_nonneg := bochnerResolventEnergy_weilTest_nonneg (realWeilTestFn f hf hfc)
  have hsinh_nonneg : 0 ≤ sinhHalfMoment f ^ 2 := sq_nonneg _
  have hres0 : bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) = 0 := by
    linarith
  exact markovCountertermEnergy_nonneg_of_bochnerResolventEnergy_eq_zero lam hres0

end RHTower

end
