import GaloisForLFunctions.RHTower.MarkovTrapezoidalSecularCancellationAndNumeratorPBAP

/-!
# Pure Secant Numerator Quadrature, the Exact Cubic Square-Root Slope Integral, and Summation-by-Parts Origin Peak Positivity

In Module 46, we proved the trapezoidal secular cancellation law
`(√2 / 2) * ∫ ‖f.1‖² + trapezoidalNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
where `trapezoidalNumeratorCellDefect f.1 N` integrates the midpoint-average remainder
`(C_f(x) - (C_f(n - 1) + C_f(n)) / 2) / √x` on each unit cell `[n - 1, n]` (`C_f = weilSymmetricLogNumerator f.1`).

In this module, we upgrade the midpoint average `(C_f(n - 1) + C_f(n)) / 2` inside the numerator to
the **Full Second-Order Linear Secant Interpolant**
`cellSecant C_f n x = ((n : ℝ) - x) * C_f(n - 1) + (x - ((n : ℝ) - 1)) * C_f(n)`:

1. **Section 1 (The Pure Secant Numerator Defect `secantNumeratorCellDefect` and the Exact Cubic
   Square-Root Slope Integral `-(1 / 3) * (√n - √(n - 1)) ^ 3`):**
   - On each cell `[n - 1, n]`, the midpoint difference decomposes into the linear slope term plus
     the second-order secant remainder (`sub_midpoint_eq_slope_add_sub_cellSecant`):
     `g x - (g (n - 1) + g n) / 2 = (x - n + 1 / 2) * (g n - g (n - 1)) + (g x - cellSecant g n x)`.
   - Integrating the linear slope weight `(x - n + 1 / 2) / √x` over `[n - 1, n]` (`n ≥ 2`) yields
     the **Exact Cubic Square-Root Identity** (`intervalIntegral_linear_offset_div_sqrt_cell`):
     `∫ x in (n - 1)..n, ((x - n + 1 / 2) / √x) = -(1 / 3) * (√n - √(n - 1)) ^ 3`.
   - Crucially, this integral is **negative** on every cell because `1 / √x` is strictly decreasing,
     putting more weight on the left half `[n - 1, n - 1/2]` where `x - n + 1/2 < 0`.

2. **Section 2 (The Autocorrelation Origin Peak Summation-by-Parts Positivity Principle and
   `secantNumeratorCellDefect f.1 N ≤ trapezoidalNumeratorCellDefect f.1 N`):**
   - Because `C_f(x) = weilSymmetricLogNumerator f.1 x` achieves its global maximum at the origin
     `x = 1` (`C_f(n) ≤ |C_f(n)| ≤ 2 ∫ ‖f.1‖² = C_f(1)`), summation by parts against ANY nonnegative
     antitone weight sequence `w(n)` on `[2, N]` with `C_f(N) = 0` yields a **Nonnegative Sum**
     (`two_mul_tail_l2_le_neg_sum_Icc_two_mul_weilSymmetricLogNumerator_sub_pred`):
     `2 * w (N + 1) * ∫ ‖f.1‖² ≤ ∑ n ∈ Finset.Icc 2 N, -w n * (C_f(n) - C_f(n - 1))`.
   - Applying this principle to `w(n) = (1 / 3) * (√n - √(n - 1)) ^ 3` proves that the linear slope
     contribution to `trapezoidalNumeratorCellDefect f.1 N` is **unconditionally nonnegative**:
     `secantNumeratorCellDefect f.1 N + (2 / 3) * (√(N + 1) - √N) ^ 3 * ∫ ‖f.1‖² ≤ trapezoidalNumeratorCellDefect f.1 N`,
     and in particular `secantNumeratorCellDefect f.1 N ≤ trapezoidalNumeratorCellDefect f.1 N`!

3. **Section 3 (Unconditional `√2 / 2 > 7 / 10` Positive $L^2$ Surplus over `secantNumeratorCellDefect`
   and `1 / √(n - 1)`-Weighted Peano Semiconcavity Bounds on `weilSymmetricLogNumerator`):**
   - Combining Section 2 with Module 46 upgrades the `√2 / 2 > 7 / 10` positive $L^2$ surplus directly
     to the pure second-order secant remainder `secantNumeratorCellDefect f.1 N` with **zero loss**:
     `(√2 / 2) * ∫ ‖f.1‖² + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.
   - Because `1 / √x` is outside the secant and bounded above by `1 / √(n - 1)` on `[n - 1, n]`,
     cellwise `K_n`-semiconcavity of the pure numerator `C_f` gains an extra `1 / √(n - 1)` decay
     factor (`neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave`):
     `-(∑ n ∈ Finset.Icc 2 N, K n / (12 * √(n - 1))) ≤ secantNumeratorCellDefect f.1 N`.
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

/-! ## Section 1: The Pure Secant Numerator Defect `secantNumeratorCellDefect` and the Exact Cubic Square-Root Slope Integral `-(1 / 3) * (√n - √(n - 1)) ^ 3` -/

/-- The **Pure Secant Numerator Cell Quadrature Defect** on `(1, N]`:
`∑_{n = 2}^N ∫_{n - 1}^n ((weilSymmetricLogNumerator f x - cellSecant (weilSymmetricLogNumerator f) n x) / √x) dx`. -/
def secantNumeratorCellDefect (f : ℝ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    ∫ x in ((n : ℝ) - 1)..(n : ℝ),
      ((weilSymmetricLogNumerator f x -
          cellSecant (weilSymmetricLogNumerator f) n x) /
        Real.sqrt x)

/-- Pointwise decomposition of the midpoint-average difference into the linear slope term plus the
secant remainder:
`g x - (g (n - 1) + g n) / 2 = (x - n + 1 / 2) * (g n - g (n - 1)) + (g x - cellSecant g n x)`. -/
theorem sub_midpoint_eq_slope_add_sub_cellSecant (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    g x - (g ((n : ℝ) - 1) + g (n : ℝ)) / 2 =
      (x - (n : ℝ) + 1 / 2) * (g (n : ℝ) - g ((n : ℝ) - 1)) +
        (g x - cellSecant g n x) := by
  unfold cellSecant
  ring

/-- Derivative of `t ↦ (2 / 3) * t * √t` for `0 < x`:
`HasDerivAt (fun t : ℝ => (2 / 3) * t * Real.sqrt t) (Real.sqrt x) x`. -/
theorem hasDerivAt_two_thirds_mul_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (2 / 3) * t * Real.sqrt t) (Real.sqrt x) x := by
  have h1 : HasDerivAt (fun t : ℝ => (2 / 3) * t) ((2 / 3) * 1) x :=
    (hasDerivAt_id x).const_mul (2 / 3)
  have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hmul := h1.mul h2
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
  have hne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have heq : (2 / 3 * 1) * Real.sqrt x + (2 / 3 * x) * (1 / (2 * Real.sqrt x)) = Real.sqrt x := by
    have hcancel : 1 / (2 * Real.sqrt x) * Real.sqrt x = 1 / 2 := by
      rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hne, mul_one, one_div]
    apply mul_right_cancel₀ hne
    rw [add_mul, mul_assoc (2 / 3 * x), hcancel]
    linear_combination -(1 / 3 : ℝ) * hsq
  rwa [heq] at hmul

/-- Exact evaluation of `∫_{n - 1}^n √x dx` for `n ≥ 2`:
`∫ x in ((n : ℝ) - 1)..(n : ℝ), Real.sqrt x = (2 / 3) * (n : ℝ) * Real.sqrt n - (2 / 3) * ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)`. -/
theorem intervalIntegral_sqrt_cell {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ), Real.sqrt x) =
      (2 / 3) * (n : ℝ) * Real.sqrt n -
        (2 / 3) * ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => (2 / 3) * x * Real.sqrt x)
    (f' := fun x : ℝ => Real.sqrt x)
    (fun x hx => ?_)
    (Real.continuous_sqrt.intervalIntegrable _ _)
  rw [uIcc_of_le (by linarith)] at hx
  exact hasDerivAt_two_thirds_mul_sqrt (by linarith [hx.1])

/-- **Exact Cubic Square-Root Algebraic Identity for `1 ≤ n`**:
`((2 / 3) * n * √n - (2 / 3) * (n - 1) * √(n - 1)) - (n - 1 / 2) * (2 * (√n - √(n - 1))) = -(1 / 3) * (√n - √(n - 1)) ^ 3`. -/
theorem two_thirds_sub_linear_mul_sqrt_sub_eq_neg_third_cube {n : ℕ} (hn : 1 ≤ n) :
    ((2 / 3) * (n : ℝ) * Real.sqrt n -
        (2 / 3) * ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1)) -
      ((n : ℝ) - 1 / 2) * (2 * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1))) =
    -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hn)
  have hsq_n : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsq_n1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hn1
  linear_combination
    ((1 / 3) * Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) * hsq_n +
    (Real.sqrt n - (1 / 3) * Real.sqrt ((n : ℝ) - 1)) * hsq_n1

/-- **Exact Unit-Cell Linear-Slope Square-Root Integral Identity**:
for every `2 ≤ n`,
`∫ x in ((n : ℝ) - 1)..(n : ℝ), ((x - (n : ℝ) + 1 / 2) / Real.sqrt x) = -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3`. -/
theorem intervalIntegral_linear_offset_div_sqrt_cell {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ), ((x - (n : ℝ) + 1 / 2) / Real.sqrt x)) =
      -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ n := by omega
  have hcongr : (∫ x in ((n : ℝ) - 1)..(n : ℝ), ((x - (n : ℝ) + 1 / 2) / Real.sqrt x)) =
      ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (Real.sqrt x - ((n : ℝ) - 1 / 2) * (Real.sqrt x)⁻¹) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx_pos)
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (le_of_lt hx_pos)
    apply mul_right_cancel₀ hne
    rw [div_mul_cancel₀ _ hne, sub_mul, mul_assoc, inv_mul_cancel₀ hne, hsq]
    ring
  have hint_sqrt : IntervalIntegrable Real.sqrt volume ((n : ℝ) - 1) (n : ℝ) :=
    Real.continuous_sqrt.intervalIntegrable _ _
  have hint_inv : IntervalIntegrable (fun x : ℝ => (Real.sqrt x)⁻¹) volume ((n : ℝ) - 1) (n : ℝ) := by
    refine (ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_).intervalIntegrable
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  rw [hcongr, intervalIntegral.integral_sub hint_sqrt (hint_inv.const_mul ((n : ℝ) - 1 / 2)),
    intervalIntegral.integral_const_mul, intervalIntegral_sqrt_cell hn,
    intervalIntegral_inv_sqrt_cell hn]
  exact two_thirds_sub_linear_mul_sqrt_sub_eq_neg_third_cube hn1

/-- **Exact Decomposition of `trapezoidalNumeratorCellDefect` into the Cubic-Weighted Forward
Difference plus `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and `N : ℕ`,
`trapezoidalNumeratorCellDefect f.1 N = (∑ n ∈ Finset.Icc 2 N, -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 * (weilSymmetricLogNumerator f.1 (n : ℝ) - weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))) + secantNumeratorCellDefect f.1 N`. -/
theorem trapezoidalNumeratorCellDefect_eq_cubic_diff_add_secantNumerator
    (f : WeilTestFn) (N : ℕ) :
    trapezoidalNumeratorCellDefect f.1 N =
      (∑ n ∈ Finset.Icc 2 N,
        -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 *
          (weilSymmetricLogNumerator f.1 (n : ℝ) -
            weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))) +
        secantNumeratorCellDefect f.1 N := by
  rw [trapezoidalNumeratorCellDefect, secantNumeratorCellDefect, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
    refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
    rw [uIcc_of_le (by linarith)] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hslope_int : IntervalIntegrable
      (fun x : ℝ => (x - (n : ℝ) + 1 / 2) / Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    simp_rw [div_eq_mul_inv]
    exact (((continuousOn_id.sub continuousOn_const).add continuousOn_const).mul hinv).intervalIntegrable
  have hsec_int : IntervalIntegrable
      (fun x : ℝ =>
        (weilSymmetricLogNumerator f.1 x -
          cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    have hnum : ContinuousOn
        (fun x : ℝ => weilSymmetricLogNumerator f.1 x)
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine (continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      rw [mem_Ici]
      linarith [hx.1]
    have hsec : ContinuousOn
        (fun x : ℝ => cellSecant (weilSymmetricLogNumerator f.1) n x)
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      unfold cellSecant
      exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
    simp_rw [div_eq_mul_inv]
    exact ((hnum.sub hsec).mul hinv).intervalIntegrable
  let Δ := weilSymmetricLogNumerator f.1 (n : ℝ) - weilSymmetricLogNumerator f.1 ((n : ℝ) - 1)
  have hterm1 : -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 * Δ =
      ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        Δ * ((x - (n : ℝ) + 1 / 2) / Real.sqrt x) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral_linear_offset_div_sqrt_cell hn.1]
    ring
  rw [hterm1, ← intervalIntegral.integral_add (hslope_int.const_mul Δ) hsec_int]
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hpt := sub_midpoint_eq_slope_add_sub_cellSecant (weilSymmetricLogNumerator f.1) n x
  dsimp [Δ]
  linear_combination (Real.sqrt x)⁻¹ * hpt

/-! ## Section 2: The Autocorrelation Origin Peak Summation-by-Parts Positivity Principle and `secantNumeratorCellDefect f.1 N ≤ trapezoidalNumeratorCellDefect f.1 N` -/

/-- **Autocorrelation Origin Peak Summation-by-Parts Positivity Principle**:
because `C_f(x) = weilSymmetricLogNumerator f.1 x` satisfies `C_f(1) = 2 ∫ ‖f.1‖²` and
`C_f(n) ≤ |C_f(n)| ≤ 2 ∫ ‖f.1‖²` for every `n ≥ 1`, any nonnegative sequence `w : ℕ → ℝ` that is
nonincreasing on `[2, N]` (`w (n + 1) ≤ w n`) with `0 ≤ w (N + 1)` and `C_f(N) = 0` satisfies
`2 * w (N + 1) * ∫ u, ‖f.1 u‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 2 N, -w n * (C_f(n) - C_f(n - 1))`. -/
theorem two_mul_tail_l2_le_neg_sum_Icc_two_mul_weilSymmetricLogNumerator_sub_pred
    (w : ℕ → ℝ) (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hw_anti : ∀ n ∈ Finset.Icc 2 N, w (n + 1) ≤ w n) :
    2 * w (N + 1) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 2 N,
        -w n * (weilSymmetricLogNumerator f.1 (n : ℝ) -
          weilSymmetricLogNumerator f.1 ((n : ℝ) - 1)) := by
  let v : ℕ → ℝ := fun n => weilSymmetricLogNumerator f.1 (n : ℝ)
  have hcongr : (∑ n ∈ Finset.Icc 2 N,
        -w n * (weilSymmetricLogNumerator f.1 (n : ℝ) -
          weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))) =
      -(∑ n ∈ Finset.Icc 2 N, w n * (v n - v (n - 1))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn1, Nat.cast_one]
    dsimp [v]
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
  have hsum_le : (∑ n ∈ Finset.Icc 2 N, (w n - w (n + 1)) * v n) ≤
      (w 2 - w (N + 1)) * (2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
    rw [← sum_Icc_two_sub_succ_nat w hN1, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    have hdiff_nonneg : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw_anti n hn)
    have hvn_le : v n ≤ 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
      (le_abs_self (v n)).trans (abs_weilSymmetricLogNumerator_le_two_mul_integral_norm_sq f (n : ℝ))
    exact mul_le_mul_of_nonneg_left hvn_le hdiff_nonneg
  rw [hvN, mul_zero, zero_sub, hv1]
  linarith

/-- **Unconditional Origin-Peak Positivity of the Cubic Square-Root Slope Sum**:
for every `f : WeilTestFn` and `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 * ∫ u, ‖f.1 u‖ ^ 2 ≤ ∑ n ∈ Finset.Icc 2 N, -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 * (weilSymmetricLogNumerator f.1 (n : ℝ) - weilSymmetricLogNumerator f.1 ((n : ℝ) - 1))`. -/
theorem two_thirds_cube_tail_l2_le_neg_sum_cubic_diff_weilSymmetricLogNumerator
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    (2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 2 N,
        -(1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 *
          (weilSymmetricLogNumerator f.1 (n : ℝ) -
            weilSymmetricLogNumerator f.1 ((n : ℝ) - 1)) := by
  let w : ℕ → ℝ := fun n => (1 / 3) * (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3
  have hw_anti : ∀ n ∈ Finset.Icc 2 N, w (n + 1) ≤ w n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    dsimp [w]
    push_cast
    rw [add_sub_cancel_right]
    have hle := sqrt_succ_sub_sqrt_le_sqrt_sub_sqrt_pred (by omega : 1 ≤ n)
    have hnonneg : 0 ≤ Real.sqrt ((n : ℝ) + 1) - Real.sqrt n :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
    have hcube := pow_le_pow_left₀ hnonneg hle 3
    linarith
  have hmain :=
    two_mul_tail_l2_le_neg_sum_Icc_two_mul_weilSymmetricLogNumerator_sub_pred w f hN1 hN0 hw_anti
  have hwN : 2 * w (N + 1) = (2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 := by
    dsimp [w]
    push_cast
    rw [add_sub_cancel_right]
    ring
  rw [hwN] at hmain
  refine hmain.trans_eq ?_
  refine Finset.sum_congr rfl fun n _ => ?_
  dsimp [w]
  ring

/-- **Unconditional Comparison `secantNumeratorCellDefect ≤ trapezoidalNumeratorCellDefect` with
Positive Cubic Tail Surplus**:
for every `f : WeilTestFn` and `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`secantNumeratorCellDefect f.1 N + (2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 * ∫ u, ‖f.1 u‖ ^ 2 ≤ trapezoidalNumeratorCellDefect f.1 N`. -/
theorem secantNumeratorCellDefect_add_cube_tail_le_trapezoidalNumeratorCellDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    secantNumeratorCellDefect f.1 N +
        (2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      trapezoidalNumeratorCellDefect f.1 N := by
  rw [trapezoidalNumeratorCellDefect_eq_cubic_diff_add_secantNumerator]
  linarith [two_thirds_cube_tail_l2_le_neg_sum_cubic_diff_weilSymmetricLogNumerator f hN1 hN0]

/-- **Unconditional Comparison `secantNumeratorCellDefect f.1 N ≤ trapezoidalNumeratorCellDefect f.1 N`**: -/
theorem secantNumeratorCellDefect_le_trapezoidalNumeratorCellDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0) :
    secantNumeratorCellDefect f.1 N ≤ trapezoidalNumeratorCellDefect f.1 N := by
  have h := secantNumeratorCellDefect_add_cube_tail_le_trapezoidalNumeratorCellDefect f hN1 hN0
  have hdiff : 0 ≤ Real.sqrt ((N : ℝ) + 1) - Real.sqrt N :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hnorm : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have htail : 0 ≤ (2 / 3) * (Real.sqrt ((N : ℝ) + 1) - Real.sqrt N) ^ 3 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 :=
    by positivity
  linarith

/-! ## Section 3: Unconditional `√2 / 2 > 7 / 10` Positive $L^2$ Surplus over `secantNumeratorCellDefect` and `1 / √(n - 1)`-Weighted Peano Semiconcavity Bounds -/

/-- **Unconditional `√2 / 2` Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(Real.sqrt 2 / 2) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem sqrt_two_div_two_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (Real.sqrt 2 / 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := sqrt_two_div_two_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have h2 := secantNumeratorCellDefect_le_trapezoidalNumeratorCellDefect f hN1 hN0
  linarith

/-- **Unconditional `7 / 10` Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(7 / 10) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem seven_tenths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (7 / 10) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_tenths_l2_add_trapezoidalNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have h2 := secantNumeratorCellDefect_le_trapezoidalNumeratorCellDefect f hN1 hN0
  linarith

/-- **Hermite–Hadamard Secant Positivity for `secantNumeratorCellDefect`**:
if `cellSecant (weilSymmetricLogNumerator f.1) n x ≤ weilSymmetricLogNumerator f.1 x` on `[n - 1, n]`
for every `n ∈ Finset.Icc 2 N`, then `0 ≤ secantNumeratorCellDefect f.1 N`. -/
theorem secantNumeratorCellDefect_nonneg_of_cellSecant_le (f : WeilTestFn) {N : ℕ}
    (hsec : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      cellSecant (weilSymmetricLogNumerator f.1) n x ≤ weilSymmetricLogNumerator f.1 x) :
    0 ≤ secantNumeratorCellDefect f.1 N := by
  rw [secantNumeratorCellDefect]
  refine Finset.sum_nonneg fun n hn => ?_
  have hn_mem := Finset.mem_Icc.mp hn
  have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  refine intervalIntegral.integral_nonneg hle fun x hx => ?_
  have hnum : 0 ≤ weilSymmetricLogNumerator f.1 x -
      cellSecant (weilSymmetricLogNumerator f.1) n x :=
    sub_nonneg.mpr (hsec n hn x hx)
  exact div_nonneg hnum (Real.sqrt_nonneg x)

/-- **`1 / √(n - 1)`-Weighted Peano Semiconcavity Lower Bound for `secantNumeratorCellDefect`**:
if on each cell `[n - 1, n]` (`n ∈ Finset.Icc 2 N`),
`-(K n / 2) * cellParabola n x ≤ weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x`
with `0 ≤ K n`, then since `1 / √x ≤ 1 / √(n - 1)` and `0 ≤ cellParabola n x` on `[n - 1, n]`,
`-(∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    (f : WeilTestFn) {N : ℕ} (K : ℕ → ℝ)
    (hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤
      secantNumeratorCellDefect f.1 N := by
  rw [secantNumeratorCellDefect, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn_mem := Finset.mem_Icc.mp hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
  have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
    refine ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun x hx => ?_
    rw [uIcc_of_le hle] at hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
  have hnum_int : IntervalIntegrable
      (fun x : ℝ =>
        (weilSymmetricLogNumerator f.1 x -
          cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    have hnum : ContinuousOn
        (fun x : ℝ => weilSymmetricLogNumerator f.1 x)
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      refine (continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_
      rw [uIcc_of_le hle] at hx
      rw [mem_Ici]
      linarith [hx.1]
    have hsec : ContinuousOn
        (fun x : ℝ => cellSecant (weilSymmetricLogNumerator f.1) n x)
        (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
      unfold cellSecant
      exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
    simp_rw [div_eq_mul_inv]
    exact ((hnum.sub hsec).mul hinv).intervalIntegrable
  have hpar_int : IntervalIntegrable
      (fun x : ℝ => -((K n / (2 * Real.sqrt ((n : ℝ) - 1))) * cellParabola n x))
      volume ((n : ℝ) - 1) (n : ℝ) := by
    unfold cellParabola
    exact (((continuousOn_id.sub continuousOn_const).mul
      (continuousOn_const.sub continuousOn_id)).const_mul _).neg.intervalIntegrable
  have hpar_eval :
      (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        -((K n / (2 * Real.sqrt ((n : ℝ) - 1))) * cellParabola n x)) =
      -(K n / (12 * Real.sqrt ((n : ℝ) - 1))) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral_cellParabola n]
    ring
  rw [← hpar_eval]
  refine intervalIntegral.integral_mono_on hle hpar_int hnum_int fun x hx => ?_
  have hK := hK0 n hn
  have hpar_nonneg := cellParabola_nonneg_of_mem_Icc hx
  have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt_le : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
  have hinv_le : (Real.sqrt x)⁻¹ ≤ (Real.sqrt ((n : ℝ) - 1))⁻¹ :=
    inv_anti₀ hsqrt_pos hsqrt_le
  have hpt := hsemi n hn x hx
  have h1 : -(K n / 2 * cellParabola n x) / Real.sqrt x ≤
      (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) /
        Real.sqrt x :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg x)
  have h2 : -((K n / (2 * Real.sqrt ((n : ℝ) - 1))) * cellParabola n x) ≤
      -(K n / 2 * cellParabola n x) / Real.sqrt x := by
    have hnonneg : 0 ≤ (K n / 2) * cellParabola n x := mul_nonneg (by linarith) hpar_nonneg
    have hmul := mul_le_mul_of_nonneg_left hinv_le hnonneg
    calc
      -((K n / (2 * Real.sqrt ((n : ℝ) - 1))) * cellParabola n x) =
          -((K n / 2 * cellParabola n x) * (Real.sqrt ((n : ℝ) - 1))⁻¹) := by ring
      _ ≤ -((K n / 2 * cellParabola n x) * (Real.sqrt x)⁻¹) := neg_le_neg hmul
      _ = -(K n / 2 * cellParabola n x) / Real.sqrt x := by ring
  exact h2.trans h1

/-- **Upgraded Coercive Lower Bound on `markovEnergy` in Terms of `secantNumeratorCellDefect`
(Primitive Hyperplane)**:
for every real test `f ∈ C²_c(ℝ)` with `coshHalfMoment f = 0`, if `θ ≥ max (20 / 7) (Real.log N)`
and `0 ≤ iteratedForwardDiff m (logValue F) n` on `[2, N]`, then
`(1 / 100 + (7 / 10) * θ - 2) * ∫ ‖F‖² + (θ - 1) * bochnerResolventEnergy k_F + 2 * θ * sinhHalfMoment f ^ 2 + θ * secantNumeratorCellDefect F N ≤ markovEnergy F`. -/
theorem secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero (m : ℕ) {θ : ℝ}
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
        θ * secantNumeratorCellDefect (realWeilTestFn f hf hfc).1 N ≤
      markovEnergy (realWeilTestFn f hf hfc).1 := by
  have h1 := trapezoidalNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have h2 := secantNumeratorCellDefect_le_trapezoidalNumeratorCellDefect
    (realWeilTestFn f hf hfc) hN1 hN0
  have hθ2 := mul_le_mul_of_nonneg_left h2 hθ0
  linarith

end RHTower

end
