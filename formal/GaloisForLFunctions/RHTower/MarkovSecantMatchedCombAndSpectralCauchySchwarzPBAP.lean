import GaloisForLFunctions.RHTower.MarkovSpectralSecondMomentAndHalfL2SurplusPBAP

/-!
# The Secant-Matched Poisson Comb `secantMatchedCombWeight`, the Universal Spectral Cauchy–Schwarz Inequality, and the `(71 / 120) ∫ ‖f.1‖² - (119 / 240) spectralSecondMoment f.1` Coercivity Law

In Module 51, we proved that the second derivative of `cos (r * log t)` on `[n - 1, n]` has an
exact `1 / t^2` factor, yielding the cutoff-independent $p = 5/2$ bound
`-(7 / 24) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`,
and at frequency scale `λ = 1` (`2 * |r| ≤ r^2 + 1`),
`(61 / 120) * ∫ ‖f.1‖² - (7 / 16) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.

In this module, we establish three major advances along Route HF / PBAP:

1. **Section 1 (The Exact Secant-Matched Poisson Comb `secantMatchedCombWeight` and Its
   `(16√2 - 20) / 3 > 7 / 8` Un-Reduced Origin $L^2$ Surplus):**
   - We define `secantMatchedCombWeight n := unitStepCountertermWeight n + secantCombinedSecularWeight n`,
     which satisfies `1 ≤ secantMatchedCombWeight n` for all `2 ≤ n` (`one_le_secantMatchedCombWeight_of_two_le`).
   - Absorbing `secantCombinedSecularWeight` directly into the discrete Poisson comb eliminates the
     secular counterterm error completely in the Primitive Hyperplane Conservation Law
     (`secantMatchedComb_add_origin_add_secantNumerator_add_resolvent_add_sinh_sq_eq_zero_of_cosh_zero`):
     `primeBlindCounterterm secantMatchedCombWeight F + ((16 * √2 - 20) / 3) * ∫ ‖F‖² + secantNumeratorCellDefect F N + bochnerResolventEnergy k_F + 2 * sinhHalfMoment f ^ 2 = 0`.
   - Using the rational certificate `181 / 128 ≤ √2` (`181^2 = 32761 < 32768 = 2 * 128^2`), we prove
     `7 / 8 ≤ (16 * √2 - 20) / 3` (`seven_eighths_le_sixteen_sqrt_two_sub_twenty_div_three`), so on
     the Prime-Blind Cone (`logVector f = 0`), `rightCellQuadratureDefect` enjoys the full
     `(7 / 8) * ∫ ‖f.1‖²` positive surplus (`seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero`).

2. **Section 2 (The Universal Spectral Quadratic Form, General $\lambda$-Scale Interpolation, and
   Exact Spectral Cauchy–Schwarz Inequality):**
   - Integrating the nonnegative square `(1 / (2 * π)) * ‖paperFT f.1 r‖ ^ 2 * 2 * (t * |r| - 1) ^ 2 ≥ 0`
     and applying Plancherel (`one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq`) proves the
     universal spectral quadratic form (`spectral_quadratic_nonneg`): for every `t : ℝ`,
     `0 ≤ t ^ 2 * spectralSecondMoment f.1 - 2 * t * spectralFirstMoment f.1 + 2 * ∫ u, ‖f.1 u‖ ^ 2`.
   - From this single universal quadratic inequality, we derive:
     - the general `λ > 0` scale interpolation (`spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2`):
       `spectralFirstMoment f.1 ≤ (λ / 2) * spectralSecondMoment f.1 + (1 / λ) * ∫ u, ‖f.1 u‖ ^ 2`, and
     - the **Exact Spectral Cauchy–Schwarz Inequality**
       (`sq_spectralFirstMoment_le_two_mul_spectralSecondMoment_mul_l2` and
       `spectralFirstMoment_le_sqrt_two_mul_spectralSecondMoment_mul_l2`):
       `spectralFirstMoment f.1 ^ 2 ≤ 2 * spectralSecondMoment f.1 * ∫ u, ‖f.1 u‖ ^ 2` and
       `spectralFirstMoment f.1 ≤ Real.sqrt (2 * spectralSecondMoment f.1 * ∫ u, ‖f.1 u‖ ^ 2)`.

3. **Section 3 (The `(71 / 120) ∫ ‖f.1‖² - (119 / 240) spectralSecondMoment f.1` Coercivity Bound
   and Unconditional `markovEnergy ≥ 0` on the Primitive Hyperplane):**
   - Choosing the rational scale `λ = 7 / 5` (where `1 / λ = 5 / 7` cancels the `7` in `7 / 24`!)
     yields (`seventy_one_one_twentieths_l2_sub_one_nineteen_two_fortieths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(71 / 120) * ∫ ‖f.1‖² - (119 / 240) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     raising the critical `spectralSecondMoment / L^2` ratio to `142 / 119 > 1.1932` and proving
     unconditional `0 ≤ markovEnergy F` on the primitive hyperplane whenever
     `spectralSecondMoment F ≤ (142 / 119 - δ) * ∫ ‖F‖²` (`markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_of_cosh_zero`).
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

/-! ## Section 1: The Exact Secant-Matched Poisson Comb `secantMatchedCombWeight` and Its `(16√2 - 20) / 3 > 7 / 8` Un-Reduced Origin $L^2$ Surplus -/

/-- **The Secant-Matched Poisson Comb Weight `secantMatchedCombWeight`**:
`secantMatchedCombWeight n = unitStepCountertermWeight n + secantCombinedSecularWeight n`. -/
def secantMatchedCombWeight (n : ℕ) : ℝ :=
  unitStepCountertermWeight n + secantCombinedSecularWeight n

/-- At `n = 0`, `secantMatchedCombWeight 0 = 0`. -/
@[simp]
theorem secantMatchedCombWeight_zero : secantMatchedCombWeight 0 = 0 := by
  unfold secantMatchedCombWeight unitStepCountertermWeight
    secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
  norm_num

/-- At `n = 1`, `secantMatchedCombWeight 1 = 0`. -/
@[simp]
theorem secantMatchedCombWeight_one : secantMatchedCombWeight 1 = 0 := by
  unfold secantMatchedCombWeight unitStepCountertermWeight
    secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
  norm_num

/-- For every `2 ≤ n`, `1 ≤ secantMatchedCombWeight n`. -/
theorem one_le_secantMatchedCombWeight_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ secantMatchedCombWeight n := by
  unfold secantMatchedCombWeight unitStepCountertermWeight
  simp only [if_pos hn]
  linarith [secantCombinedSecularWeight_nonneg n]

/-- `secantMatchedCombWeight n` is nonnegative for all `n : ℕ`. -/
theorem secantMatchedCombWeight_nonneg (n : ℕ) :
    0 ≤ secantMatchedCombWeight n := by
  unfold secantMatchedCombWeight unitStepCountertermWeight
  split_ifs <;> linarith [secantCombinedSecularWeight_nonneg n]

/-- Linearity of `primeBlindCounterterm` for `secantMatchedCombWeight`: -/
theorem primeBlindCounterterm_secantMatchedCombWeight_eq_add (f : WeilTestFn) {N : ℕ}
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    primeBlindCounterterm secantMatchedCombWeight f =
      primeBlindCounterterm unitStepCountertermWeight f +
        primeBlindCounterterm secantCombinedSecularWeight f := by
  rw [primeBlindCounterterm_eq_sum_Icc secantMatchedCombWeight f hN,
    primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight f hN,
    primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold secantMatchedCombWeight
  ring

/-- **Secant-Matched Conservation Law on the Primitive Hyperplane (`coshHalfMoment f = 0`)**:
absorbing `secantCombinedSecularWeight` into the discrete Poisson comb eliminates the secular
counterterm remainder completely and preserves the full `((16 * √2 - 20) / 3) * ∫ ‖F‖²` origin
surplus! -/
theorem secantMatchedComb_add_origin_add_secantNumerator_add_resolvent_add_sinh_sq_eq_zero_of_cosh_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0) :
    primeBlindCounterterm secantMatchedCombWeight (realWeilTestFn f hf hfc) +
        ((16 * Real.sqrt 2 - 20) / 3) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) +
        secantNumeratorCellDefect (realWeilTestFn f hf hfc).1 N +
        bochnerResolventEnergy
          (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
        2 * sinhHalfMoment f ^ 2 = 0 := by
  have h1 := unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
    hf hfc hcosh hN1 hN
  have h2 := rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
    (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h3 := primeBlindCounterterm_secantMatchedCombWeight_eq_add
    (realWeilTestFn f hf hfc) (fun n hn => hN n (by exact_mod_cast hn))
  linarith

/-- Rational lower bound `7 / 8 ≤ (16 * Real.sqrt 2 - 20) / 3` via `181 / 128 ≤ √2`
(`181^2 = 32761 < 32768 = 2 * 128^2`). -/
theorem seven_eighths_le_sixteen_sqrt_two_sub_twenty_div_three :
    (7 / 8 : ℝ) ≤ (16 * Real.sqrt 2 - 20) / 3 := by
  have h : (181 / 128 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 181 / 128)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Prime-Blind Cone `(7 / 8) ∫ ‖f.1‖²` Surplus Theorem**:
whenever `logVector f = 0`, `primeBlindCounterterm secantCombinedSecularWeight f = 0`, so
`(7 / 8) * ∫ ‖f.1‖² + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (7 / 8) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq := rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
    f hN1 hN0 hN
  have hct : primeBlindCounterterm secantCombinedSecularWeight f = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h78 := mul_le_mul_of_nonneg_right
    seven_eighths_le_sixteen_sqrt_two_sub_twenty_div_three hnorm_nonneg
  linarith

/-! ## Section 2: The Universal Spectral Quadratic Form, General $\lambda$-Scale Interpolation, and Exact Spectral Cauchy–Schwarz Inequality -/

/-- **The Universal Spectral Quadratic Form Inequality**:
for every `f : WeilTestFn` with integrable first and second spectral moments and every `t : ℝ`,
`0 ≤ t ^ 2 * spectralSecondMoment f.1 - 2 * t * spectralFirstMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectral_quadratic_nonneg
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (t : ℝ) :
    0 ≤ t ^ 2 * spectralSecondMoment f.1 - 2 * t * spectralFirstMoment f.1 +
      2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hrhs :
      t ^ 2 * spectralSecondMoment f.1 - 2 * t * spectralFirstMoment f.1 +
        2 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
      (1 / (2 * π)) * ∫ r : ℝ,
        ((t ^ 2 * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) -
          (2 * t) * (‖paperFT f.1 r‖ ^ 2 * (2 * |r|))) +
          ‖paperFT f.1 r‖ ^ 2 * 2) := by
    unfold spectralSecondMoment spectralFirstMoment
    have hint_sub := integral_sub (hint2.const_mul (t ^ 2)) (hint1.const_mul (2 * t))
    have hint_add := integral_add
      ((hint2.const_mul (t ^ 2)).sub (hint1.const_mul (2 * t)))
      (hsq.mul_const 2)
    dsimp at hint_sub hint_add
    rw [hint_add, hint_sub, integral_const_mul, integral_const_mul]
    linarith [hplanch]
  rw [hrhs]
  refine mul_nonneg (div_nonneg zero_le_one Real.two_pi_pos.le)
    (integral_nonneg fun r => ?_)
  dsimp
  have hr2 : |r| ^ 2 = r ^ 2 := sq_abs r
  have hsq_nonneg : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 * (t * |r| - 1) ^ 2 := by positivity
  have halg : ‖paperFT f.1 r‖ ^ 2 * 2 * (t * |r| - 1) ^ 2 =
      (t ^ 2 * (‖paperFT f.1 r‖ ^ 2 * (2 * |r| ^ 2)) -
        (2 * t) * (‖paperFT f.1 r‖ ^ 2 * (2 * |r|))) +
        ‖paperFT f.1 r‖ ^ 2 * 2 := by ring
  rw [hr2] at halg
  linarith

/-- **General $\lambda$-Scale Spectral Interpolation (`0 < λ`)**:
for every `0 < lam`,
`spectralFirstMoment f.1 ≤ (lam / 2) * spectralSecondMoment f.1 + (1 / lam) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {lam : ℝ} (hlam : 0 < lam) :
    spectralFirstMoment f.1 ≤
      (lam / 2) * spectralSecondMoment f.1 + (1 / lam) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hlam_ne : lam ≠ 0 := hlam.ne'
  have hq_lam := spectral_quadratic_nonneg f hint1 hint2 lam
  have hmul_lam := mul_le_mul_of_nonneg_left hq_lam (div_nonneg zero_le_one (by linarith : 0 ≤ 2 * lam))
  have halg_lam : (1 / (2 * lam)) *
      (lam ^ 2 * spectralSecondMoment f.1 - 2 * lam * spectralFirstMoment f.1 +
        2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) =
      (lam / 2) * spectralSecondMoment f.1 - spectralFirstMoment f.1 +
        (1 / lam) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    field_simp [hlam_ne]
  linarith

/-- If `spectralSecondMoment f.1 = 0`, then `spectralFirstMoment f.1 = 0`. -/
theorem spectralFirstMoment_eq_zero_of_spectralSecondMoment_eq_zero
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (hzero : spectralSecondMoment f.1 = 0) :
    spectralFirstMoment f.1 = 0 := by
  have hnonneg := spectralFirstMoment_nonneg f.1
  by_contra hne
  have hpos : 0 < spectralFirstMoment f.1 := lt_of_le_of_ne hnonneg (Ne.symm hne)
  let t := ((∫ u : ℝ, ‖f.1 u‖ ^ 2) + 1) / spectralFirstMoment f.1
  have hq := spectral_quadratic_nonneg f hint1 hint2 t
  rw [hzero, mul_zero, zero_sub] at hq
  have hmul : 2 * t * spectralFirstMoment f.1 = 2 * ((∫ u : ℝ, ‖f.1 u‖ ^ 2) + 1) := by
    dsimp [t]
    rw [mul_assoc, div_mul_cancel₀ _ hpos.ne']
  linarith

/-- **Exact Spectral Cauchy–Schwarz Inequality (Squared Form)**:
`spectralFirstMoment f.1 ^ 2 ≤ 2 * spectralSecondMoment f.1 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem sq_spectralFirstMoment_le_two_mul_spectralSecondMoment_mul_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ^ 2 ≤
      2 * spectralSecondMoment f.1 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rcases eq_or_lt_of_le (spectralSecondMoment_nonneg f.1) with hzero | hpos
  · have h1 := spectralFirstMoment_eq_zero_of_spectralSecondMoment_eq_zero f hint1 hint2 hzero.symm
    rw [h1, ← hzero]
    norm_num
  · let t := spectralFirstMoment f.1 / spectralSecondMoment f.1
    have hq := spectral_quadratic_nonneg f hint1 hint2 t
    have hmul := mul_le_mul_of_nonneg_left hq hpos.le
    have hne : spectralSecondMoment f.1 ≠ 0 := hpos.ne'
    have halg : spectralSecondMoment f.1 *
        (t ^ 2 * spectralSecondMoment f.1 - 2 * t * spectralFirstMoment f.1 +
          2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        2 * spectralSecondMoment f.1 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
          spectralFirstMoment f.1 ^ 2 := by
      dsimp [t]
      field_simp [hne]
      ring
    linarith

/-- **Exact Spectral Cauchy–Schwarz Inequality (Square-Root Form)**:
`spectralFirstMoment f.1 ≤ Real.sqrt (2 * spectralSecondMoment f.1 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)`. -/
theorem spectralFirstMoment_le_sqrt_two_mul_spectralSecondMoment_mul_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ≤
      Real.sqrt (2 * spectralSecondMoment f.1 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
  rw [← Real.sqrt_sq (spectralFirstMoment_nonneg f.1)]
  exact Real.sqrt_le_sqrt (sq_spectralFirstMoment_le_two_mul_spectralSecondMoment_mul_l2 f hint1 hint2)

/-! ## Section 3: The `(71 / 120) ∫ ‖f.1‖² - (119 / 240) spectralSecondMoment f.1` Coercivity Bound and Unconditional `markovEnergy ≥ 0` on the Primitive Hyperplane -/

/-- Specializing `spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2` at
`lam = 7 / 5` gives
`spectralFirstMoment f.1 ≤ (7 / 10) * spectralSecondMoment f.1 + (5 / 7) * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectralFirstMoment_le_seven_tenths_spectralSecondMoment_add_five_sevenths_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ≤
      (7 / 10) * spectralSecondMoment f.1 + (5 / 7) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have h := spectralFirstMoment_le_scale_spectralSecondMoment_add_inv_scale_l2
    f hint1 hint2 (by norm_num : (0 : ℝ) < 7 / 5)
  linarith

/-- **Cutoff-Independent `-(119 / 240) spectralSecondMoment f.1 - (5 / 24) ∫ ‖f.1‖² ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_one_nineteen_two_fortieths_spectralSecondMoment_sub_five_twenty_fourths_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(119 / 240) * spectralSecondMoment f.1 - (5 / 24) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have h1 := neg_seven_twenty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h2 := spectralFirstMoment_le_seven_tenths_spectralSecondMoment_add_five_sevenths_l2
    f hint1 hint2
  linarith

/-- **Pure Second-Moment `(71 / 120) ∫ ‖f.1‖² - (119 / 240) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect`**:
at `lam = 7 / 5`, `1 / lam = 5 / 7` cancels the `7` in `7 / 24`, leaving `4 / 5 - 5 / 24 = 71 / 120`
and `(7 / 24) * (17 / 10) = 119 / 240` (critical ratio `142 / 119 > 1.1932`)! -/
theorem seventy_one_one_twentieths_l2_sub_one_nineteen_two_fortieths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (71 / 120) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (119 / 240) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_one_nineteen_two_fortieths_spectralSecondMoment_sub_five_twenty_fourths_l2_le_secantNumeratorCellDefect
    f hint1 hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (142 / 119 - δ) ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint1 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (142 / 119 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (480 / (119 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h119δ : 0 < 119 * δ := by linarith
  have hθδ_le : 480 / (119 * δ) ≤ θ := le_max_right _ _
  have hθδ : 480 ≤ θ * (119 * δ) := (div_le_iff₀ h119δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_one_nineteen_two_fortieths_spectralSecondMoment_sub_five_twenty_fourths_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint1 hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (119 / 240) * θ)
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hθδ_norm := mul_le_mul_of_nonneg_right hθδ hnorm_nonneg
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
