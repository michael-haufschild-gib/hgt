import GaloisForLFunctions.RHTower.WeilDeviationBumps
import GaloisForLFunctions.HTGeometry.ConductorPlancherelPairing

/-!
# The Fejér test with spectral gap below `log 2`

Let `ρ = 1_{[−a,a]} ⋆ m`, with `a = 33/100` and `m ≥ 0` a smooth bump of integral one supported in
`[−1/100, 1/100]`. The Fejér test is `F = |𝓕ρ|²`. It satisfies:
- `F ≥ 0` and `F(0) = (2a)² = 0.4356` (`fejerTest_zero`);
- `F(ξ) ≤ 1/(πξ)²` (`fejerTest_le`), because `|𝓕1_{[−a,a]}(ξ)| ≤ 1/(π|ξ|)` and `|𝓕m| ≤ 1`;
- `𝓕F(u) = ∫ ρ(x) ρ(x + u) dx` (Plancherel), which vanishes for `|u| > 17/25 < log 2`
  (`fourier_fejerTest_eq_zero`). So `𝓕F` vanishes at `±log n` for every `n ≥ 2`.

At a real zero `t` of `Ξ` the frequency is `ξ = t/2π`, so `F(ξ) ≤ 4/t²`. The sum over any finite
set of real zeros is at most `3/8 < F(0)` (`sum_fejerTest_zeros_le`).
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff Convolution

namespace RHTower.WeilExcess

noncomputable section

/-! ## The profile `ρ` -/

/-- The mollifier bump, supported in `[−1/100, 1/100]`. -/
def fejerMollifierBump : ContDiffBump (0 : ℝ) := ⟨1 / 200, 1 / 100, by norm_num, by norm_num⟩

/-- The normalized mollifier. -/
def fejerMollifier (x : ℝ) : ℝ := fejerMollifierBump.normed volume x

theorem fejerMollifier_nonneg (x : ℝ) : 0 ≤ fejerMollifier x := fejerMollifierBump.nonneg_normed x

theorem integral_fejerMollifier : ∫ x, fejerMollifier x = 1 := fejerMollifierBump.integral_normed

theorem fejerMollifier_eq_zero {x : ℝ} (hx : 1 / 100 ≤ |x|) : fejerMollifier x = 0 := by
  have h : x ∉ Function.support fejerMollifier := by
    rw [show fejerMollifier = fejerMollifierBump.normed volume from rfl,
      fejerMollifierBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
    exact hx
  simpa using h

theorem contDiff_fejerMollifier : ContDiff ℝ ∞ fejerMollifier := fejerMollifierBump.contDiff_normed

theorem hasCompactSupport_fejerMollifier : HasCompactSupport fejerMollifier :=
  fejerMollifierBump.hasCompactSupport_normed

/-- The half-width `a = 33/100`. -/
def fejerHalfWidth : ℝ := 33 / 100

/-- The indicator `1_{[−a,a]}`. -/
def fejerIndicator (x : ℝ) : ℝ := (Icc (-fejerHalfWidth) fejerHalfWidth).indicator 1 x

/-- The profile `ρ = 1_{[−a,a]} ⋆ m`. -/
def fejerProfile (x : ℝ) : ℝ := ∫ t, fejerIndicator t * fejerMollifier (x - t)

theorem fejerProfile_eq_convolution :
    fejerProfile = convolution fejerIndicator fejerMollifier (ContinuousLinearMap.lsmul ℝ ℝ)
      volume := by
  funext x; rw [convolution_def]; rfl

theorem locallyIntegrable_fejerIndicator : LocallyIntegrable fejerIndicator volume := by
  show LocallyIntegrable ((Icc (-fejerHalfWidth) fejerHalfWidth).indicator (fun _ => (1 : ℝ))) volume
  exact (locallyIntegrable_const (1 : ℝ)).indicator measurableSet_Icc

theorem contDiff_fejerProfile : ContDiff ℝ ∞ fejerProfile := by
  rw [fejerProfile_eq_convolution]
  exact hasCompactSupport_fejerMollifier.contDiff_convolution_right _
    locallyIntegrable_fejerIndicator contDiff_fejerMollifier

theorem fejerProfile_eq_zero {x : ℝ} (hx : 17 / 50 < |x|) : fejerProfile x = 0 := by
  unfold fejerProfile
  have h0 : (fun t => fejerIndicator t * fejerMollifier (x - t)) = fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : t ∈ Icc (-fejerHalfWidth) fejerHalfWidth
    · have hta : |t| ≤ 33 / 100 := abs_le.mpr ⟨by
        have := ht.1; simp only [fejerHalfWidth] at this; linarith,
        by have := ht.2; simp only [fejerHalfWidth] at this; linarith⟩
      have : 1 / 100 ≤ |x - t| := by
        have := abs_sub_abs_le_abs_sub x t; linarith
      rw [fejerMollifier_eq_zero this, mul_zero]
    · simp [fejerIndicator, Set.indicator_of_notMem ht]
  rw [h0, integral_zero]

theorem hasCompactSupport_fejerProfile : HasCompactSupport fejerProfile := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(17 / 50)) (b := 17 / 50)) fun x hx => ?_
  apply fejerProfile_eq_zero
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hx | hx
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

/-- The complex profile. -/
def fejerProfileC (x : ℝ) : ℂ := (fejerProfile x : ℂ)

theorem contDiff_fejerProfileC : ContDiff ℝ ∞ fejerProfileC :=
  ofRealCLM.contDiff.comp contDiff_fejerProfile

theorem hasCompactSupport_fejerProfileC : HasCompactSupport fejerProfileC :=
  hasCompactSupport_fejerProfile.comp_left Complex.ofReal_zero

theorem integrable_fejerProfileC : Integrable fejerProfileC :=
  contDiff_fejerProfileC.continuous.integrable_of_hasCompactSupport hasCompactSupport_fejerProfileC

/-! ## The transform of `ρ` -/

/-- The transform of the indicator. -/
theorem norm_fourier_fejerIndicator_le {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun x => (fejerIndicator x : ℂ)) ξ‖ ≤ 1 / (π * |ξ|) := by
  rw [fourier_eq_integral]
  have hint : (∫ x, Complex.exp (-(2 * π * x * ξ : ℝ) * I) * (fejerIndicator x : ℂ)) =
      ∫ x in (-fejerHalfWidth)..fejerHalfWidth,
        Complex.exp ((-2 * π * ξ * I) * x) := by
    rw [intervalIntegral.integral_of_le (by norm_num [fejerHalfWidth]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Icc (-fejerHalfWidth) fejerHalfWidth
    · simp only [fejerIndicator, Set.indicator_of_mem hx, Pi.one_apply, Complex.ofReal_one,
        mul_one]
      congr 1; push_cast; ring
    · simp [fejerIndicator, Set.indicator_of_notMem hx]
  have hc : (-2 * π * ξ * I : ℂ) ≠ 0 := by
    have : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [hπ, this, I_ne_zero]
  rw [hint, integral_exp_mul_complex hc]
  rw [norm_div]
  have hnum : ‖Complex.exp ((-2 * π * ξ * I) * fejerHalfWidth) -
      Complex.exp ((-2 * π * ξ * I) * ((-fejerHalfWidth : ℝ) : ℂ))‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have e1 : ‖Complex.exp ((-2 * π * ξ * I) * fejerHalfWidth)‖ = 1 := by
      rw [show (-2 * π * ξ * I) * (fejerHalfWidth : ℂ) =
        ((-2 * π * ξ * fejerHalfWidth : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have e2 : ‖Complex.exp ((-2 * π * ξ * I) * (-fejerHalfWidth : ℝ))‖ = 1 := by
      rw [show (-2 * π * ξ * I) * ((-fejerHalfWidth : ℝ) : ℂ) =
        ((2 * π * ξ * fejerHalfWidth : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [e1, e2]; norm_num
  have hden : ‖(-2 * π * ξ * I : ℂ)‖ = 2 * π * |ξ| := by
    simp [abs_of_pos Real.pi_pos]
  rw [hden]
  calc ‖Complex.exp ((-2 * π * ξ * I) * fejerHalfWidth) -
        Complex.exp ((-2 * π * ξ * I) * ((-fejerHalfWidth : ℝ) : ℂ))‖ / (2 * π * |ξ|)
      ≤ 2 / (2 * π * |ξ|) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (π * |ξ|) := by field_simp

/-- The complex indicator and mollifier. -/
def fejerIndicatorC (x : ℝ) : ℂ := (fejerIndicator x : ℂ)

def fejerMollifierC (x : ℝ) : ℂ := (fejerMollifier x : ℂ)

theorem integrable_fejerIndicatorC : Integrable fejerIndicatorC := by
  have : Integrable fejerIndicator :=
    (continuous_const.integrableOn_Icc (a := -fejerHalfWidth) (b := fejerHalfWidth)
      (f := fun _ : ℝ => (1 : ℝ))).integrable_indicator measurableSet_Icc
  exact this.ofReal

theorem integrable_fejerMollifierC : Integrable fejerMollifierC :=
  (fejerMollifierBump.integrable_normed (μ := volume)).ofReal

theorem fejerProfileC_eq_convolution :
    fejerProfileC = fejerIndicatorC ⋆[ContinuousLinearMap.mul ℂ ℂ] fejerMollifierC := by
  funext x
  rw [convolution_def, fejerProfileC, fejerProfile, ← integral_complex_ofReal]
  simp only [ContinuousLinearMap.mul_apply', fejerIndicatorC, fejerMollifierC]
  push_cast; rfl

theorem fourier_fejerProfileC (ξ : ℝ) :
    𝓕 fejerProfileC ξ = 𝓕 fejerIndicatorC ξ * 𝓕 fejerMollifierC ξ := by
  rw [fejerProfileC_eq_convolution,
    Real.fourier_mul_convolution_eq integrable_fejerIndicatorC integrable_fejerMollifierC]

theorem norm_fourier_fejerMollifierC_le (ξ : ℝ) : ‖𝓕 fejerMollifierC ξ‖ ≤ 1 := by
  refine (norm_fourier_le_integral_norm _ ξ).trans (le_of_eq ?_)
  simp only [fejerMollifierC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fejerMollifier_nonneg _)]
  exact integral_fejerMollifier

theorem fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  rw [fourier_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp

theorem fourier_fejerMollifierC_zero : 𝓕 fejerMollifierC 0 = 1 := by
  rw [fourier_zero_eq_integral]
  simp only [fejerMollifierC]
  rw [integral_complex_ofReal, integral_fejerMollifier, Complex.ofReal_one]

theorem fourier_fejerIndicatorC_zero : 𝓕 fejerIndicatorC 0 = 2 * fejerHalfWidth := by
  rw [fourier_zero_eq_integral]
  simp only [fejerIndicatorC]
  rw [integral_complex_ofReal]
  have h : ∫ x, fejerIndicator x = 2 * fejerHalfWidth := by
    show ∫ x, (Icc (-fejerHalfWidth) fejerHalfWidth).indicator 1 x = _
    rw [integral_indicator_one measurableSet_Icc, Real.volume_real_Icc_of_le
      (by norm_num [fejerHalfWidth])]
    ring
  rw [h]; push_cast; ring

/-- **The Fejér test** `F = |𝓕ρ|²`. -/
def fejerTest (ξ : ℝ) : ℝ := Complex.normSq (𝓕 fejerProfileC ξ)

theorem fejerTest_nonneg (ξ : ℝ) : 0 ≤ fejerTest ξ := Complex.normSq_nonneg _

theorem fejerTest_zero : fejerTest 0 = (2 * fejerHalfWidth) ^ 2 := by
  rw [fejerTest, fourier_fejerProfileC, fourier_fejerIndicatorC_zero, fourier_fejerMollifierC_zero,
    mul_one, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.normSq_ofReal, sq]

theorem fejerTest_le {ξ : ℝ} (hξ : ξ ≠ 0) : fejerTest ξ ≤ 1 / (π * ξ) ^ 2 := by
  rw [fejerTest, Complex.normSq_eq_norm_sq, fourier_fejerProfileC, norm_mul]
  have h1 := norm_fourier_fejerIndicator_le hξ
  have h2 := norm_fourier_fejerMollifierC_le ξ
  have h3 : ‖𝓕 fejerIndicatorC ξ‖ * ‖𝓕 fejerMollifierC ξ‖ ≤ 1 / (π * |ξ|) :=
    (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans (by rw [mul_one])
  calc (‖𝓕 fejerIndicatorC ξ‖ * ‖𝓕 fejerMollifierC ξ‖) ^ 2 ≤ (1 / (π * |ξ|)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
    _ = 1 / (π * ξ) ^ 2 := by rw [div_pow, mul_pow, mul_pow, sq_abs, one_pow]

/-- The complex Fejér test. -/
def fejerTestC (ξ : ℝ) : ℂ := (fejerTest ξ : ℂ)

theorem fejerTestC_eq (ξ : ℝ) :
    fejerTestC ξ = 𝓕 fejerProfileC ξ * (starRingEnd ℂ) (𝓕 fejerProfileC ξ) := by
  rw [fejerTestC, fejerTest, Complex.mul_conj]

theorem contDiff_fourier_fejerProfileC : ContDiff ℝ ∞ (𝓕 fejerProfileC) := by
  refine Real.contDiff_fourier (fun n _ => ?_)
  refine ((continuous_norm.pow n).mul contDiff_fejerProfileC.continuous.norm
    ).integrable_of_hasCompactSupport ?_
  exact hasCompactSupport_fejerProfileC.norm.mul_left

theorem contDiff_fejerTestC : ContDiff ℝ ∞ fejerTestC := by
  have h : fejerTestC = fun ξ => 𝓕 fejerProfileC ξ * (starRingEnd ℂ) (𝓕 fejerProfileC ξ) :=
    funext fejerTestC_eq
  rw [h]
  exact contDiff_fourier_fejerProfileC.mul
    ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      contDiff_fourier_fejerProfileC)

theorem fejerTest_le_profile (ξ : ℝ) : fejerTest ξ ≤ 2 / (1 + ξ ^ 2) := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [fejerTest_zero]; norm_num [fejerHalfWidth]
  · have h := fejerTest_le hξ
    have hπ : (3 : ℝ) < π := Real.pi_gt_three
    rw [le_div_iff₀ (by positivity)]
    rcases le_or_gt (ξ ^ 2) 1 with hs | hs
    · -- small `ξ`: `F ≤ F(0)`-type bound through `|𝓕ρ| ≤ ∫|ρ| ≤ 2a`
      have hb : fejerTest ξ ≤ (2 * fejerHalfWidth) ^ 2 := by
        rw [fejerTest, Complex.normSq_eq_norm_sq, fourier_fejerProfileC, norm_mul]
        have h1 : ‖𝓕 fejerIndicatorC ξ‖ ≤ 2 * fejerHalfWidth := by
          refine (norm_fourier_le_integral_norm _ ξ).trans (le_of_eq ?_)
          simp only [fejerIndicatorC, Complex.norm_real, Real.norm_eq_abs]
          have : ∀ x, |fejerIndicator x| = fejerIndicator x := fun x => abs_of_nonneg (by
            simp only [fejerIndicator]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x)
          simp only [this]
          have := congrArg Complex.re fourier_fejerIndicatorC_zero
          rw [fourier_zero_eq_integral] at this
          simp only [fejerIndicatorC] at this
          rw [integral_complex_ofReal] at this
          simpa using this
        have h2 := norm_fourier_fejerMollifierC_le ξ
        have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by norm_num [fejerHalfWidth])
        rw [mul_one] at h3
        exact pow_le_pow_left₀ (by positivity) h3 2
      have : fejerTest ξ * (1 + ξ ^ 2) ≤ (2 * fejerHalfWidth) ^ 2 * 2 :=
        mul_le_mul hb (by linarith) (by positivity) (by positivity)
      nlinarith [show (2 * fejerHalfWidth) ^ 2 ≤ 1 by norm_num [fejerHalfWidth]]
    · have h' : fejerTest ξ * (π * ξ) ^ 2 ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at h; exact h
      have hF0 := fejerTest_nonneg ξ
      have hπ2 : 9 ≤ π ^ 2 := by nlinarith
      have h1 : fejerTest ξ * (1 + ξ ^ 2) ≤ 2 * (fejerTest ξ * ξ ^ 2) := by nlinarith
      have h2 : 9 * (fejerTest ξ * ξ ^ 2) ≤ fejerTest ξ * (π * ξ) ^ 2 := by
        rw [mul_pow]
        have : 0 ≤ fejerTest ξ * ξ ^ 2 := by positivity
        nlinarith
      linarith

theorem integrable_fejerTestC : Integrable fejerTestC := by
  refine (integrable_inv_one_add_sq.const_mul 2).mono' contDiff_fejerTestC.continuous.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [fejerTestC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerTest_nonneg ξ),
    ← div_eq_mul_inv]
  exact fejerTest_le_profile ξ

/-! ## The spectral gap of the Fejér test -/

theorem fourier_comp_add (f : ℝ → ℂ) (u ξ : ℝ) :
    𝓕 (fun x => f (x + u)) ξ = Complex.exp ((2 * π * ξ * u : ℝ) * I) * 𝓕 f ξ := by
  rw [fourier_eq_integral, fourier_eq_integral, ← integral_const_mul,
    ← integral_add_right_eq_self (μ := volume)
      (fun x => Complex.exp ((2 * π * ξ * u : ℝ) * I) *
        (Complex.exp (-(2 * π * x * ξ : ℝ) * I) * f x)) u]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- **Plancherel:** `𝓕F(u) = ∫ ρ(x) ρ(x + u) dx`. -/
theorem fourier_fejerTestC (u : ℝ) :
    𝓕 fejerTestC u = ∫ x, fejerProfileC x * (starRingEnd ℂ) (fejerProfileC (x + u)) := by
  have hψc : Continuous fun x => fejerProfileC (x + u) :=
    contDiff_fejerProfileC.continuous.comp (continuous_id.add continuous_const)
  have hψi : Integrable fun x => fejerProfileC (x + u) := integrable_fejerProfileC.comp_add_right u
  have hψs : ContDiff ℝ ∞ fun x => fejerProfileC (x + u) :=
    contDiff_fejerProfileC.comp (contDiff_id.add contDiff_const)
  have hψcs : HasCompactSupport fun x => fejerProfileC (x + u) :=
    hasCompactSupport_fejerProfileC.comp_homeomorph (Homeomorph.addRight u)
  have hFψ : Integrable (𝓕 fun x => fejerProfileC (x + u)) := integrable_fourier_smooth hψs hψcs
  rw [← GaloisForLFunctions.HTGeometry.plancherel_pairing integrable_fejerProfileC hψi hFψ hψc,
    fourier_eq_integral]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [fejerTestC_eq, fourier_comp_add]
  rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have e : Complex.exp (((2 * π * ξ * u : ℝ) : ℂ) * -I) =
      Complex.exp (-((2 * π * ξ * u : ℝ) : ℂ) * I) := by congr 1; ring
  rw [e]
  ring

/-- **Spectral gap.** `𝓕F(u) = 0` for `|u| > 17/25`. -/
theorem fourier_fejerTestC_eq_zero {u : ℝ} (hu : 17 / 25 < |u|) : 𝓕 fejerTestC u = 0 := by
  rw [fourier_fejerTestC]
  have h0 : (fun x => fejerProfileC x * (starRingEnd ℂ) (fejerProfileC (x + u))) =
      fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : 17 / 50 < |x|
    · simp [fejerProfileC, fejerProfile_eq_zero hx]
    · push Not at hx
      have : 17 / 50 < |x + u| := by
        have := abs_sub_abs_le_abs_sub u (-x)
        rw [sub_neg_eq_add, add_comm, abs_neg] at this
        linarith
      simp [fejerProfileC, fejerProfile_eq_zero this]
  rw [h0, integral_zero]

theorem seventeen_div_twentyfive_lt_log_two : (17 / 25 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- `𝓕F` vanishes at `±log n` for every `n ≥ 2`. -/
theorem fourier_fejerTestC_log_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    𝓕 fejerTestC (Real.log n) = 0 ∧ 𝓕 fejerTestC (-Real.log n) = 0 := by
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h2 := seventeen_div_twentyfive_lt_log_two
  have hpos : 0 < Real.log n := by linarith
  constructor
  · exact fourier_fejerTestC_eq_zero (by rw [abs_of_pos hpos]; linarith)
  · exact fourier_fejerTestC_eq_zero (by rw [abs_neg, abs_of_pos hpos]; linarith)

/-- **The zero budget of the Fejér test.** For every finite set of real zeros `t` of `Ξ`,
`Σ F(t/2π) ≤ 3/8 < F(0)`. -/
theorem sum_fejerTest_zeros_le (s : Finset ℝ) (hs : ∀ t ∈ s, XiC t = 0) :
    ∑ t ∈ s, fejerTest (t / (2 * π)) ≤ 3 / 8 := by
  refine le_trans (Finset.sum_le_sum fun t ht => ?_) (sum_four_div_sq_le s hs)
  have h45 := four_half_lt_abs_of_XiC_eq_zero (hs t ht)
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at h45; norm_num at h45
  have hξ : t / (2 * π) ≠ 0 := div_ne_zero ht0 (by positivity)
  refine (fejerTest_le hξ).trans (le_of_eq ?_)
  field_simp
  ring

theorem three_eighths_lt_fejerTest_zero : (3 / 8 : ℝ) < fejerTest 0 := by
  rw [fejerTest_zero]; norm_num [fejerHalfWidth]

end

end RHTower.WeilExcess
