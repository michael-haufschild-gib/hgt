import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHorizonAdmission
import GaloisForLFunctions.RHTower.RectangleCauchyFormula
import GaloisForLFunctions.RHTower.XiWeilCauchyLpContinuity
import GaloisForLFunctions.RHTower.XiGaussianTestFunction

/-!
# Reflected-Gaussian prime--Gamma Cauchy landing

The fixed reflected Meyer Gaussian is reconstructed from two literal Cauchy boundary lines in the
absolute-Euler prime--Gamma sectors.  The reconstruction is performed before restriction to the
Xi divisor.  After restriction, the two-sided boundary field is Bochner integrable in the exact
multiplicity-aware Xi `ell^(2 : ℕ)` carrier and its integral is the reflected-Gaussian horizon vector.

This constructs the nonlocal source completion forced by the compact Green range wall.  It uses no
RH premise, divisor-indexed damping, target-selected interpolation, or pulled-back source norm.
-/

open Complex Filter Set Topology MeasureTheory intervalIntegral
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- The centered Gaussian whose Xi-divisor restriction is the reflected Meyer horizon grade. -/
def reflectedGaussianCauchyProfile (z : ℂ) : ℂ :=
  Complex.exp (-(reflectedGaussianHorizonTime : ℂ) * z ^ 2)

/-- Exterior upper prime--Gamma Cauchy line. -/
def reflectedGaussianUpperCauchyPoint (x : ℝ) : XiCRegularPoint :=
  ⟨(x : ℂ) + Complex.I, by
    intro hzero
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hzero
    have him := congrArg Complex.im hq
    have hstrip := abs_im_xiSpectralPoint_lt_half q
    simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add] at him
    rw [him] at hstrip
    norm_num at hstrip⟩

/-- Exterior lower prime--Gamma Cauchy line. -/
def reflectedGaussianLowerCauchyPoint (x : ℝ) : XiCRegularPoint :=
  ⟨(x : ℂ) - Complex.I, by
    intro hzero
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hzero
    have him := congrArg Complex.im hq
    have hstrip := abs_im_xiSpectralPoint_lt_half q
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im, zero_sub] at him
    rw [him] at hstrip
    norm_num at hstrip⟩

/-- Multiplicity-exact Xi `ell^(2 : ℕ)` Cauchy column on the upper source boundary. -/
def reflectedGaussianUpperCauchyColumn (x : ℝ) : XiDivisorL2 :=
  xiWeilCauchyLp (reflectedGaussianUpperCauchyPoint x)

/-- Multiplicity-exact Xi `ell^(2 : ℕ)` Cauchy column on the lower source boundary. -/
def reflectedGaussianLowerCauchyColumn (x : ℝ) : XiDivisorL2 :=
  xiWeilCauchyLp (reflectedGaussianLowerCauchyPoint x)

@[simp]
theorem reflectedGaussianUpperCauchyColumn_apply (x : ℝ) (q : XiZeroCopy) :
    reflectedGaussianUpperCauchyColumn x q =
      (xiSpectralPoint q - ((x : ℂ) + Complex.I))⁻¹ := by
  rfl

@[simp]
theorem reflectedGaussianLowerCauchyColumn_apply (x : ℝ) (q : XiZeroCopy) :
    reflectedGaussianLowerCauchyColumn x q =
      (xiSpectralPoint q - ((x : ℂ) - Complex.I))⁻¹ := by
  rfl

/-- Two-sided source boundary field, normalized with the positive rectangle orientation. -/
def reflectedGaussianPrimeGammaCauchyBoundary (x : ℝ) : XiDivisorL2 :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    (reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) •
        reflectedGaussianUpperCauchyColumn x -
      reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) •
        reflectedGaussianLowerCauchyColumn x)

@[simp]
theorem reflectedGaussianPrimeGammaCauchyBoundary_apply
    (x : ℝ) (q : XiZeroCopy) :
    reflectedGaussianPrimeGammaCauchyBoundary x q =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) *
            (xiSpectralPoint q - ((x : ℂ) + Complex.I))⁻¹ -
          reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) *
            (xiSpectralPoint q - ((x : ℂ) - Complex.I))⁻¹) := by
  rfl

theorem norm_reflectedGaussianCauchyProfile_upper (x : ℝ) :
    ‖reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I)‖ =
      Real.exp reflectedGaussianHorizonTime *
        Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) := by
  rw [reflectedGaussianCauchyProfile, Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, pow_two, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, add_zero, zero_add]
  ring

theorem norm_reflectedGaussianCauchyProfile_lower (x : ℝ) :
    ‖reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I)‖ =
      Real.exp reflectedGaussianHorizonTime *
        Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) := by
  rw [reflectedGaussianCauchyProfile, Complex.norm_exp]
  rw [← Real.exp_add]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, pow_two, Complex.sub_re,
    Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero, zero_sub]
  ring

private theorem half_lt_norm_sub_upper
    {a : ℂ} (ha : |a.im| < 1 / 2) (x : ℝ) :
    (1 / 2 : ℝ) < ‖a - ((x : ℂ) + Complex.I)‖ := by
  have him := Complex.abs_im_le_norm (a - ((x : ℂ) + Complex.I))
  have haUpper := (abs_lt.mp ha).2
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
    Complex.I_im, zero_add] at him
  rw [abs_of_neg (by linarith)] at him
  linarith

private theorem half_lt_norm_sub_lower
    {a : ℂ} (ha : |a.im| < 1 / 2) (x : ℝ) :
    (1 / 2 : ℝ) < ‖a - ((x : ℂ) - Complex.I)‖ := by
  have him := Complex.abs_im_le_norm (a - ((x : ℂ) - Complex.I))
  have haLower := (abs_lt.mp ha).1
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.I_im,
    zero_sub] at him
  rw [abs_of_pos (by linarith)] at him
  linarith

theorem integrable_reflectedGaussianCauchyProfile_mul_upper
    {a : ℂ} (ha : |a.im| < 1 / 2) :
    Integrable (fun x : ℝ =>
      reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) *
        (a - ((x : ℂ) + Complex.I))⁻¹) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq reflectedGaussianHorizonTime_pos).const_mul
      (2 * Real.exp reflectedGaussianHorizonTime))
  · have hprofile : Continuous (fun x : ℝ =>
        reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I)) := by
      unfold reflectedGaussianCauchyProfile
      fun_prop
    have hdenom : Continuous (fun x : ℝ =>
        a - ((x : ℂ) + Complex.I)) := by fun_prop
    have hne : ∀ x : ℝ, a - ((x : ℂ) + Complex.I) ≠ 0 := by
      intro x hx
      have h := half_lt_norm_sub_upper ha x
      rw [hx, norm_zero] at h
      norm_num at h
    exact (hprofile.mul (hdenom.inv₀ hne)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, norm_inv, norm_reflectedGaussianCauchyProfile_upper]
    have hden := half_lt_norm_sub_upper ha x
    have hinv : ‖a - ((x : ℂ) + Complex.I)‖⁻¹ ≤ 2 := by
      calc
        ‖a - ((x : ℂ) + Complex.I)‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) hden.le
        _ = 2 := by norm_num
    calc
      Real.exp reflectedGaussianHorizonTime *
            Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) *
          ‖a - ((x : ℂ) + Complex.I)‖⁻¹ ≤
        Real.exp reflectedGaussianHorizonTime *
            Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * x ^ 2) := by
            rw [neg_mul]
            ring

theorem integrable_reflectedGaussianCauchyProfile_mul_lower
    {a : ℂ} (ha : |a.im| < 1 / 2) :
    Integrable (fun x : ℝ =>
      reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) *
        (a - ((x : ℂ) - Complex.I))⁻¹) := by
  apply Integrable.mono'
    ((integrable_exp_neg_mul_sq reflectedGaussianHorizonTime_pos).const_mul
      (2 * Real.exp reflectedGaussianHorizonTime))
  · have hprofile : Continuous (fun x : ℝ =>
        reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I)) := by
      unfold reflectedGaussianCauchyProfile
      fun_prop
    have hdenom : Continuous (fun x : ℝ =>
        a - ((x : ℂ) - Complex.I)) := by fun_prop
    have hne : ∀ x : ℝ, a - ((x : ℂ) - Complex.I) ≠ 0 := by
      intro x hx
      have h := half_lt_norm_sub_lower ha x
      rw [hx, norm_zero] at h
      norm_num at h
    exact (hprofile.mul (hdenom.inv₀ hne)).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, norm_inv, norm_reflectedGaussianCauchyProfile_lower]
    have hden := half_lt_norm_sub_lower ha x
    have hinv : ‖a - ((x : ℂ) - Complex.I)‖⁻¹ ≤ 2 := by
      calc
        ‖a - ((x : ℂ) - Complex.I)‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
          inv_anti₀ (by norm_num) hden.le
        _ = 2 := by norm_num
    calc
      Real.exp reflectedGaussianHorizonTime *
            Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) *
          ‖a - ((x : ℂ) - Complex.I)‖⁻¹ ≤
        Real.exp reflectedGaussianHorizonTime *
            Real.exp (-(reflectedGaussianHorizonTime * x ^ 2)) * 2 :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 * Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * x ^ 2) := by
            rw [neg_mul]
            ring

private theorem norm_reflectedGaussianCauchyProfile_vertical (x y : ℝ) :
    ‖reflectedGaussianCauchyProfile ((x : ℂ) + (y : ℂ) * Complex.I)‖ =
      Real.exp (-reflectedGaussianHorizonTime * x ^ 2 +
        reflectedGaussianHorizonTime * y ^ 2) := by
  rw [reflectedGaussianCauchyProfile, Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, pow_two, Complex.add_re, Complex.add_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, add_zero, zero_mul, zero_add]
  ring

private theorem tendsto_reflectedGaussianCauchyProfile_vertical_right
    (a : ℂ) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in (-1)..1,
      reflectedGaussianCauchyProfile ((R : ℂ) + (y : ℂ) * Complex.I) *
        (((R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹)
      atTop (nhds 0) := by
  have hexp0 : Tendsto
      (fun R : ℝ => Real.exp (-reflectedGaussianHorizonTime * R ^ 2))
      atTop (nhds 0) := by
    simpa using tendsto_polyGaussian_atTop
      reflectedGaussianHorizonTime_pos 0 0
  have hmajor : Tendsto (fun R : ℝ =>
      (2 * Real.exp reflectedGaussianHorizonTime) *
        Real.exp (-reflectedGaussianHorizonTime * R ^ 2))
      atTop (nhds 0) := by
    simpa using hexp0.const_mul (2 * Real.exp reflectedGaussianHorizonTime)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (|a.re| + 1)] with R hR
  have hpoint : ∀ y ∈ Set.uIoc (-1 : ℝ) 1,
      ‖reflectedGaussianCauchyProfile ((R : ℂ) + (y : ℂ) * Complex.I) *
          (((R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹‖ ≤
        Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by
    intro y hy
    have hy' : -1 ≤ y ∧ y ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact ⟨hy.1.le, hy.2⟩
    have hySq : y ^ 2 ≤ 1 := by nlinarith
    have hreal : 1 ≤
        |(((R : ℂ) + (y : ℂ) * Complex.I) - a).re| := by
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [abs_of_nonneg]
      · linarith [le_abs_self a.re]
      · linarith [le_abs_self a.re]
    have hden : 1 ≤ ‖((R : ℂ) + (y : ℂ) * Complex.I) - a‖ :=
      hreal.trans (Complex.abs_re_le_norm _)
    rw [norm_mul, norm_inv, norm_reflectedGaussianCauchyProfile_vertical]
    have hinv : ‖((R : ℂ) + (y : ℂ) * Complex.I) - a‖⁻¹ ≤ 1 := by
      simpa using inv_le_one_of_one_le₀ hden
    calc
      Real.exp (-reflectedGaussianHorizonTime * R ^ 2 +
          reflectedGaussianHorizonTime * y ^ 2) *
          ‖((R : ℂ) + (y : ℂ) * Complex.I) - a‖⁻¹ ≤
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2 +
            reflectedGaussianHorizonTime * y ^ 2) := by
              simpa using mul_le_of_le_one_right (Real.exp_nonneg _) hinv
      _ ≤ Real.exp (-reflectedGaussianHorizonTime * R ^ 2 +
          reflectedGaussianHorizonTime) := by
            apply Real.exp_le_exp.mpr
            have hmul :=
              mul_le_mul_of_nonneg_left hySq reflectedGaussianHorizonTime_pos.le
            nlinarith
      _ = Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
  calc
    ‖∫ y : ℝ in (-1)..1,
        reflectedGaussianCauchyProfile ((R : ℂ) + (y : ℂ) * Complex.I) *
          (((R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹‖ ≤
        (Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2)) * |(1 : ℝ) - (-1)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * Real.exp reflectedGaussianHorizonTime) *
        Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by ring

private theorem tendsto_reflectedGaussianCauchyProfile_vertical_left
    (a : ℂ) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in (-1)..1,
      reflectedGaussianCauchyProfile ((-R : ℂ) + (y : ℂ) * Complex.I) *
        (((-R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹)
      atTop (nhds 0) := by
  have hexp0 : Tendsto
      (fun R : ℝ => Real.exp (-reflectedGaussianHorizonTime * R ^ 2))
      atTop (nhds 0) := by
    simpa using tendsto_polyGaussian_atTop
      reflectedGaussianHorizonTime_pos 0 0
  have hmajor : Tendsto (fun R : ℝ =>
      (2 * Real.exp reflectedGaussianHorizonTime) *
        Real.exp (-reflectedGaussianHorizonTime * R ^ 2))
      atTop (nhds 0) := by
    simpa using hexp0.const_mul (2 * Real.exp reflectedGaussianHorizonTime)
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (|a.re| + 1)] with R hR
  have hpoint : ∀ y ∈ Set.uIoc (-1 : ℝ) 1,
      ‖reflectedGaussianCauchyProfile ((-R : ℂ) + (y : ℂ) * Complex.I) *
          (((-R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹‖ ≤
        Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by
    intro y hy
    have hy' : -1 ≤ y ∧ y ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num)] at hy
      exact ⟨hy.1.le, hy.2⟩
    have hySq : y ^ 2 ≤ 1 := by nlinarith
    have hreal : 1 ≤
        |(((-R : ℂ) + (y : ℂ) * Complex.I) - a).re| := by
      simp only [Complex.sub_re, Complex.add_re, Complex.neg_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [abs_of_nonpos]
      · linarith [neg_abs_le a.re]
      · linarith [neg_abs_le a.re]
    have hden : 1 ≤ ‖((-R : ℂ) + (y : ℂ) * Complex.I) - a‖ :=
      hreal.trans (Complex.abs_re_le_norm _)
    rw [norm_mul, norm_inv]
    have hprofile :
        ‖reflectedGaussianCauchyProfile ((-R : ℂ) + (y : ℂ) * Complex.I)‖ =
          Real.exp (-reflectedGaussianHorizonTime * (-R) ^ 2 +
            reflectedGaussianHorizonTime * y ^ 2) := by
      simpa only [Complex.ofReal_neg] using
        norm_reflectedGaussianCauchyProfile_vertical (-R) y
    rw [hprofile]
    have hinv : ‖((-R : ℂ) + (y : ℂ) * Complex.I) - a‖⁻¹ ≤ 1 := by
      simpa using inv_le_one_of_one_le₀ hden
    calc
      Real.exp (-reflectedGaussianHorizonTime * (-R) ^ 2 +
          reflectedGaussianHorizonTime * y ^ 2) *
          ‖((-R : ℂ) + (y : ℂ) * Complex.I) - a‖⁻¹ ≤
          Real.exp (-reflectedGaussianHorizonTime * (-R) ^ 2 +
            reflectedGaussianHorizonTime * y ^ 2) := by
              simpa using mul_le_of_le_one_right (Real.exp_nonneg _) hinv
      _ ≤ Real.exp (-reflectedGaussianHorizonTime * R ^ 2 +
          reflectedGaussianHorizonTime) := by
            rw [neg_sq]
            apply Real.exp_le_exp.mpr
            have hmul :=
              mul_le_mul_of_nonneg_left hySq reflectedGaussianHorizonTime_pos.le
            nlinarith
      _ = Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
  calc
    ‖∫ y : ℝ in (-1)..1,
        reflectedGaussianCauchyProfile ((-R : ℂ) + (y : ℂ) * Complex.I) *
          (((-R : ℂ) + (y : ℂ) * Complex.I) - a)⁻¹‖ ≤
        (Real.exp reflectedGaussianHorizonTime *
          Real.exp (-reflectedGaussianHorizonTime * R ^ 2)) * |(1 : ℝ) - (-1)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * Real.exp reflectedGaussianHorizonTime) *
        Real.exp (-reflectedGaussianHorizonTime * R ^ 2) := by ring

/-- Cauchy's formula on the two exterior source lines.  The coefficient is fixed by the source
Gaussian; the theorem applies to every point in the full unconditional Xi spectral strip. -/
theorem integral_reflectedGaussian_twoSidedCauchyBoundary
    {a : ℂ} (ha : |a.im| < 1 / 2) :
    (∫ x : ℝ, reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) *
        (a - ((x : ℂ) + Complex.I))⁻¹) -
      (∫ x : ℝ, reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) *
        (a - ((x : ℂ) - Complex.I))⁻¹) =
      2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a := by
  let F : ℂ → ℂ := fun z => reflectedGaussianCauchyProfile z * (z - a)⁻¹
  have hprofileDiff : Differentiable ℂ reflectedGaussianCauchyProfile := by
    unfold reflectedGaussianCauchyProfile
    fun_prop
  have hprofileAnalytic :
      AnalyticOnNhd ℂ reflectedGaussianCauchyProfile Set.univ :=
    hprofileDiff.differentiableOn.analyticOnNhd isOpen_univ
  have hrect : ∀ R : ℝ, |a.re| + 1 ≤ R →
      rectIntegral F ((-R : ℂ) - Complex.I) ((R : ℂ) + Complex.I) =
        2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a := by
    intro R hR
    apply rectIntegral_cauchyFormula_entire hprofileAnalytic
    · simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re,
        Complex.I_re, sub_zero]
      linarith [neg_abs_le a.re]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      linarith [le_abs_self a.re]
    · simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im,
        Complex.I_im, neg_zero, zero_sub]
      linarith [(abs_lt.mp ha).1]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
      linarith [(abs_lt.mp ha).2]
  have hbottomInt : Integrable (fun x : ℝ => F ((x : ℂ) - Complex.I)) := by
    have h := (integrable_reflectedGaussianCauchyProfile_mul_lower ha).neg
    apply h.congr
    filter_upwards with x
    simp only [Pi.neg_apply]
    dsimp only [F]
    rw [show ((x : ℂ) - Complex.I) - a =
      -(a - ((x : ℂ) - Complex.I)) by ring, inv_neg, mul_neg]
  have htopInt : Integrable (fun x : ℝ => F ((x : ℂ) + Complex.I)) := by
    have h := (integrable_reflectedGaussianCauchyProfile_mul_upper ha).neg
    apply h.congr
    filter_upwards with x
    simp only [Pi.neg_apply]
    dsimp only [F]
    rw [show ((x : ℂ) + Complex.I) - a =
      -(a - ((x : ℂ) + Complex.I)) by ring, inv_neg, mul_neg]
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral hbottomInt
    tendsto_neg_atTop_atBot tendsto_id
  have htop := MeasureTheory.intervalIntegral_tendsto_integral htopInt
    tendsto_neg_atTop_atBot tendsto_id
  have hright := tendsto_reflectedGaussianCauchyProfile_vertical_right a
  have hleft := tendsto_reflectedGaussianCauchyProfile_vertical_left a
  have hlim := ((hbottom.sub htop).add (hright.const_smul Complex.I)).sub
    (hleft.const_smul Complex.I)
  have heventually : ∀ᶠ R : ℝ in atTop,
      rectIntegral F ((-R : ℂ) - Complex.I) ((R : ℂ) + Complex.I) =
        2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a := by
    filter_upwards [eventually_ge_atTop (|a.re| + 1)] with R hR
    exact hrect R hR
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F ((-R : ℂ) - Complex.I) ((R : ℂ) + Complex.I))
      atTop (nhds ((∫ x : ℝ, F ((x : ℂ) - Complex.I)) -
        (∫ x : ℝ, F ((x : ℂ) + Complex.I)))) := by
    simpa [rectIntegral, F, sub_eq_add_neg] using hlim
  have hconst : Tendsto (fun _ : ℝ =>
      2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a)
      atTop (nhds (2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a)) :=
    tendsto_const_nhds
  have heventually' : ∀ᶠ R : ℝ in atTop,
      2 * Real.pi * Complex.I * reflectedGaussianCauchyProfile a =
        rectIntegral F ((-R : ℂ) - Complex.I) ((R : ℂ) + Complex.I) :=
    heventually.mono fun _ h => h.symm
  have htarget := tendsto_nhds_unique hlim' (hconst.congr' heventually')
  have hupper :
      (∫ x : ℝ, reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) *
        (a - ((x : ℂ) + Complex.I))⁻¹) =
      -(∫ x : ℝ, F ((x : ℂ) + Complex.I)) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [F]
    rw [show a - ((x : ℂ) + Complex.I) =
      -(((x : ℂ) + Complex.I) - a) by ring, inv_neg]
    ring
  have hlower :
      (∫ x : ℝ, reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) *
        (a - ((x : ℂ) - Complex.I))⁻¹) =
      -(∫ x : ℝ, F ((x : ℂ) - Complex.I)) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [F]
    rw [show a - ((x : ℂ) - Complex.I) =
      -(((x : ℂ) - Complex.I) - a) by ring, inv_neg]
    ring
  rw [hupper, hlower]
  linear_combination htarget

/-- Finite unconditional reciprocal-square mass of the complete Xi divisor. -/
def xiDivisorReciprocalSquareMass : ℝ :=
  ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

theorem xiDivisorReciprocalSquareMass_nonneg :
    0 ≤ xiDivisorReciprocalSquareMass := by
  unfold xiDivisorReciprocalSquareMass
  exact tsum_nonneg fun _ => by positivity

/-- A Cauchy column separated by half a unit from the divisor has at most polynomial pole growth,
with the constant measured by the canonical reciprocal-square divisor mass. -/
theorem norm_sq_xiWeilCauchyLp_le_of_half_le
    (z : XiCRegularPoint)
    (hsep : ∀ q : XiZeroCopy,
      (1 / 2 : ℝ) ≤ ‖xiSpectralPoint q - (z : ℂ)‖) :
    ‖xiWeilCauchyLp z‖ ^ 2 ≤
      (2 * (1 + ‖(z : ℂ)‖)) ^ 2 * xiDivisorReciprocalSquareMass := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  have hleft : Summable (fun q : XiZeroCopy =>
      ‖xiWeilCauchyLp z q‖ ^ 2) :=
    XiWeilSquareSummable_cauchy (z : ℂ)
  have hright : Summable (fun q : XiZeroCopy =>
      (2 * (1 + ‖(z : ℂ)‖)) ^ 2 *
        (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  calc
    (∑' q : XiZeroCopy, ‖xiWeilCauchyLp z q‖ ^ 2) ≤
        ∑' q : XiZeroCopy,
          (2 * (1 + ‖(z : ℂ)‖)) ^ 2 *
            (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      exact hleft.tsum_le_tsum (fun q => by
        have hlam : 0 < ‖xiSpectralPoint q‖ :=
          norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
        have hden : 0 < ‖xiSpectralPoint q - (z : ℂ)‖ :=
          lt_of_lt_of_le (by norm_num) (hsep q)
        have htri : ‖xiSpectralPoint q‖ ≤
            ‖xiSpectralPoint q - (z : ℂ)‖ + ‖(z : ℂ)‖ := by
          simpa using norm_add_le
            (xiSpectralPoint q - (z : ℂ)) (z : ℂ)
        have hscale : ‖xiSpectralPoint q‖ ≤
            (2 * (1 + ‖(z : ℂ)‖)) *
              ‖xiSpectralPoint q - (z : ℂ)‖ := by
          have hznonneg := norm_nonneg (z : ℂ)
          have hdenNonneg := norm_nonneg (xiSpectralPoint q - (z : ℂ))
          have htwo : 1 ≤ 2 * ‖xiSpectralPoint q - (z : ℂ)‖ := by
            linarith [hsep q]
          calc
            ‖xiSpectralPoint q‖ ≤
                ‖xiSpectralPoint q - (z : ℂ)‖ + ‖(z : ℂ)‖ := htri
            _ ≤ 2 * ‖xiSpectralPoint q - (z : ℂ)‖ +
                ‖(z : ℂ)‖ * (2 * ‖xiSpectralPoint q - (z : ℂ)‖) := by
              exact add_le_add (by linarith)
                (le_mul_of_one_le_right hznonneg htwo)
            _ = (2 * (1 + ‖(z : ℂ)‖)) *
                ‖xiSpectralPoint q - (z : ℂ)‖ := by ring
        have hinv : ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ ≤
            (2 * (1 + ‖(z : ℂ)‖)) /
              ‖xiSpectralPoint q‖ := by
          rw [inv_eq_one_div]
          exact (div_le_div_iff₀ hden hlam).2 (by simpa using hscale)
        have hsq := pow_le_pow_left₀ (by positivity) hinv 2
        have hcolumn : ‖xiWeilCauchyLp z q‖ =
            ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ := by
          change ‖(xiSpectralPoint q - (z : ℂ))⁻¹‖ = _
          rw [norm_inv]
        rw [hcolumn]
        calc
          ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ ^ 2 ≤
              ((2 * (1 + ‖(z : ℂ)‖)) /
                ‖xiSpectralPoint q‖) ^ 2 := hsq
          _ = (2 * (1 + ‖(z : ℂ)‖)) ^ 2 *
              (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring)
        hright
    _ = (2 * (1 + ‖(z : ℂ)‖)) ^ 2 *
        xiDivisorReciprocalSquareMass := by
      rw [tsum_mul_left]
      rfl

theorem continuous_reflectedGaussianUpperCauchyColumn :
    Continuous reflectedGaussianUpperCauchyColumn := by
  rw [continuous_iff_seqContinuous]
  intro u x hu
  apply tendsto_xiWeilCauchyLp
  have hreal := Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  simpa [reflectedGaussianUpperCauchyPoint] using hreal.add_const Complex.I

theorem continuous_reflectedGaussianLowerCauchyColumn :
    Continuous reflectedGaussianLowerCauchyColumn := by
  rw [continuous_iff_seqContinuous]
  intro u x hu
  apply tendsto_xiWeilCauchyLp
  have hreal := Complex.continuous_ofReal.continuousAt.tendsto.comp hu
  simpa [reflectedGaussianLowerCauchyPoint] using hreal.sub_const Complex.I

private theorem norm_reflectedGaussianCauchyColumn_le
    (x : ℝ) (z : XiCRegularPoint)
    (hz : ‖(z : ℂ)‖ ≤ |x| + 1)
    (hsep : ∀ q : XiZeroCopy,
      (1 / 2 : ℝ) ≤ ‖xiSpectralPoint q - (z : ℂ)‖) :
    ‖xiWeilCauchyLp z‖ ≤
      (2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1 := by
  have hsq := norm_sq_xiWeilCauchyLp_le_of_half_le z hsep
  have hself : ‖xiWeilCauchyLp z‖ ≤ ‖xiWeilCauchyLp z‖ ^ 2 + 1 := by
    nlinarith [sq_nonneg (‖xiWeilCauchyLp z‖ - 1 / 2)]
  have hfactor : 0 ≤ 2 * (1 + ‖(z : ℂ)‖) := by positivity
  have hfactor' : 2 * (1 + ‖(z : ℂ)‖) ≤ 2 * (2 + |x|) := by
    linarith
  have hpow : (2 * (1 + ‖(z : ℂ)‖)) ^ 2 ≤
      (2 * (2 + |x|)) ^ 2 :=
    pow_le_pow_left₀ hfactor hfactor' 2
  calc
    ‖xiWeilCauchyLp z‖ ≤ ‖xiWeilCauchyLp z‖ ^ 2 + 1 := hself
    _ ≤ (2 * (1 + ‖(z : ℂ)‖)) ^ 2 *
        xiDivisorReciprocalSquareMass + 1 := by gcongr
    _ ≤ (2 * (2 + |x|)) ^ 2 *
        xiDivisorReciprocalSquareMass + 1 := by
      gcongr
      exact xiDivisorReciprocalSquareMass_nonneg

theorem norm_reflectedGaussianUpperCauchyColumn_le (x : ℝ) :
    ‖reflectedGaussianUpperCauchyColumn x‖ ≤
      (2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1 := by
  apply norm_reflectedGaussianCauchyColumn_le x
      (reflectedGaussianUpperCauchyPoint x)
  · dsimp only [reflectedGaussianUpperCauchyPoint]
    calc
      ‖(x : ℂ) + Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖Complex.I‖ := norm_add_le _ _
      _ = |x| + 1 := by simp
  · intro q
    exact (half_lt_norm_sub_upper (abs_im_xiSpectralPoint_lt_half q) x).le

theorem norm_reflectedGaussianLowerCauchyColumn_le (x : ℝ) :
    ‖reflectedGaussianLowerCauchyColumn x‖ ≤
      (2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1 := by
  apply norm_reflectedGaussianCauchyColumn_le x
      (reflectedGaussianLowerCauchyPoint x)
  · dsimp only [reflectedGaussianLowerCauchyPoint]
    calc
      ‖(x : ℂ) - Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
      _ = |x| + 1 := by simp
  · intro q
    exact (half_lt_norm_sub_lower (abs_im_xiSpectralPoint_lt_half q) x).le

theorem continuous_reflectedGaussianPrimeGammaCauchyBoundary :
    Continuous reflectedGaussianPrimeGammaCauchyBoundary := by
  unfold reflectedGaussianPrimeGammaCauchyBoundary
  have hprofileUpper : Continuous (fun x : ℝ =>
      reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I)) := by
    unfold reflectedGaussianCauchyProfile
    fun_prop
  have hprofileLower : Continuous (fun x : ℝ =>
      reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I)) := by
    unfold reflectedGaussianCauchyProfile
    fun_prop
  have hconstant : Continuous (fun _ : ℝ =>
      (2 * Real.pi * Complex.I : ℂ)⁻¹) := continuous_const
  exact hconstant.smul
    ((hprofileUpper.smul continuous_reflectedGaussianUpperCauchyColumn).sub
      (hprofileLower.smul continuous_reflectedGaussianLowerCauchyColumn))

private def reflectedGaussianPrimeGammaCauchyMajorant (x : ℝ) : ℝ :=
  (2 * ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
      Real.exp reflectedGaussianHorizonTime) *
    Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
      ((32 + 8 * x ^ 2) * xiDivisorReciprocalSquareMass + 1)

private theorem integrable_reflectedGaussianPrimeGammaCauchyMajorant :
    Integrable reflectedGaussianPrimeGammaCauchyMajorant := by
  let A : ℝ := 2 * ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
    Real.exp reflectedGaussianHorizonTime
  let S : ℝ := xiDivisorReciprocalSquareMass
  have hzero := (integrable_exp_neg_mul_sq
    reflectedGaussianHorizonTime_pos).const_mul (A * (32 * S + 1))
  have htwoBase : Integrable (fun x : ℝ =>
      x ^ 2 * Real.exp (-reflectedGaussianHorizonTime * x ^ 2)) := by
    simpa [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq
        reflectedGaussianHorizonTime_pos (by norm_num : (-1 : ℝ) < 2))
  have htwo := htwoBase.const_mul (A * (8 * S))
  have hadd := hzero.add htwo
  apply hadd.congr
  filter_upwards with x
  change
    A * (32 * S + 1) *
          Real.exp (-reflectedGaussianHorizonTime * x ^ 2) +
        A * (8 * S) *
          (x ^ 2 * Real.exp (-reflectedGaussianHorizonTime * x ^ 2)) =
      A * Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
        ((32 + 8 * x ^ 2) * S + 1)
  ring

private theorem norm_reflectedGaussianPrimeGammaCauchyBoundary_le_majorant
    (x : ℝ) :
    ‖reflectedGaussianPrimeGammaCauchyBoundary x‖ ≤
      reflectedGaussianPrimeGammaCauchyMajorant x := by
  have hpolyBase : (2 * (2 + |x|)) ^ 2 ≤ 32 + 8 * x ^ 2 := by
    have habsSq : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [sq_nonneg (|x| - 2)]
  have hpoly :
      (2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1 ≤
        (32 + 8 * x ^ 2) * xiDivisorReciprocalSquareMass + 1 := by
    gcongr
    exact xiDivisorReciprocalSquareMass_nonneg
  have hupper := norm_reflectedGaussianUpperCauchyColumn_le x
  have hlower := norm_reflectedGaussianLowerCauchyColumn_le x
  unfold reflectedGaussianPrimeGammaCauchyBoundary
  rw [norm_smul]
  calc
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ‖reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) •
            reflectedGaussianUpperCauchyColumn x -
          reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) •
            reflectedGaussianLowerCauchyColumn x‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        (‖reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) •
            reflectedGaussianUpperCauchyColumn x‖ +
          ‖reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) •
            reflectedGaussianLowerCauchyColumn x‖) := by
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ = ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        (Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ‖reflectedGaussianUpperCauchyColumn x‖ +
          Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ‖reflectedGaussianLowerCauchyColumn x‖) := by
        rw [norm_smul, norm_smul,
          norm_reflectedGaussianCauchyProfile_upper,
          norm_reflectedGaussianCauchyProfile_lower, neg_mul]
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        (Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ((2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1) +
          Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ((2 * (2 + |x|)) ^ 2 * xiDivisorReciprocalSquareMass + 1)) := by
        gcongr
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        (Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ((32 + 8 * x ^ 2) * xiDivisorReciprocalSquareMass + 1) +
          Real.exp reflectedGaussianHorizonTime *
            Real.exp (-reflectedGaussianHorizonTime * x ^ 2) *
              ((32 + 8 * x ^ 2) * xiDivisorReciprocalSquareMass + 1)) := by
        gcongr
    _ = reflectedGaussianPrimeGammaCauchyMajorant x := by
      unfold reflectedGaussianPrimeGammaCauchyMajorant
      ring

/-- The two-sided prime--Gamma boundary field is genuinely Bochner integrable in the completed,
multiplicity-aware Xi divisor Hilbert space. -/
theorem integrable_reflectedGaussianPrimeGammaCauchyBoundary :
    Integrable reflectedGaussianPrimeGammaCauchyBoundary := by
  apply Integrable.mono' integrable_reflectedGaussianPrimeGammaCauchyMajorant
  · exact continuous_reflectedGaussianPrimeGammaCauchyBoundary.aestronglyMeasurable
  · filter_upwards with x
    exact norm_reflectedGaussianPrimeGammaCauchyBoundary_le_majorant x

theorem integral_reflectedGaussianPrimeGammaCauchyBoundary_apply
    (q : XiZeroCopy) :
    (∫ x : ℝ, reflectedGaussianPrimeGammaCauchyBoundary x) q =
      reflectedGaussianCauchyProfile (xiSpectralPoint q) := by
  let E : XiDivisorL2 →L[ℂ] ℂ :=
    lp.evalCLM ℂ (fun _ : XiZeroCopy => ℂ) 2 q
  have heval := E.integral_comp_comm
    integrable_reflectedGaussianPrimeGammaCauchyBoundary
  change E (∫ x : ℝ, reflectedGaussianPrimeGammaCauchyBoundary x) = _
  rw [← heval]
  change (∫ x : ℝ, reflectedGaussianPrimeGammaCauchyBoundary x q) = _
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  have hupper := integrable_reflectedGaussianCauchyProfile_mul_upper hstrip
  have hlower := integrable_reflectedGaussianCauchyProfile_mul_lower hstrip
  have hfun : (fun x : ℝ => reflectedGaussianPrimeGammaCauchyBoundary x q) =
      fun x : ℝ => (2 * Real.pi * Complex.I : ℂ)⁻¹ *
        (reflectedGaussianCauchyProfile ((x : ℂ) + Complex.I) *
            (xiSpectralPoint q - ((x : ℂ) + Complex.I))⁻¹ -
          reflectedGaussianCauchyProfile ((x : ℂ) - Complex.I) *
            (xiSpectralPoint q - ((x : ℂ) - Complex.I))⁻¹) := by
    funext x
    exact reflectedGaussianPrimeGammaCauchyBoundary_apply x q
  rw [hfun, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub hupper hlower,
    integral_reflectedGaussian_twoSidedCauchyBoundary hstrip]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- **Unconditional source-to-Xi landing.**  The Bochner integral of the literal two-sided
absolute-Euler prime--Gamma Cauchy boundary is exactly the fixed reflected Meyer Gaussian horizon
grade in the complete multiplicity-aware Xi divisor Hilbert space. -/
theorem integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2 :
    (∫ x : ℝ, reflectedGaussianPrimeGammaCauchyBoundary x) =
      reflectedGaussianHorizonGradeL2 := by
  ext q
  rw [integral_reflectedGaussianPrimeGammaCauchyBoundary_apply,
    reflectedGaussianHorizonGradeL2_apply,
    reflectedGaussianHorizonGrade_eq_heat]
  rfl

end

end DeningerMeyerGaussianGreen
end RHTower
