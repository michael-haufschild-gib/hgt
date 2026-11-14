import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# The Selberg small-gap kernel

The nonnegative Fourier profile gives the sharp upper bound one. An explicit
antiderivative identifies the transform away from its removable singularities,
where its sign detects pairs at distance at most one.
-/

open Real Set MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.TransThresholdPairCorrelation
noncomputable section

/-- The positive half of the compact Fourier profile. -/
def selbergProfile (u : ℝ) : ℝ := 1 - u + sin (2 * π * u) / (2 * π)

private theorem continuous_selbergProfile : Continuous selbergProfile := by
  unfold selbergProfile
  fun_prop

/-- The Fourier profile is nonnegative throughout its support. -/
theorem selbergProfile_nonneg (u : Icc (0 : ℝ) 1) : 0 ≤ selbergProfile u := by
  have hp : 0 < 2 * π := by positivity
  have hv : 0 ≤ 2 * π * (1 - (u : ℝ)) := mul_nonneg hp.le (sub_nonneg.mpr u.2.2)
  have hs := Real.abs_sin_le_abs (x := 2 * π * (1 - (u : ℝ)))
  rw [abs_of_nonneg hv] at hs
  have he : sin (2 * π * (1 - (u : ℝ))) = -sin (2 * π * (u : ℝ)) := by
    rw [show 2 * π * (1 - (u : ℝ)) = 2 * π - 2 * π * (u : ℝ) by ring,
      sin_sub, sin_two_pi, cos_two_pi]
    ring
  rw [he, abs_neg] at hs
  have hlow := (abs_le.mp hs).1
  have hdiv : -(1 - (u : ℝ)) ≤ sin (2 * π * (u : ℝ)) / (2 * π) :=
    (le_div_iff₀ hp).2 (by nlinarith only [hlow])
  unfold selbergProfile
  linarith only [hdiv]

private theorem selbergProfile_primitive (u : ℝ) :
    HasDerivAt (fun v : ℝ => v - v ^ 2 / 2 - cos (2 * π * v) / (2 * π) ^ 2)
      (selbergProfile u) u := by
  have h := ((hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 2)).sub
    ((((hasDerivAt_id u).const_mul (2 * π)).cos).div_const ((2 * π) ^ 2))
  convert h using 1 <;> try rfl
  simp only [id_eq]
  unfold selbergProfile
  field_simp
  ring

/-- The profile has half-unit mass on the positive half-axis. -/
theorem integral_selbergProfile : (∫ u in (0 : ℝ)..1, selbergProfile u) = 1 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => selbergProfile_primitive u) (continuous_selbergProfile.intervalIntegrable 0 1)]
  simp only [mul_one, one_pow, mul_zero, cos_zero, cos_two_pi, zero_pow (by decide : 2 ≠ 0),
    zero_div, sub_zero, zero_sub]
  ring

/-- The Selberg kernel, defined by its everywhere regular cosine transform. -/
def selbergKernel (x : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..1, selbergProfile u * cos (2 * π * x * u)

@[simp] theorem selbergKernel_zero : selbergKernel 0 = 1 := by
  simp only [selbergKernel, mul_zero, zero_mul, cos_zero, mul_one, integral_selbergProfile]
  norm_num

/-- Positivity of the profile bounds every kernel value by its diagonal value. -/
theorem selbergKernel_le_one (x : ℝ) : selbergKernel x ≤ 1 := by
  have hi : IntervalIntegrable (fun u => selbergProfile u * cos (2 * π * x * u)) volume 0 1 :=
    (continuous_selbergProfile.mul
      (by fun_prop : Continuous (fun u : ℝ => cos (2 * π * x * u)))).intervalIntegrable 0 1
  have h := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    hi (continuous_selbergProfile.intervalIntegrable 0 1) (fun u hu =>
      mul_le_of_le_one_right (selbergProfile_nonneg ⟨u, hu⟩) (cos_le_one _))
  rw [integral_selbergProfile] at h
  unfold selbergKernel
  linarith only [h]

private theorem product_primitive (a b u : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a + b ≠ 0) (hsub : a - b ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 - v) * sin (b * v) / b - cos (b * v) / b ^ 2 -
      cos ((a + b) * v) / (2 * a * (a + b)) -
      cos ((a - b) * v) / (2 * a * (a - b)))
      ((1 - u + sin (a * u) / a) * cos (b * u)) u := by
  have hi := hasDerivAt_id u
  have h := (((((hasDerivAt_const u 1).sub hi).mul ((hi.const_mul b).sin)).div_const b).sub
    (((hi.const_mul b).cos).div_const (b ^ 2))).sub
      (((hi.const_mul (a + b)).cos).div_const (2 * a * (a + b)))
  have hh := h.sub (((hi.const_mul (a - b)).cos).div_const (2 * a * (a - b)))
  convert hh using 1 <;> try rfl
  simp only [id_eq, Pi.sub_apply, mul_one, one_mul, sub_mul, add_mul, sin_add, sin_sub]
  field_simp [ha, hb, hab, hsub]
  ring

private theorem selbergKernel_formula (x : ℝ) (hx : x ≠ 0)
    (hplus : 1 + x ≠ 0) (hminus : 1 - x ≠ 0) :
    selbergKernel x = Real.sinc (π * x) ^ 2 / (1 - x ^ 2) := by
  have ha : 2 * π ≠ 0 := by positivity
  have hb : 2 * π * x ≠ 0 := mul_ne_zero ha hx
  have hab : 2 * π + 2 * π * x ≠ 0 := by
    rw [show 2 * π + 2 * π * x = (2 * π) * (1 + x) by ring]
    exact mul_ne_zero ha hplus
  have hsub : 2 * π - 2 * π * x ≠ 0 := by
    rw [show 2 * π - 2 * π * x = (2 * π) * (1 - x) by ring]
    exact mul_ne_zero ha hminus
  have hden : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hminus hplus
  have hi : IntervalIntegrable
      (fun u => (1 - u + sin (2 * π * u) / (2 * π)) * cos (2 * π * x * u)) volume 0 1 :=
    (by fun_prop : Continuous
      (fun u : ℝ => (1 - u + sin (2 * π * u) / (2 * π)) * cos (2 * π * x * u))).intervalIntegrable 0 1
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => product_primitive (2 * π) (2 * π * x) u ha hb hab hsub) hi
  unfold selbergKernel selbergProfile
  rw [he]
  simp only [mul_one, sub_self, zero_mul, mul_zero, sin_zero, cos_zero, zero_div,
    sub_zero, zero_sub, cos_add, cos_sub, cos_two_pi, sin_two_pi, one_mul, add_zero]
  calc
    _ = 2 * (1 - cos (2 * π * x)) / ((2 * π * x) ^ 2 * (1 - x ^ 2)) := by
      field_simp [ha, hb, hab, hsub, hx, pi_ne_zero, hden]
      ring
    _ = _ := by
      have hcos : 1 - cos (2 * π * x) = 2 * sin (π * x) ^ 2 := by
        rw [show 2 * π * x = 2 * (π * x) by ring, cos_two_mul]
        nlinarith only [sin_sq_add_cos_sq (π * x)]
      rw [hcos, sinc_of_ne_zero (mul_ne_zero pi_ne_zero hx)]
      field_simp

/-- The kernel majorizes no distant pair: only distances at most one can contribute positively. -/
theorem selbergKernel_le_indicator (x : ℝ) :
    selbergKernel x ≤ if |x| ≤ 1 then 1 else 0 := by
  split_ifs with h
  · exact selbergKernel_le_one x
  · have hlarge : 1 < |x| := lt_of_not_ge h
    have hx : x ≠ 0 := by intro he; norm_num [he] at hlarge
    have hplus : 1 + x ≠ 0 := by
      intro he
      have : x = -1 := by linarith only [he]
      simp [this] at hlarge
    have hminus : 1 - x ≠ 0 := by
      intro he
      have : x = 1 := by linarith only [he]
      simp [this] at hlarge
    rw [selbergKernel_formula x hx hplus hminus]
    apply div_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    have hs := (sq_le_one_iff_abs_le_one x).not.mpr h
    linarith only [hs]

private theorem selbergKernel_one : selbergKernel 1 = 0 := by
  have hp (u : ℝ) : HasDerivAt
      (fun v : ℝ => (1 - v) * sin (2 * π * v) / (2 * π) -
        cos (2 * π * v) / (2 * π) ^ 2 - cos (2 * (2 * π) * v) / (4 * (2 * π) ^ 2))
      (selbergProfile u * cos (2 * π * u)) u := by
    have hi := hasDerivAt_id u
    have h := (((((hasDerivAt_const u 1).sub hi).mul ((hi.const_mul (2 * π)).sin)).div_const
      (2 * π)).sub (((hi.const_mul (2 * π)).cos).div_const ((2 * π) ^ 2))).sub
        (((hi.const_mul (2 * (2 * π))).cos).div_const (4 * (2 * π) ^ 2))
    convert h using 1 <;> try rfl
    simp only [id_eq, Pi.sub_apply, mul_one]
    rw [show 2 * (2 * π) * u = 2 * (2 * π * u) by ring, sin_two_mul]
    unfold selbergProfile
    field_simp
    ring
  have hi : IntervalIntegrable (fun u => selbergProfile u * cos (2 * π * u)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold selbergProfile
    fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hp u) hi
  unfold selbergKernel
  simp only [mul_one]
  rw [he]
  simp only [mul_one, sub_self, zero_mul, mul_zero, sin_zero, cos_zero, zero_div,
    sub_zero, zero_sub]
  rw [cos_two_mul (2 * π), cos_two_pi]
  ring

/-- The cosine transform equals the Selberg quotient, with both removable values equal to zero. -/
theorem selbergKernel_eq_sinc_quotient (x : ℝ) :
    selbergKernel x = sinc (π * x) ^ 2 / (1 - x ^ 2) := by
  by_cases hzero : x = 0
  · simp [hzero]
  by_cases hplus : 1 + x = 0
  · have hx : x = -1 := by linarith only [hplus]
    have he : selbergKernel (-1) = selbergKernel 1 := by
      simp only [selbergKernel, mul_neg, neg_mul, cos_neg]
    rw [hx, he, selbergKernel_one]
    norm_num
  by_cases hminus : 1 - x = 0
  · have hx : x = 1 := by linarith only [hminus]
    rw [hx, selbergKernel_one]
    norm_num
  exact selbergKernel_formula x hzero hplus hminus

/-- The transform satisfies the sinc-square identity at every real argument,
including the two removable singularities of the quotient formula. -/
theorem selbergKernel_mul_one_sub_sq (x : ℝ) :
    selbergKernel x * (1 - x ^ 2) = sinc (π * x) ^ 2 := by
  by_cases hzero : x = 0
  · simp [hzero]
  by_cases hplus : 1 + x = 0
  · have hx : x = -1 := by linarith only [hplus]
    simp [hx, sinc_of_ne_zero pi_ne_zero]
  by_cases hminus : 1 - x = 0
  · have hx : x = 1 := by linarith only [hminus]
    simp [hx, sinc_of_ne_zero pi_ne_zero]
  have hden : 1 - x ^ 2 ≠ 0 := by
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
    exact mul_ne_zero hminus hplus
  rw [selbergKernel_formula x hzero hplus hminus, div_mul_cancel₀ _ hden]

end
end GaloisForLFunctions.TransThresholdPairCorrelation

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergProfile_nonneg
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_le_one
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_le_indicator
#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_mul_one_sub_sq

#print axioms GaloisForLFunctions.TransThresholdPairCorrelation.selbergKernel_eq_sinc_quotient
