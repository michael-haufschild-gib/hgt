import GaloisForLFunctions.RHTower.CCMThetaArithmeticLocalization
import GaloisForLFunctions.RHTower.CCMSmoothSupportUncertainty

/-!
# Quantitative bounds for the exact arithmetic localization correlation

The angle derivative controls the error quadratically in the link length.
For each shift, its absolute spatial integral is bounded by that factor
times the actual physical mass. All interactions vanish beyond twice the
aperture. These estimates retain arbitrary complex source phases.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem thetaLocalizationWeight_le_angle_sq (theta : ℝ → ℝ) (x y : ℝ) :
    thetaLocalizationWeight theta x y ≤ (theta y - theta x) ^ 2 := by
  rw [thetaLocalizationWeight_eq_cos]
  linarith [Real.one_sub_sq_div_two_le_cos (x := theta y - theta x)]

theorem thetaLocalizationWeight_le_seminorm (theta : 𝓢(ℝ, ℝ)) (x y : ℝ) :
    thetaLocalizationWeight theta x y ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * (y - x) ^ 2 := by
  have hder (z : ℝ) : ‖deriv theta z‖ ≤ SchwartzMap.seminorm ℝ 0 1 theta := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using theta.le_seminorm' ℝ 0 1 z
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => theta.differentiableAt (x := z)) (fun z _ => hder z)
    (mem_univ x) (mem_univ y)
  have hs := pow_le_pow_left₀ (norm_nonneg (theta y - theta x)) h 2
  simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hs
  exact (thetaLocalizationWeight_le_angle_sq theta x y).trans hs

theorem abs_ccmThetaLocalizationCross_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x y : ℝ) :
    |ccmThetaLocalizationCross u theta x y| ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * (y - x) ^ 2 * ‖u y‖ * ‖u x‖ := by
  rw [ccmThetaLocalizationCross, abs_mul,
    abs_of_nonneg (thetaLocalizationWeight_nonneg theta x y)]
  have hc : |(u y * star (u x)).re| ≤ ‖u y‖ * ‖u x‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (u y * star (u x))
  calc
    _ ≤ (SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * (y - x) ^ 2) *
        (‖u y‖ * ‖u x‖) := mul_le_mul (thetaLocalizationWeight_le_seminorm theta x y)
          hc (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem ccmThetaLocalizationCross_eq_zero_of_aperture_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : ℝ → ℝ) (x h : ℝ)
    (hh : 2 * a.1 ≤ |h|) : ccmThetaLocalizationCross u theta x (x + h) = 0 := by
  by_cases hx : u x = 0
  · simp [ccmThetaLocalizationCross, hx]
  by_cases hy : u (x + h) = 0
  · simp [ccmThetaLocalizationCross, hy]
  have hxs := u.support_subset hx
  have hys := u.support_subset hy
  have : |h| < 2 * a.1 := abs_lt.mpr ⟨by linarith [hxs.2, hys.1],
    by linarith [hxs.1, hys.2]⟩
  exact False.elim (not_lt_of_ge hh this)

theorem integrable_ccmSmooth_norm_sq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : Integrable (fun x : ℝ => ‖u x‖ ^ 2) := by
  have hc : HasCompactSupport (fun x : ℝ => ‖u x‖ ^ 2) :=
    u.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
  exact (u.continuous.norm.pow 2).integrable_of_hasCompactSupport hc

theorem integrable_ccmSmooth_shift_norm_mul {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    Integrable (fun x : ℝ => ‖u (x + h)‖ * ‖u x‖) := by
  apply ((u.continuous.comp (continuous_id.add continuous_const)).norm.mul
    u.continuous.norm).integrable_of_hasCompactSupport
  exact u.hasCompactSupport.norm.mul_left

/-- The spatial absolute correlation never exceeds the physical mass. -/
theorem integral_ccmSmooth_shift_norm_mul_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    (∫ x : ℝ, ‖u (x + h)‖ * ‖u x‖) ≤
      ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  have hi := integrable_ccmSmooth_norm_sq u
  have hp := integrable_ccmSmooth_shift_norm_mul u h
  have hle := integral_mono (hp.const_mul 2) ((hi.comp_add_right h).fun_add hi)
    (fun x => by nlinarith [sq_nonneg (‖u (x + h)‖ - ‖u x‖)])
  rw [integral_const_mul, integral_add (hi.comp_add_right h) hi,
    integral_add_right_eq_self (fun x : ℝ => ‖u x‖ ^ 2) h,
    ccmSmooth_integral_norm_sq_eq_physical] at hle
  linarith

theorem integrable_ccmThetaLocalizationCross_shift {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (h : ℝ) :
    Integrable (fun x : ℝ => ccmThetaLocalizationCross u theta x (x + h)) := by
  have hc : Continuous (fun x : ℝ => ccmThetaLocalizationCross u theta x (x + h)) := by
    have hu := u.continuous
    have ht := theta.continuous
    unfold ccmThetaLocalizationCross thetaLocalizationWeight
    fun_prop
  apply (((integrable_ccmSmooth_shift_norm_mul u h).const_mul
    (SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * h ^ 2))).mono' hc.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, add_sub_cancel_left, mul_assoc] using
    abs_ccmThetaLocalizationCross_le u theta x (x + h)

/-- Literal, unconditional second-moment estimate for every individual arithmetic link. -/
theorem integral_abs_ccmThetaLocalizationCross_shift_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (h : ℝ) :
    (∫ x : ℝ, |ccmThetaLocalizationCross u theta x (x + h)|) ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * h ^ 2 *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  have hle := integral_mono (integrable_ccmThetaLocalizationCross_shift u theta h).abs
    ((integrable_ccmSmooth_shift_norm_mul u h).const_mul
      (SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * h ^ 2)) (fun x => by
        simpa only [add_sub_cancel_left, mul_assoc] using
          abs_ccmThetaLocalizationCross_le u theta x (x + h))
  rw [integral_const_mul] at hle
  exact hle.trans (mul_le_mul_of_nonneg_left (integral_ccmSmooth_shift_norm_mul_le u h)
    (by positivity))

end RHTower
