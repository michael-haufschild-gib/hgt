import GaloisForLFunctions.RHTower.CCMThetaLocalizationCrossBounds

/-!
# The actual continuous localization second moment

The moment includes the singular Gamma coefficient and both pole channels,
truncated only where compact source correlations vanish identically. It is
finite at every aperture and bounds the full continuous localization error.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmThetaContinuousMomentDensity (a : SuzukiPositiveAperture) (h : ℝ) : ℝ :=
  if h < 2 * a.1 then |thetaGammaPolarScalingKernel h| * h ^ 2 else 0

def ccmThetaContinuousLocalizationMoment (a : SuzukiPositiveAperture) : ℝ :=
  ∫ h in Ioi (0 : ℝ), ccmThetaContinuousMomentDensity a h

theorem ccmThetaContinuousMomentDensity_nonneg (a : SuzukiPositiveAperture) (h : ℝ) :
    0 ≤ ccmThetaContinuousMomentDensity a h := by
  unfold ccmThetaContinuousMomentDensity
  split <;> positivity

theorem ccmThetaContinuousMomentDensity_le (a : SuzukiPositiveAperture)
    {h : ℝ} (hh : 0 < h) : ccmThetaContinuousMomentDensity a h ≤
      Real.exp (4 * a.1) * ((2 * h ^ 2 + h / 2) * Real.exp (-h / 2)) := by
  unfold ccmThetaContinuousMomentDensity
  split_ifs with hcut
  · have he : Real.exp (2 * h) ≤ Real.exp (4 * a.1) := Real.exp_le_exp.mpr (by linarith)
    calc
      _ = Real.exp (2 * h) *
          (|thetaGammaPolarScalingKernel h| * Real.exp (-2 * h) * h ^ 2) := by
        rw [show -2 * h = -(2 * h) by ring, Real.exp_neg]
        field_simp
      _ ≤ Real.exp (2 * h) * ((2 * h ^ 2 + h / 2) * Real.exp (-h / 2)) :=
        mul_le_mul_of_nonneg_left (thetaGammaPolar_damped_square_bound hh) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)
  · positivity

theorem integrable_ccmThetaContinuousMomentDensity (a : SuzukiPositiveAperture) :
    IntegrableOn (ccmThetaContinuousMomentDensity a) (Ioi 0) := by
  have hi₁ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hi₂ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hi : IntegrableOn (fun h : ℝ => Real.exp (4 * a.1) *
      ((2 * |h| ^ 2 + |h| / 2) * Real.exp (-(1 / 2) * |h|))) (Ioi 0) := by
    convert! (((hi₂.const_mul 2).add (hi₁.div_const 2)).const_mul
      (Real.exp (4 * a.1))).integrableOn using 1
    ext h
    simp only [Pi.add_apply, pow_one]
    ring
  have hm : Measurable (ccmThetaContinuousMomentDensity a) := by
    unfold ccmThetaContinuousMomentDensity thetaGammaPolarScalingKernel
    exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [Real.norm_of_nonneg (ccmThetaContinuousMomentDensity_nonneg a h), abs_of_pos hh]
  simpa only [show -(1 / 2 : ℝ) * h = -h / 2 by ring] using
    ccmThetaContinuousMomentDensity_le a hh

theorem ccmThetaContinuousLocalizationMoment_nonneg (a : SuzukiPositiveAperture) :
    0 ≤ ccmThetaContinuousLocalizationMoment a :=
  integral_nonneg (ccmThetaContinuousMomentDensity_nonneg a)

theorem integral_norm_ccmThetaContinuousLocalizationDensity_le
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a)
    (theta : 𝓢(ℝ, ℝ)) {h : ℝ} (hh : 0 < h) :
    (∫ x : ℝ, ‖ccmThetaContinuousLocalizationDensity u theta (h, x)‖) ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * ccmThetaContinuousMomentDensity a h *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  by_cases hcut : h < 2 * a.1
  · simp only [ccmThetaContinuousLocalizationDensity, norm_mul, Real.norm_eq_abs,
      integral_const_mul, ccmThetaContinuousMomentDensity, if_pos hcut]
    have hb := mul_le_mul_of_nonneg_left
      (integral_abs_ccmThetaLocalizationCross_shift_le u theta h)
      (abs_nonneg (thetaGammaPolarScalingKernel h))
    convert! hb using 1; ring
  · have hz (x : ℝ) := ccmThetaLocalizationCross_eq_zero_of_aperture_le u theta x h
      (by simpa only [abs_of_pos hh] using le_of_not_gt hcut)
    simp only [ccmThetaContinuousLocalizationDensity, hz, mul_zero, norm_zero,
      integral_zero, ccmThetaContinuousMomentDensity, if_neg hcut, zero_mul, le_refl]

/-- The full signed continuous error is controlled without an unproved kernel estimate. -/
theorem abs_ccmThetaContinuousLocalizationError_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    |ccmThetaContinuousLocalizationError u theta| ≤
      SchwartzMap.seminorm ℝ 0 1 theta ^ 2 * ccmThetaContinuousLocalizationMoment a *
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := by
  have hi := integrable_ccmThetaContinuousLocalizationDensity u theta
  have hm := ((integrable_ccmThetaContinuousMomentDensity a).const_mul
    (SchwartzMap.seminorm ℝ 0 1 theta ^ 2)).mul_const
      (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2)
  have hb := integral_mono_ae hi.integral_norm_prod_left hm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact integral_norm_ccmThetaContinuousLocalizationDensity_le u theta hh)
  rw [integral_mul_const, integral_const_mul] at hb
  calc
    _ ≤ ∫ p, ‖ccmThetaContinuousLocalizationDensity u theta p‖ ∂thetaContinuousLinkMeasure :=
      norm_integral_le_integral_norm _
    _ = ∫ h in Ioi (0 : ℝ), ∫ x : ℝ, ‖ccmThetaContinuousLocalizationDensity u theta (h, x)‖ :=
      integral_prod _ hi.norm
    _ ≤ _ := hb

end RHTower
