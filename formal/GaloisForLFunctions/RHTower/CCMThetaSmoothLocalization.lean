import GaloisForLFunctions.RHTower.CCMThetaThreeEnergyComparison

/-!
# Smooth quadratic localization of actual CCM sources

An arbitrary real Schwartz angle produces the exact quadratic partition
`cos(theta)^2 + sin(theta)^2 = 1`. Both localized sources remain in the
same strict-interior smooth core. Their physical masses add exactly.
The squared-increment identity below retains the complex cross term;
discarding its sign would lose the full arithmetic localization error.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmCosLocalizedSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    CCMComplexSmoothInteriorSource a where
  toFun := fun x => (Real.cos (theta x) : ℂ) * u x
  smooth := (Complex.ofRealCLM.contDiff.comp (theta.smooth ⊤).cos).mul u.smooth
  hasCompactSupport := u.hasCompactSupport.mul_left
  tsupport_subset := tsupport_mul_subset_right.trans u.tsupport_subset

def ccmSinLocalizedSource {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    CCMComplexSmoothInteriorSource a where
  toFun := fun x => (Real.sin (theta x) : ℂ) * u x
  smooth := (Complex.ofRealCLM.contDiff.comp (theta.smooth ⊤).sin).mul u.smooth
  hasCompactSupport := u.hasCompactSupport.mul_left
  tsupport_subset := tsupport_mul_subset_right.trans u.tsupport_subset

@[simp] theorem ccmCosLocalizedSource_apply {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x : ℝ) :
    ccmCosLocalizedSource u theta x = (Real.cos (theta x) : ℂ) * u x := rfl

@[simp] theorem ccmSinLocalizedSource_apply {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x : ℝ) :
    ccmSinLocalizedSource u theta x = (Real.sin (theta x) : ℂ) * u x := rfl

theorem ccmThetaGroundProfile_cosLocalized {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x : ℝ) :
    ccmThetaGroundProfile (ccmCosLocalizedSource u theta) x =
      (Real.cos (theta x) : ℂ) * ccmThetaGroundProfile u x := by
  simp only [ccmThetaGroundProfile_apply, ccmCosLocalizedSource_apply, mul_div_assoc]

theorem ccmThetaGroundProfile_sinLocalized {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (x : ℝ) :
    ccmThetaGroundProfile (ccmSinLocalizedSource u theta) x =
      (Real.sin (theta x) : ℂ) * ccmThetaGroundProfile u x := by
  simp only [ccmThetaGroundProfile_apply, ccmSinLocalizedSource_apply, mul_div_assoc]

def thetaLocalizationWeight (theta : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (Real.cos (theta y) - Real.cos (theta x)) ^ 2 +
    (Real.sin (theta y) - Real.sin (theta x)) ^ 2

theorem thetaLocalizationWeight_nonneg (theta : ℝ → ℝ) (x y : ℝ) :
    0 ≤ thetaLocalizationWeight theta x y := by
  unfold thetaLocalizationWeight
  positivity

theorem thetaLocalizationWeight_eq_cos (theta : ℝ → ℝ) (x y : ℝ) :
    thetaLocalizationWeight theta x y = 2 * (1 - Real.cos (theta y - theta x)) := by
  unfold thetaLocalizationWeight
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq (theta x), Real.sin_sq_add_cos_sq (theta y)]

theorem thetaLocalizationWeight_le_four (theta : ℝ → ℝ) (x y : ℝ) :
    thetaLocalizationWeight theta x y ≤ 4 := by
  rw [thetaLocalizationWeight_eq_cos]
  linarith [Real.neg_one_le_cos (theta y - theta x)]

/-- Exact local rotation identity, valid for arbitrary complex source values. -/
theorem thetaLocalization_increment_identity (theta : ℝ → ℝ) (x y : ℝ) (z w : ℂ) :
    ‖(Real.cos (theta y) : ℂ) * z - (Real.cos (theta x) : ℂ) * w‖ ^ 2 +
      ‖(Real.sin (theta y) : ℂ) * z - (Real.sin (theta x) : ℂ) * w‖ ^ 2 -
        ‖z - w‖ ^ 2 = thetaLocalizationWeight theta x y * (z * star w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.star_def, Complex.conj_re, Complex.conj_im,
    thetaLocalizationWeight]
  linear_combination
    (z.re ^ 2 + z.im ^ 2 - z.re * w.re - z.im * w.im) *
      (Real.sin_sq_add_cos_sq (theta y)) +
    (w.re ^ 2 + w.im ^ 2 - z.re * w.re - z.im * w.im) *
      (Real.sin_sq_add_cos_sq (theta x))

theorem thetaLocalization_mass_identity (t : ℝ) (z : ℂ) :
    ‖(Real.cos t : ℂ) * z‖ ^ 2 + ‖(Real.sin t : ℂ) * z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem thetaGroundNormSq_localization {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    thetaGroundNormSq (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)) +
      thetaGroundNormSq (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)) =
        thetaGroundNormSq (ccmThetaGroundProfile u) := by
  unfold thetaGroundNormSq
  rw [← integral_add (integrable_thetaGroundNormDensity _)
    (integrable_thetaGroundNormDensity _)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [thetaGroundNormDensity, ccmThetaGroundProfile_cosLocalized,
    ccmThetaGroundProfile_sinLocalized, ← mul_add, thetaLocalization_mass_identity]

/-- Localization preserves the total physical mass exactly, in the actual CCM domain. -/
theorem ccmPhysicalMass_localization {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ‖ccmArchimedeanFormToAperture a (ccmCosLocalizedSource u theta).toCCMFormVector‖ ^ 2 +
      ‖ccmArchimedeanFormToAperture a (ccmSinLocalizedSource u theta).toCCMFormVector‖ ^ 2 =
        ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
  simpa only [thetaGroundNormSq_ccmProfile_eq_physical] using
    thetaGroundNormSq_localization u theta

end RHTower
