import GaloisForLFunctions.RHTower.ThetaLocalizationChainWeight

/-!
# Exact arithmetic totals through a single bounded localization weight

Every finite chain has one common link weight for the prime atoms and the
signed continuous kernel. The error integrals converge by the finite chain
identities, without using the pointwise bound at the singular diagonal.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmThetaChainCross {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) : ℝ :=
  thetaLocalizationChainWeight angles x y * (u y * star (u x)).re

@[simp] theorem ccmThetaChainCross_nil {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (x y : ℝ) :
    ccmThetaChainCross u [] x y = 0 := by
  simp only [ccmThetaChainCross, thetaLocalizationChainWeight, thetaLocalizationChainOverlap,
    sub_self, mul_zero, zero_mul]

theorem ccmThetaChainCross_cons {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (rest : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    ccmThetaChainCross u (theta :: rest) x y = ccmThetaLocalizationCross u theta x y +
      ccmThetaChainCross (ccmCosLocalizedSource u theta) rest x y := by
  simp only [ccmThetaChainCross, ccmThetaLocalizationCross,
    thetaLocalizationChainWeight_cons, ccmCosLocalizedSource_correlation]
  ring

theorem abs_ccmThetaChainCross_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (x y : ℝ) :
    |ccmThetaChainCross u angles x y| ≤ 4 * ‖u y‖ * ‖u x‖ := by
  have hc : |(u y * star (u x)).re| ≤ ‖u y‖ * ‖u x‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (u y * star (u x))
  rw [ccmThetaChainCross, abs_mul,
    abs_of_nonneg (thetaLocalizationChainWeight_nonneg angles x y)]
  calc
    _ ≤ thetaLocalizationChainWeight angles x y * (‖u y‖ * ‖u x‖) :=
      mul_le_mul_of_nonneg_left hc (thetaLocalizationChainWeight_nonneg angles x y)
    _ ≤ 4 * (‖u y‖ * ‖u x‖) := mul_le_mul_of_nonneg_right
      (thetaLocalizationChainWeight_le_four angles x y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := (mul_assoc _ _ _).symm

def ccmThetaChainPrimeDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (p : ℕ × ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 *
    ccmThetaChainCross u angles p.2 (p.2 + Real.log p.1)

def ccmThetaChainContinuousDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (p : ℝ × ℝ) : ℝ :=
  thetaGammaPolarScalingKernel p.1 * ccmThetaChainCross u angles p.2 (p.2 + p.1)

theorem ccmThetaChainPrimeDensity_cons {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (rest : List 𝓢(ℝ, ℝ)) :
    ccmThetaChainPrimeDensity u (theta :: rest) = fun p =>
      ccmThetaPrimeLocalizationDensity u theta p +
        ccmThetaChainPrimeDensity (ccmCosLocalizedSource u theta) rest p := by
  funext p
  simp only [ccmThetaChainPrimeDensity, ccmThetaPrimeLocalizationDensity,
    ccmThetaChainCross_cons, mul_add]

theorem ccmThetaChainContinuousDensity_cons {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ))
    (rest : List 𝓢(ℝ, ℝ)) :
    ccmThetaChainContinuousDensity u (theta :: rest) = fun p =>
      ccmThetaContinuousLocalizationDensity u theta p +
        ccmThetaChainContinuousDensity (ccmCosLocalizedSource u theta) rest p := by
  funext p
  simp only [ccmThetaChainContinuousDensity, ccmThetaContinuousLocalizationDensity,
    ccmThetaChainCross_cons, mul_add]

theorem integrable_ccmThetaChainPrimeDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    Integrable (ccmThetaChainPrimeDensity u angles) thetaPrimeLinkMeasure := by
  induction angles generalizing u with
  | nil =>
    have hz : ccmThetaChainPrimeDensity u [] = 0 := by
      funext p
      simp only [ccmThetaChainPrimeDensity, ccmThetaChainCross_nil, mul_zero, Pi.zero_apply]
    rw [hz]
    exact integrable_zero _ _ _
  | cons theta rest ih =>
    rw [ccmThetaChainPrimeDensity_cons]
    exact (integrable_ccmThetaPrimeLocalizationDensity u theta).add (ih _)

theorem integrable_ccmThetaChainContinuousDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    Integrable (ccmThetaChainContinuousDensity u angles) thetaContinuousLinkMeasure := by
  induction angles generalizing u with
  | nil =>
    have hz : ccmThetaChainContinuousDensity u [] = 0 := by
      funext p
      simp only [ccmThetaChainContinuousDensity, ccmThetaChainCross_nil, mul_zero, Pi.zero_apply]
    rw [hz]
    exact integrable_zero _ _ _
  | cons theta rest ih =>
    rw [ccmThetaChainContinuousDensity_cons]
    exact (integrable_ccmThetaContinuousLocalizationDensity u theta).add (ih _)

theorem ccmLocalizationPrimeTotal_eq_integral {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    ccmLocalizationPrimeTotal u angles =
      ∫ p, ccmThetaChainPrimeDensity u angles p ∂thetaPrimeLinkMeasure := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationPrimeTotal, ccmThetaChainPrimeDensity,
      ccmThetaChainCross_nil, mul_zero, integral_zero]
  | cons theta rest ih =>
    rw [ccmLocalizationPrimeTotal, ccmThetaChainPrimeDensity_cons,
      integral_add (integrable_ccmThetaPrimeLocalizationDensity u theta)
        (integrable_ccmThetaChainPrimeDensity _ rest), ← ih]
    rfl

theorem ccmLocalizationContinuousTotal_eq_integral {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    ccmLocalizationContinuousTotal u angles =
      ∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure := by
  induction angles generalizing u with
  | nil => simp only [ccmLocalizationContinuousTotal, ccmThetaChainContinuousDensity,
      ccmThetaChainCross_nil, mul_zero, integral_zero]
  | cons theta rest ih =>
    rw [ccmLocalizationContinuousTotal, ccmThetaChainContinuousDensity_cons,
      integral_add (integrable_ccmThetaContinuousLocalizationDensity u theta)
        (integrable_ccmThetaChainContinuousDensity _ rest), ← ih]
    rfl

end RHTower
