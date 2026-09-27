import GaloisForLFunctions.RHTower.CCMThetaSmoothLocalization

/-!
# Exact localization of the full prime--Gamma--pole form

The errors here are literal arithmetic integrals of the physical source,
not assumed bounds or abstract quadratic remainders. Absolute convergence
follows from the three convergent energies and the exact increment identity.
The theta ground factors cancel, leaving the von Mangoldt prime atoms and
the full signed Gamma/pole kernel against the same complex correlation.
-/

noncomputable section

open MeasureTheory Filter
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

def ccmThetaLocalizationCross {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : ℝ → ℝ) (x y : ℝ) : ℝ :=
  thetaLocalizationWeight theta x y * (u y * star (u x)).re

theorem ccmThetaGroundProfile_cross {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (x y : ℝ) :
    thetaCuspFullSource x * thetaCuspFullSource y *
      (ccmThetaGroundProfile u y * star (ccmThetaGroundProfile u x)).re =
        (u y * star (u x)).re := by
  conv_rhs => rw [← ccmThetaGroundProfile_reconstruct u y,
    ← ccmThetaGroundProfile_reconstruct u x]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_add]
  ring

/-- Weighted local-rotation defect after cancelling the actual theta ground state. -/
theorem ccmThetaWeightedIncrement_localization {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (c x y : ℝ) :
    c * thetaCuspFullSource x * thetaCuspFullSource y *
      (‖ccmThetaGroundProfile (ccmCosLocalizedSource u theta) y -
          ccmThetaGroundProfile (ccmCosLocalizedSource u theta) x‖ ^ 2 +
        ‖ccmThetaGroundProfile (ccmSinLocalizedSource u theta) y -
          ccmThetaGroundProfile (ccmSinLocalizedSource u theta) x‖ ^ 2 -
        ‖ccmThetaGroundProfile u y - ccmThetaGroundProfile u x‖ ^ 2) =
      c * ccmThetaLocalizationCross u theta x y := by
  simp only [ccmThetaGroundProfile_cosLocalized, ccmThetaGroundProfile_sinLocalized]
  rw [thetaLocalization_increment_identity]
  unfold ccmThetaLocalizationCross
  calc
    _ = c * thetaLocalizationWeight theta x y *
        (thetaCuspFullSource x * thetaCuspFullSource y *
          (ccmThetaGroundProfile u y * star (ccmThetaGroundProfile u x)).re) := by ring
    _ = _ := by rw [ccmThetaGroundProfile_cross]; ring

def ccmThetaPrimeLocalizationDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : ℝ → ℝ) (p : ℕ × ℝ) : ℝ :=
  ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 *
    ccmThetaLocalizationCross u theta p.2 (p.2 + Real.log p.1)

def ccmThetaContinuousLocalizationDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  thetaGammaPolarScalingKernel p.1 * ccmThetaLocalizationCross u theta p.2 (p.2 + p.1)

theorem ccmThetaPrimeLocalizationDensity_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (p : ℕ × ℝ) :
    ccmThetaPrimeLocalizationDensity u theta p =
      thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)).toBoundedContinuousFunction p +
      thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)).toBoundedContinuousFunction p -
      thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction p := by
  simp only [thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement,
    SchwartzMap.toBoundedContinuousFunction_apply, thetaPrimeLinkDensity_eq_real,
    Complex.ofReal_re]
  rw [ccmThetaPrimeLocalizationDensity,
    ← ccmThetaWeightedIncrement_localization u theta
      (ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1) p.2 (p.2 + Real.log p.1)]
  change _ = _ * (_ * thetaCuspFullSource _ * thetaCuspFullSource _) +
    _ * (_ * thetaCuspFullSource _ * thetaCuspFullSource _) -
    _ * (_ * thetaCuspFullSource _ * thetaCuspFullSource _)
  ring

theorem ccmThetaContinuousLocalizationDensity_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (p : ℝ × ℝ) :
    ccmThetaContinuousLocalizationDensity u theta p =
      thetaGammaPolarScalingDensity thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)) p +
      thetaGammaPolarScalingDensity thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)) p -
      thetaGammaPolarScalingDensity thetaCuspTiltSource (ccmThetaGroundProfile u) p := by
  rw [ccmThetaContinuousLocalizationDensity,
    ← ccmThetaWeightedIncrement_localization u theta (thetaGammaPolarScalingKernel p.1)
      p.2 (p.2 + p.1)]
  simp only [thetaGammaPolarScalingDensity]
  change _ = _ * thetaCuspFullSource _ * thetaCuspFullSource _ * _ +
    _ * thetaCuspFullSource _ * thetaCuspFullSource _ * _ -
    _ * thetaCuspFullSource _ * thetaCuspFullSource _ * _
  ring

/-- No integrability premise is needed: the actual prime error converges absolutely. -/
theorem integrable_ccmThetaPrimeLocalizationDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    Integrable (ccmThetaPrimeLocalizationDensity u theta) thetaPrimeLinkMeasure := by
  apply ((integrable_thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
      (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)).toBoundedContinuousFunction).add
    (integrable_thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
      (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)).toBoundedContinuousFunction) |>.sub
    (integrable_thetaPrimeScalingEnergyDensity thetaCuspTiltSource thetaCuspTiltSource
      (ccmThetaGroundProfile u).toBoundedContinuousFunction)).congr
  exact Eventually.of_forall fun p => (ccmThetaPrimeLocalizationDensity_eq u theta p).symm

/-- The singular Gamma term and both growing pole terms are retained and converge. -/
theorem integrable_ccmThetaContinuousLocalizationDensity {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    Integrable (ccmThetaContinuousLocalizationDensity u theta) thetaContinuousLinkMeasure := by
  apply ((integrable_thetaGammaPolarScalingDensity thetaCuspTiltSource
      (ccmThetaGroundProfile (ccmCosLocalizedSource u theta))).add
    (integrable_thetaGammaPolarScalingDensity thetaCuspTiltSource
      (ccmThetaGroundProfile (ccmSinLocalizedSource u theta))) |>.sub
    (integrable_thetaGammaPolarScalingDensity thetaCuspTiltSource (ccmThetaGroundProfile u))).congr
  exact Eventually.of_forall fun p => (ccmThetaContinuousLocalizationDensity_eq u theta p).symm

def ccmThetaPrimeLocalizationError {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) : ℝ :=
  ∫ p, ccmThetaPrimeLocalizationDensity u theta p ∂thetaPrimeLinkMeasure

def ccmThetaContinuousLocalizationError {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) : ℝ :=
  ∫ p, ccmThetaContinuousLocalizationDensity u theta p ∂thetaContinuousLinkMeasure

theorem ccmThetaPrimeLocalizationError_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ccmThetaPrimeLocalizationError u theta =
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)).toBoundedContinuousFunction +
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)).toBoundedContinuousFunction -
      thetaPrimeScalingEnergy thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  unfold ccmThetaPrimeLocalizationError thetaPrimeScalingEnergy
  simp_rw [ccmThetaPrimeLocalizationDensity_eq]
  rw [integral_sub ((integrable_thetaPrimeScalingEnergyDensity _ _ _).fun_add
    (integrable_thetaPrimeScalingEnergyDensity _ _ _))
    (integrable_thetaPrimeScalingEnergyDensity _ _ _),
    integral_add (integrable_thetaPrimeScalingEnergyDensity _ _ _)
      (integrable_thetaPrimeScalingEnergyDensity _ _ _)]

theorem ccmThetaContinuousLocalizationError_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ccmThetaContinuousLocalizationError u theta =
      thetaGammaPolarScalingEnergy thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmCosLocalizedSource u theta)) +
      thetaGammaPolarScalingEnergy thetaCuspTiltSource
        (ccmThetaGroundProfile (ccmSinLocalizedSource u theta)) -
      thetaGammaPolarScalingEnergy thetaCuspTiltSource (ccmThetaGroundProfile u) := by
  unfold ccmThetaContinuousLocalizationError thetaGammaPolarScalingEnergy
  simp_rw [ccmThetaContinuousLocalizationDensity_eq]
  rw [integral_sub ((integrable_thetaGammaPolarScalingDensity _ _).fun_add
    (integrable_thetaGammaPolarScalingDensity _ _))
    (integrable_thetaGammaPolarScalingDensity _ _),
    integral_add (integrable_thetaGammaPolarScalingDensity _ _)
      (integrable_thetaGammaPolarScalingDensity _ _)]

/-- Exact IMS formula for the actual full restricted Weil form, for every complex smooth source. -/
theorem ccmRestrictedWeilSourceQuadratic_localization {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic a (ccmCosLocalizedSource u theta).toCCMFormVector +
      ccmRestrictedWeilSourceQuadratic a (ccmSinLocalizedSource u theta).toCCMFormVector -
      ccmThetaPrimeLocalizationError u theta + ccmThetaContinuousLocalizationError u theta := by
  simp only [ccmRestrictedWeilSourceQuadratic_eq_thetaEnergyDifference,
    ccmThetaPrimeLocalizationError_eq, ccmThetaContinuousLocalizationError_eq]
  ring

end RHTower
