import GaloisForLFunctions.RHTower.CCMThetaArithmeticPhaseOrbit

/-!
# Local potentials do not alter the arithmetic phase interaction

Every continuous local potential obeys the same pointwise mass partition.
It cancels from the localization defect and from the relative phase energy.
The explicit opposite-sign witnesses therefore survive every such potential.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

theorem ccmSmoothLocalPotentialEnergy_localization {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ccmSmoothLocalPotentialEnergy V (ccmCosLocalizedSource u theta) +
      ccmSmoothLocalPotentialEnergy V (ccmSinLocalizedSource u theta) =
      ccmSmoothLocalPotentialEnergy V u := by
  unfold ccmSmoothLocalPotentialEnergy
  rw [← integral_add (integrable_ccmSmoothLocalPotentialDensity V _)
    (integrable_ccmSmoothLocalPotentialDensity V _)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [ccmCosLocalizedSource_apply, ccmSinLocalizedSource_apply,
    ← mul_add, thetaLocalization_mass_identity]

def ccmLocalPotentialLocalizationDefect {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) : ℝ :=
  (ccmRestrictedWeilSourceQuadratic a (ccmCosLocalizedSource u theta).toCCMFormVector +
      ccmSmoothLocalPotentialEnergy V (ccmCosLocalizedSource u theta)) +
    (ccmRestrictedWeilSourceQuadratic a (ccmSinLocalizedSource u theta).toCCMFormVector +
      ccmSmoothLocalPotentialEnergy V (ccmSinLocalizedSource u theta)) -
    (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + ccmSmoothLocalPotentialEnergy V u)

/-- All continuous local potentials cancel from the literal arithmetic localization defect. -/
theorem ccmLocalPotentialLocalizationDefect_eq {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    ccmLocalPotentialLocalizationDefect V u theta =
      ccmThetaPrimeLocalizationError u theta - ccmThetaContinuousLocalizationError u theta := by
  have hq := ccmRestrictedWeilSourceQuadratic_localization u theta
  have hp := ccmSmoothLocalPotentialEnergy_localization V u theta
  unfold ccmLocalPotentialLocalizationDefect
  linarith

/-- One actual compact pair exhibits both signs after every continuous local potential. -/
theorem exists_ccmLocalization_opposite_signs_all_local_potentials :
    ∃ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)), HasCompactSupport theta ∧
      (∀ x, v x = (‖u x‖ : ℂ)) ∧
      ∀ V : C(ℝ, ℝ), 0 < ccmLocalPotentialLocalizationDefect V u theta ∧
        ccmLocalPotentialLocalizationDefect V v theta < 0 := by
  obtain ⟨a, u, v, theta, htc, habs, _, _, _, _, _, hpu, hpv, hcu, hcv, _⟩ :=
    exists_ccmTheta_localization_error_both_signs
  refine ⟨a, u, v, theta, htc, habs, fun V => ?_⟩
  rw [ccmLocalPotentialLocalizationDefect_eq, ccmLocalPotentialLocalizationDefect_eq, hpu, hpv]
  constructor <;> linarith

def ccmPhaseLocalizationEnergyWithPotential {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (t : ℝ) : ℝ :=
  ccmPhaseLocalizationEnergy u theta t +
    ccmSmoothLocalPotentialEnergy V (ccmCosLocalizedSource u (ccmScaledPhaseAngle theta t)) +
    ccmSmoothLocalPotentialEnergy V (ccmSinLocalizedSource u (ccmScaledPhaseAngle theta t))

theorem ccmPhaseLocalizationEnergyWithPotential_eq {a : SuzukiPositiveAperture}
    (V : C(ℝ, ℝ)) (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) (t : ℝ) :
    ccmPhaseLocalizationEnergyWithPotential V u theta t =
      ccmPhaseLocalizationEnergy u theta t + ccmSmoothLocalPotentialEnergy V u := by
  unfold ccmPhaseLocalizationEnergyWithPotential
  rw [add_assoc, ccmSmoothLocalPotentialEnergy_localization]

/-- The exact positive phase stiffness survives every continuous local potential. -/
theorem exists_ccmArithmetic_phase_potential_independent_of_local_potentials :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ), 0 < B ∧
      ∀ (V : C(ℝ, ℝ)) (t : ℝ),
        ccmPhaseLocalizationEnergyWithPotential V u theta t -
          ccmPhaseLocalizationEnergyWithPotential V u theta 0 = B * (1 - Real.cos t) := by
  obtain ⟨a, u, theta, B, hB, _, _, _, he, _⟩ := exists_ccmArithmetic_positive_phase_potential
  refine ⟨a, u, theta, B, hB, fun V t => ?_⟩
  rw [ccmPhaseLocalizationEnergyWithPotential_eq, ccmPhaseLocalizationEnergyWithPotential_eq,
    he t, he 0, Real.cos_zero]
  ring

end RHTower
