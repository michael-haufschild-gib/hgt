import GaloisForLFunctions.RHTower.CCM.CCMPrimeLocalizationStabilization

/-!
# The continuous arithmetic invariant of fine localization

Below the first prime translation, the sum of all localized Weil energies
plus the continuous correction is independent of the localization. Its value
is the literal Gamma and pole quadratic. This is an equality, not a sign
claim: the prime comparison needed for RH remains present.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

/-- Literal continuous Gamma and pole quadratic on an actual smooth source. -/
def ccmContinuousArithmeticQuadratic {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  (∫ p, thetaGammaPolarQuadraticDensity thetaCuspTiltSource (ccmThetaGroundProfile u) p
    ∂thetaContinuousLinkMeasure) - 2 * archConstant.re * thetaGroundNormSq (ccmThetaGroundProfile u)

/-- All local energies, including the remainder, compensated by the continuous correction. -/
def ccmLocalizationCompensatedEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) : ℝ :=
  ccmRestrictedWeilSourceQuadratic a (ccmLocalizationRemainder u angles).toCCMFormVector +
    ((ccmLocalizationPieces u angles).map
      (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum +
    ccmLocalizationContinuousTotal u angles

theorem ccmContinuousArithmeticQuadratic_eq_physical {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmContinuousArithmeticQuadratic u =
      ((∫ h in Ioc (0 : ℝ) (2 * a.1), ccmThetaPolarCorrelation u h) -
        ccmArchimedeanWeilDistribution (ccmComplexSmoothCrossCorrelationTest u u)).re :=
  thetaGammaPolarQuadratic_ccmSource_eq u

theorem ccmContinuousArithmeticQuadratic_eq_weil_add_prime {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmContinuousArithmeticQuadratic u = ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic, thetaFullArithmeticQuadratic]
  unfold ccmContinuousArithmeticQuadratic
  ring

theorem ccmLocalizationCompensatedEnergy_eq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    ccmLocalizationCompensatedEnergy u angles =
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
        ccmLocalizationPrimeTotal u angles := by
  unfold ccmLocalizationCompensatedEnergy
  linarith only [ccmLocalization_energy_conservation u angles]

theorem ccmLocalizationCompensatedEnergy_stabilized {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (delta : ℝ)
    (hs : ∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta)
    (hz : ∀ x, ccmLocalizationRemainder u angles x = 0) (hd : 2 * delta ≤ Real.log 2) :
    ccmLocalizationCompensatedEnergy u angles = ccmContinuousArithmeticQuadratic u := by
  rw [ccmLocalizationCompensatedEnergy_eq,
    ccmLocalizationPrimeTotal_stabilized u angles delta hs hz hd,
    ccmContinuousArithmeticQuadratic_eq_weil_add_prime]

/-- The invariant is realized by a finite compact smooth localization for every source. -/
theorem exists_ccmFiniteLocalization_continuous_invariant
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ,
        tsupport v ⊆ Metric.ball c (Real.log 2 / 4)) ∧
      (∀ x, ccmLocalizationRemainder u angles x = 0) ∧
      ccmLocalizationCompensatedEnergy u angles = ccmContinuousArithmeticQuadratic u ∧
      (((ccmLocalizationPieces u angles).map
        (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum +
        ccmLocalizationContinuousTotal u angles = ccmContinuousArithmeticQuadratic u) := by
  obtain ⟨angles, hc, hs, hz, hp⟩ := exists_ccmFiniteLocalization_stabilized_prime_total a u
  have he : ccmLocalizationCompensatedEnergy u angles = ccmContinuousArithmeticQuadratic u := by
    rw [ccmLocalizationCompensatedEnergy_eq, hp,
      ccmContinuousArithmeticQuadratic_eq_weil_add_prime]
  refine ⟨angles, hc, hs, hz, he, ?_⟩
  simpa only [ccmLocalizationCompensatedEnergy,
    ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hz, zero_add] using he

end RHTower
