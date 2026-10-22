import GaloisForLFunctions.RHTower.CCM.CCMFarIntegerLogGapCoercivity
import GaloisForLFunctions.RHTower.CCM.CCMThetaArithmeticPhaseOrbit

/-!
# Positive full energy along every localized phase orbit in the far-gap class

Cosine and sine localization preserve each component's support and jointly
preserve its physical mass. The full complex-source gap consequently bounds
the earlier phase potential uniformly, for every smooth angle and every phase.
This conclusion does not require either localization-error term to have a sign.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

theorem support_ccmCosLocalizedSource_subset {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    Function.support (ccmCosLocalizedSource u theta) ⊆ Function.support u := by
  intro x hx hz
  exact hx (by rw [ccmCosLocalizedSource_apply, hz, mul_zero])

theorem support_ccmSinLocalizedSource_subset {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (theta : 𝓢(ℝ, ℝ)) :
    Function.support (ccmSinLocalizedSource u theta) ⊆ Function.support u := by
  intro x hx hz
  exact hx (by rw [ccmSinLocalizedSource_apply, hz, mul_zero])

theorem ccmCosLocalizedSource_combo {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (alpha beta : ℂ) (theta : 𝓢(ℝ, ℝ)) :
    ccmCosLocalizedSource (u.combo v w alpha beta) theta =
      (ccmCosLocalizedSource u theta).combo (ccmCosLocalizedSource v theta)
        (ccmCosLocalizedSource w theta) alpha beta := by
  apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
  funext x
  simp only [ccmCosLocalizedSource_apply, CCMComplexSmoothInteriorSource.combo_apply]
  ring

theorem ccmSinLocalizedSource_combo {a : SuzukiPositiveAperture}
    (u v w : CCMComplexSmoothInteriorSource a) (alpha beta : ℂ) (theta : 𝓢(ℝ, ℝ)) :
    ccmSinLocalizedSource (u.combo v w alpha beta) theta =
      (ccmSinLocalizedSource u theta).combo (ccmSinLocalizedSource v theta)
        (ccmSinLocalizedSource w theta) alpha beta := by
  apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
  funext x
  simp only [ccmSinLocalizedSource_apply, CCMComplexSmoothInteriorSource.combo_apply]
  ring

/-- The actual phase potential entering the Noether construction has a uniform physical
mass gap throughout this source class, even for angles varying inside both components. -/
theorem exists_ccmFarGap_phaseEnergy_gap :
    ∃ R kappa : ℝ, 0 < R ∧ 0 < kappa ∧
      ∀ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
        (c₁ c₂ r : ℝ), 0 ≤ r → R ≤ c₂ - c₁ - 2 * r →
        Function.support u ⊆ Metric.ball c₁ r →
        Function.support v ⊆ Metric.ball c₂ r →
        (∀ n : ℕ, 2 ≤ n → Real.log n ∉ Ioo (c₂ - c₁ - 2 * r) (c₂ - c₁ + 2 * r)) →
        ∀ (theta : 𝓢(ℝ, ℝ)) (t : ℝ),
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmPhaseLocalizationEnergy (u.combo v u 1 0) theta t := by
  obtain ⟨R, kappa, hR, hk, hcoercive⟩ := exists_ccm_farIntegerLogGap_coercivity
  refine ⟨R, kappa, hR, hk, fun a u v c₁ c₂ r hr hsep hu hv hfree theta t => ?_⟩
  let angle := ccmScaledPhaseAngle theta t
  have hc := hcoercive a (ccmCosLocalizedSource u angle) (ccmCosLocalizedSource v angle)
    c₁ c₂ r hr hsep ((support_ccmCosLocalizedSource_subset u angle).trans hu)
    ((support_ccmCosLocalizedSource_subset v angle).trans hv) hfree
  have hs := hcoercive a (ccmSinLocalizedSource u angle) (ccmSinLocalizedSource v angle)
    c₁ c₂ r hr hsep ((support_ccmSinLocalizedSource_subset u angle).trans hu)
    ((support_ccmSinLocalizedSource_subset v angle).trans hv) hfree
  have hmu : ‖ccmArchimedeanFormEmbedding a (ccmCosLocalizedSource u angle).toCCMFormVector‖ ^ 2 +
      ‖ccmArchimedeanFormEmbedding a (ccmSinLocalizedSource u angle).toCCMFormVector‖ ^ 2 =
      ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 := ccmPhysicalMass_localization u angle
  have hmv : ‖ccmArchimedeanFormEmbedding a (ccmCosLocalizedSource v angle).toCCMFormVector‖ ^ 2 +
      ‖ccmArchimedeanFormEmbedding a (ccmSinLocalizedSource v angle).toCCMFormVector‖ ^ 2 =
      ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2 := ccmPhysicalMass_localization v angle
  rw [ccmPhaseLocalizationEnergy, ccmCosLocalizedSource_combo, ccmSinLocalizedSource_combo]
  change _ ≤ ccmRestrictedWeilSourceQuadratic a
      ((ccmCosLocalizedSource u angle).combo (ccmCosLocalizedSource v angle)
        (ccmCosLocalizedSource u angle) 1 0).toCCMFormVector +
    ccmRestrictedWeilSourceQuadratic a
      ((ccmSinLocalizedSource u angle).combo (ccmSinLocalizedSource v angle)
        (ccmSinLocalizedSource u angle) 1 0).toCCMFormVector
  rw [← hmu, ← hmv]
  nlinarith only [hc.1, hs.1]

end RHTower
