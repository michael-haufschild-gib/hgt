import GaloisForLFunctions.RHTower.ThetaPrimeLogCellCoercivity
import GaloisForLFunctions.RHTower.CCM.CCMFarGapPhaseCoercivity

/-!
# Complex CCM sources and phase energies in cofinal prime-log cells

The real coercivity theorem extends to arbitrary complex amplitudes, then to
the literal CCM form and every smooth localized phase orbit. Its arithmetic
budget retains all proper-prime-power translations in the selected cells.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem exists_thetaComplex_cofinal_primeLogCell_coercivity :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ (chi eta : 𝓢(ℝ, ℂ)), HasCompactSupport chi → HasCompactSupport eta →
      ∀ c₁ c₂ r : ℝ, 0 ≤ r →
        Function.support chi ⊆ Metric.ball c₁ r →
        Function.support eta ⊆ Metric.ball c₂ r →
        xiMassNthPrimeLogHeight n ≤ c₂ - c₁ - 2 * r →
        c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (n + 1) →
        kappa * (thetaGroundNormSq chi + thetaGroundNormSq eta) ≤
          thetaFullArithmeticQuadratic (chi + eta) ∧
        kappa * (thetaGroundNormSq chi + thetaGroundNormSq eta) ≤
          thetaFullArithmeticQuadratic (chi - eta) := by
  obtain ⟨kappa, hk, hreal⟩ := exists_thetaReal_cofinal_primeLogCell_coercivity
  refine ⟨kappa, hk, fun N => ?_⟩
  obtain ⟨n, hn, hcell⟩ := hreal N
  refine ⟨n, hn, fun chi eta hc he c₁ c₂ r hr hs ht hleft hright => ?_⟩
  have hRe := hcell (thetaRealComponent chi) (thetaRealComponent eta)
    (hasCompactSupport_thetaRealComponent chi hc) (hasCompactSupport_thetaRealComponent eta he)
    c₁ c₂ r hr ((support_thetaRealComponent_subset chi).trans hs)
    ((support_thetaRealComponent_subset eta).trans ht) hleft hright
  have hIm := hcell (thetaImagComponent chi) (thetaImagComponent eta)
    (hasCompactSupport_thetaImagComponent chi hc) (hasCompactSupport_thetaImagComponent eta he)
    c₁ c₂ r hr ((support_thetaImagComponent_subset chi).trans hs)
    ((support_thetaImagComponent_subset eta).trans ht) hleft hright
  rw [thetaGroundNormSq_realImag chi, thetaGroundNormSq_realImag eta,
    thetaFullArithmeticQuadratic_realImag, thetaFullArithmeticQuadratic_realImag,
    thetaRealComponent_add, thetaImagComponent_add, thetaRealComponent_sub, thetaImagComponent_sub]
  constructor <;> nlinarith only [hRe.1, hRe.2, hIm.1, hIm.2]

/-- A genuine full Weil gap for all complex smooth pairs fitting in selected cofinal cells. -/
theorem exists_ccm_cofinal_primeLogCell_coercivity :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
        (c₁ c₂ r : ℝ), 0 ≤ r →
        Function.support u ⊆ Metric.ball c₁ r →
        Function.support v ⊆ Metric.ball c₂ r →
        xiMassNthPrimeLogHeight n ≤ c₂ - c₁ - 2 * r →
        c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (n + 1) →
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmRestrictedWeilSourceQuadratic a (u.combo v u 1 0).toCCMFormVector ∧
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmRestrictedWeilSourceQuadratic a (u.combo v u (-1) 0).toCCMFormVector := by
  obtain ⟨kappa, hk, hcomplex⟩ := exists_thetaComplex_cofinal_primeLogCell_coercivity
  refine ⟨kappa, hk, fun N => ?_⟩
  obtain ⟨n, hn, hcell⟩ := hcomplex N
  refine ⟨n, hn, fun a u v c₁ c₂ r hr hs ht hleft hright => ?_⟩
  have h := hcell (ccmThetaGroundProfile u) (ccmThetaGroundProfile v)
    (hasCompactSupport_ccmThetaGroundProfile u) (hasCompactSupport_ccmThetaGroundProfile v)
    c₁ c₂ r hr (by rwa [support_ccmThetaGroundProfile])
    (by rwa [support_ccmThetaGroundProfile]) hleft hright
  rw [thetaGroundNormSq_ccmProfile_eq_physical, thetaGroundNormSq_ccmProfile_eq_physical,
    ← ccmThetaGroundProfile_combo_add, ← ccmThetaGroundProfile_combo_sub,
    ← ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic,
    ← ccmRestrictedWeilSourceQuadratic_eq_thetaFullArithmetic] at h
  exact h

/-- The same cells have a positive mass gap along every smooth local phase potential. -/
theorem exists_ccm_cofinal_primeLogCell_phaseEnergy_gap :
    ∃ kappa : ℝ, 0 < kappa ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ (a : SuzukiPositiveAperture) (u v : CCMComplexSmoothInteriorSource a)
        (c₁ c₂ r : ℝ), 0 ≤ r →
        Function.support u ⊆ Metric.ball c₁ r →
        Function.support v ⊆ Metric.ball c₂ r →
        xiMassNthPrimeLogHeight n ≤ c₂ - c₁ - 2 * r →
        c₂ - c₁ + 2 * r ≤ xiMassNthPrimeLogHeight (n + 1) →
        ∀ (theta : 𝓢(ℝ, ℝ)) (t : ℝ),
        kappa * (‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 +
            ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2) ≤
          ccmPhaseLocalizationEnergy (u.combo v u 1 0) theta t := by
  obtain ⟨kappa, hk, hcoercive⟩ := exists_ccm_cofinal_primeLogCell_coercivity
  refine ⟨kappa, hk, fun N => ?_⟩
  obtain ⟨n, hn, hcell⟩ := hcoercive N
  refine ⟨n, hn, fun a u v c₁ c₂ r hr hu hv hleft hright theta t => ?_⟩
  let angle := ccmScaledPhaseAngle theta t
  have hc := hcell a (ccmCosLocalizedSource u angle) (ccmCosLocalizedSource v angle)
    c₁ c₂ r hr ((support_ccmCosLocalizedSource_subset u angle).trans hu)
    ((support_ccmCosLocalizedSource_subset v angle).trans hv) hleft hright
  have hs := hcell a (ccmSinLocalizedSource u angle) (ccmSinLocalizedSource v angle)
    c₁ c₂ r hr ((support_ccmSinLocalizedSource_subset u angle).trans hu)
    ((support_ccmSinLocalizedSource_subset v angle).trans hv) hleft hright
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
