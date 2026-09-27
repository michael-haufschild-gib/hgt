import GaloisForLFunctions.RHTower.CCMLocalizationLongRange
import GaloisForLFunctions.RHTower.CCMPositiveNoetherPhaseWitness

/-!
# Arbitrarily large localization debt on a positive actual source

Small total support gives any requested local coercivity margin at fixed
aperture. A finite localization preserves physical mass, so its local energy
sum and compensating signed arithmetic error can become arbitrarily large.
The combined pointwise weight still stays in [0,4].
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem exists_ccmFiniteLocalization_prescribed_reserve (a : SuzukiPositiveAperture)
    (u : CCMComplexSmoothInteriorSource a) (L : ℝ) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (((ccmLocalizationPieces u angles).map
        (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
      (L * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
        ((ccmLocalizationPieces u angles).map
          (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum) ∧
      (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
        ((ccmLocalizationPieces u angles).map
          (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum -
        ccmLocalizationPrimeTotal u angles + ccmLocalizationContinuousTotal u angles) := by
  obtain ⟨delta, hd, hgap⟩ := exists_ccmSmooth_smallSupport_coercivity a L
  obtain ⟨angles, hc, hs, hz⟩ := exists_ccmFiniteLocalization_cover (delta / 4) (by positivity) u
  have hm := ccmLocalization_mass_conservation u angles
  rw [ccmSmoothSourcePhysicalMass_eq_zero_of_pointwise _ hz, zero_add] at hm
  have he := ccmLocalization_energy_conservation u angles
  rw [ccmSmoothSourceQuadratic_eq_zero_of_pointwise _ hz, zero_add] at he
  refine ⟨angles, hc, hm, ?_, he⟩
  have hlocal (v : CCMComplexSmoothInteriorSource a) (hv : v ∈ ccmLocalizationPieces u angles) :
      L * ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2 ≤
        ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector := by
    obtain ⟨c, hc⟩ := hs v hv
    have hvol : volume (Function.support v) ≤ ENNReal.ofReal delta := by
      calc
        _ ≤ volume (Metric.ball c (delta / 4)) := measure_mono (subset_closure.trans hc)
        _ = ENNReal.ofReal (2 * (delta / 4)) := Real.volume_ball _ _
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    have h := hgap v hvol
    change L * ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2 +
      (1 / 2 : ℝ) * ‖v.toCCMFormVector‖ ^ 2 ≤ _ at h
    linarith only [h, sq_nonneg ‖v.toCCMFormVector‖]
  have hsum := List.sum_le_sum hlocal
  rw [List.sum_map_mul_left, hm] at hsum
  exact hsum

theorem ccmLocalization_signed_debt_unbounded {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a)
    (hmass : 0 < ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) (B : ℝ) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (((ccmLocalizationPieces u angles).map
        (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
      (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
        thetaLocalizationChainWeight angles x y ≤ 4) ∧
      B < (∫ p, ccmThetaChainPrimeDensity u angles p ∂thetaPrimeLinkMeasure) -
        (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure) := by
  let L := (B + ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 1) /
    ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2
  obtain ⟨angles, hc, hm, hgap, he⟩ := exists_ccmFiniteLocalization_prescribed_reserve a u L
  have hL : L * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 =
      B + ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 1 := div_mul_cancel₀ _ hmass.ne'
  rw [hL] at hgap
  rw [ccmLocalizationPrimeTotal_eq_integral, ccmLocalizationContinuousTotal_eq_integral] at he
  refine ⟨angles, hc, hm, (fun x y => ⟨thetaLocalizationChainWeight_nonneg angles x y,
    thetaLocalizationChainWeight_le_four angles x y⟩), ?_⟩
  linarith only [hgap, he]

/-- A positive actual Weil source has arbitrarily large signed localization debt.
Thus debt positivity, or even unbounded debt under refinement, does not refute RH. -/
theorem exists_positive_ccmSource_unbounded_localization_debt :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧
      0 < ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ∧
      ∀ B : ℝ, ∃ angles : List 𝓢(ℝ, ℝ),
        (∀ theta ∈ angles, HasCompactSupport theta) ∧
        (((ccmLocalizationPieces u angles).map
          (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
        (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
          thetaLocalizationChainWeight angles x y ≤ 4) ∧
        B < (∫ p, ccmThetaChainPrimeDensity u angles p ∂thetaPrimeLinkMeasure) -
          (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure) := by
  obtain ⟨a, u, _, _, hq, _⟩ := exists_ccmArithmetic_positive_baseline_phase_potential
  have hne : ccmArchimedeanFormEmbedding a u.toCCMFormVector ≠ 0 := by
    intro hz
    have hv : u.toCCMFormVector = 0 := ccmArchimedeanFormEmbedding_injective a
      (by rw [hz, map_zero])
    rw [hv, ccmRestrictedWeilSourceQuadratic_zero] at hq
    exact (lt_irrefl 0) hq
  have hm := sq_pos_of_pos (norm_pos_iff.mpr hne)
  exact ⟨a, u, hq, hm, ccmLocalization_signed_debt_unbounded u hm⟩

end RHTower
