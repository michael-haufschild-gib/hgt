import GaloisForLFunctions.RHTower.CCMFiniteLocalizationCover
import GaloisForLFunctions.RHTower.CCMLocalizationChainArithmetic

/-!
# Long-range arithmetic content survives complete localization

Every source admits a finite positive local decomposition. Its exact signed
error has a bounded common weight, but correlations farther apart than twice
the local radius survive with coefficient two. This identifies the part of
the arithmetic comparison that local mass conservation cannot erase.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmSmallBall_correlation_eq_zero_of_far {a : SuzukiPositiveAperture}
    (v : CCMComplexSmoothInteriorSource a) (c delta x y : ℝ)
    (hs : tsupport v ⊆ Metric.ball c delta) (hfar : 2 * delta ≤ dist x y) :
    (v y * star (v x)).re = 0 := by
  by_cases hx : v x = 0
  · simp only [hx, star_zero, mul_zero, Complex.zero_re]
  by_cases hy : v y = 0
  · simp only [hy, zero_mul, Complex.zero_re]
  have hxc := Metric.mem_ball.mp (hs (subset_closure hx))
  have hyc := Metric.mem_ball.mp (hs (subset_closure hy))
  have htri := dist_triangle x c y
  rw [dist_comm c y] at htri
  linarith only [hxc, hyc, htri, hfar]

theorem ccmThetaChainCross_eq_twice_correlation_of_far {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (delta x y : ℝ)
    (hs : ∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta)
    (hz : ∀ z, ccmLocalizationRemainder u angles z = 0) (hfar : 2 * delta ≤ dist x y) :
    ccmThetaChainCross u angles x y = 2 * (u y * star (u x)).re := by
  have hsum : ((ccmLocalizationPieces u angles).map (fun v => (v y * star (v x)).re)).sum = 0 := by
    apply List.sum_eq_zero
    intro r hr
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
    obtain ⟨c, hc⟩ := hs v hv
    exact ccmSmallBall_correlation_eq_zero_of_far v c delta x y hc hfar
  have h := ccmLocalization_correlation_conservation u angles x y
  rw [hz y, zero_mul, Complex.zero_re, hsum, zero_add] at h
  unfold ccmThetaChainCross thetaLocalizationChainWeight
  nlinarith only [h]

/-- An unconditional localization reserve for every actual source. Both error
integrals are literal, convergent arithmetic integrals; their comparison is not assumed. -/
theorem exists_ccmFiniteLocalization_arithmetic_reserve :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
      ∃ angles : List 𝓢(ℝ, ℝ),
        (∀ theta ∈ angles, HasCompactSupport theta) ∧
        (((ccmLocalizationPieces u angles).map
          (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
        (C * ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2 ≤
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector +
            (∫ p, ccmThetaChainPrimeDensity u angles p ∂thetaPrimeLinkMeasure) -
            (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure)) ∧
        (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
          thetaLocalizationChainWeight angles x y ≤ 4) ∧
        (∀ x y, 2 * delta ≤ dist x y →
          ccmThetaChainCross u angles x y = 2 * (u y * star (u x)).re) ∧
        (ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector < 0 ↔
          ((ccmLocalizationPieces u angles).map
            (fun v => ccmRestrictedWeilSourceQuadratic a v.toCCMFormVector)).sum <
          (∫ p, ccmThetaChainPrimeDensity u angles p ∂thetaPrimeLinkMeasure) -
            (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure)) := by
  obtain ⟨delta, C, hd, hC, hlocalize⟩ := exists_ccmFiniteLocalization_positive_assembly
  refine ⟨delta, C, hd, hC, fun a u => ?_⟩
  obtain ⟨angles, hc, hs, hz, hm, hgap, he⟩ := hlocalize a u
  rw [ccmLocalizationPrimeTotal_eq_integral, ccmLocalizationContinuousTotal_eq_integral] at he
  refine ⟨angles, hc, hm, ?_, (fun x y => ⟨thetaLocalizationChainWeight_nonneg angles x y,
    thetaLocalizationChainWeight_le_four angles x y⟩),
    (fun x y hfar => ccmThetaChainCross_eq_twice_correlation_of_far u angles delta x y hs hz hfar), ?_⟩
  · linarith only [hgap, he]
  · constructor <;> intro h <;> linarith only [he, h]

end RHTower
