import GaloisForLFunctions.RHTower.CCMLocalizationUnboundedDebt

/-!
# Prime localization stays bounded while continuous compensation diverges

The full prime correlation is absolutely integrable for each fixed source.
The common weight in [0,4] therefore bounds every prime localization total by
one source-dependent constant, independently of the partition. Arbitrarily
fine localization can still drive the signed continuous total below any real
bound, even on an explicitly positive actual Weil source.
-/

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmThetaPrimeCrossDensity_physical {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (p : ℕ × ℝ) :
    thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
      (ccmThetaGroundProfile u).toBoundedContinuousFunction p =
      ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 *
        (u (p.2 + Real.log p.1) * star (u p.2)).re := by
  rw [thetaPrimeScalingCrossDensity, thetaPrimeLinkDensity_eq_real, Complex.ofReal_re]
  change (ccmThetaGroundProfile u (p.2 + Real.log p.1) *
      star (ccmThetaGroundProfile u p.2)).re *
    (ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 *
      thetaCuspFullSource p.2 * thetaCuspFullSource (p.2 + Real.log p.1)) = _
  calc
    _ = ArithmeticFunction.vonMangoldt p.1 / Real.sqrt p.1 *
        (thetaCuspFullSource p.2 * thetaCuspFullSource (p.2 + Real.log p.1) *
          (ccmThetaGroundProfile u (p.2 + Real.log p.1) *
            star (ccmThetaGroundProfile u p.2)).re) := by ring
    _ = _ := by rw [ccmThetaGroundProfile_cross]

theorem ccmThetaChainPrimeDensity_eq_weight_mul {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (p : ℕ × ℝ) :
    ccmThetaChainPrimeDensity u angles p =
      thetaLocalizationChainWeight angles p.2 (p.2 + Real.log p.1) *
        thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
          (ccmThetaGroundProfile u).toBoundedContinuousFunction p := by
  rw [ccmThetaPrimeCrossDensity_physical]
  unfold ccmThetaChainPrimeDensity ccmThetaChainCross
  ring

def ccmLocalizationPrimeBudget {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ℝ :=
  4 * ∫ p, ‖thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
    (ccmThetaGroundProfile u).toBoundedContinuousFunction p‖ ∂thetaPrimeLinkMeasure

theorem ccmLocalizationPrimeBudget_nonneg {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : 0 ≤ ccmLocalizationPrimeBudget u :=
  mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))

theorem abs_ccmLocalizationPrimeTotal_le_budget {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) :
    |ccmLocalizationPrimeTotal u angles| ≤ ccmLocalizationPrimeBudget u := by
  rw [ccmLocalizationPrimeTotal_eq_integral]
  have hbound (p : ℕ × ℝ) : ‖ccmThetaChainPrimeDensity u angles p‖ ≤
      4 * ‖thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction p‖ := by
    rw [ccmThetaChainPrimeDensity_eq_weight_mul, norm_mul,
      Real.norm_of_nonneg (thetaLocalizationChainWeight_nonneg angles _ _)]
    exact mul_le_mul_of_nonneg_right (thetaLocalizationChainWeight_le_four angles _ _)
      (norm_nonneg _)
  calc
    _ ≤ ∫ p, ‖ccmThetaChainPrimeDensity u angles p‖ ∂thetaPrimeLinkMeasure :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p, 4 * ‖thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction p‖ ∂thetaPrimeLinkMeasure :=
      integral_mono (integrable_ccmThetaChainPrimeDensity u angles).norm
        ((integrable_thetaPrimeScalingCrossDensity _ _ _).norm.const_mul 4) hbound
    _ = _ := by rw [integral_const_mul]; rfl

theorem ccmLocalization_continuous_total_unbounded_below {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a)
    (hmass : 0 < ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) (R : ℝ) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (((ccmLocalizationPieces u angles).map
        (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
        ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
      (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
        thetaLocalizationChainWeight angles x y ≤ 4) ∧
      (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure) < R := by
  obtain ⟨angles, hc, hm, hw, hd⟩ := ccmLocalization_signed_debt_unbounded u hmass
    (ccmLocalizationPrimeBudget u - R)
  have hp := (abs_le.mp (abs_ccmLocalizationPrimeTotal_le_budget u angles)).2
  rw [ccmLocalizationPrimeTotal_eq_integral] at hp
  exact ⟨angles, hc, hm, hw, by linarith only [hd, hp]⟩

/-- The effect occurs on a source with strictly positive complete Weil energy,
with one uniform bound for every prime total and no bound below for continuous totals. -/
theorem exists_positive_ccmSource_bounded_prime_unbounded_continuous_localization :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) (K : ℝ),
      0 < ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ∧ 0 ≤ K ∧
      (∀ angles : List 𝓢(ℝ, ℝ), |ccmLocalizationPrimeTotal u angles| ≤ K) ∧
      ∀ R : ℝ, ∃ angles : List 𝓢(ℝ, ℝ),
        (∀ theta ∈ angles, HasCompactSupport theta) ∧
        (((ccmLocalizationPieces u angles).map
          (fun v => ‖ccmArchimedeanFormEmbedding a v.toCCMFormVector‖ ^ 2)).sum =
          ‖ccmArchimedeanFormEmbedding a u.toCCMFormVector‖ ^ 2) ∧
        (∀ x y, 0 ≤ thetaLocalizationChainWeight angles x y ∧
          thetaLocalizationChainWeight angles x y ≤ 4) ∧
        (∫ p, ccmThetaChainContinuousDensity u angles p ∂thetaContinuousLinkMeasure) < R := by
  obtain ⟨a, u, hq, hm, _⟩ := exists_positive_ccmSource_unbounded_localization_debt
  exact ⟨a, u, ccmLocalizationPrimeBudget u, hq, ccmLocalizationPrimeBudget_nonneg u,
    abs_ccmLocalizationPrimeTotal_le_budget u, ccmLocalization_continuous_total_unbounded_below u hm⟩

end RHTower
