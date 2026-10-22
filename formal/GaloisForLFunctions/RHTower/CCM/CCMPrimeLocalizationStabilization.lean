import GaloisForLFunctions.RHTower.CCM.CCMLocalizationPrimeBudget

/-!
# Exact stabilization below the first prime translation

When every localized piece fits in a ball of diameter at most log 2 and the
remainder vanishes, every active prime translation joins distinct pieces.
The complete prime localization total is then exactly twice the original
prime correlation, independently of the chosen finite localization.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmThetaChainPrimeDensity_eq_twice_of_small_pieces {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (delta : ℝ)
    (hs : ∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta)
    (hz : ∀ x, ccmLocalizationRemainder u angles x = 0)
    (hd : 2 * delta ≤ Real.log 2) (p : ℕ × ℝ) :
    ccmThetaChainPrimeDensity u angles p =
      2 * thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction p := by
  rw [ccmThetaPrimeCrossDensity_physical]
  by_cases hn : ArithmeticFunction.vonMangoldt p.1 = 0
  · simp only [ccmThetaChainPrimeDensity, hn, zero_div, zero_mul, mul_zero]
  have hn2 : 2 ≤ p.1 := by
    have := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hn).one_lt
    omega
  have hlog : Real.log 2 ≤ Real.log p.1 :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hdist : dist p.2 (p.2 + Real.log p.1) = Real.log p.1 := by
    rw [Real.dist_eq, sub_add_cancel_left, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p.1)))]
  have hfar : 2 * delta ≤ dist p.2 (p.2 + Real.log p.1) := by
    rw [hdist]
    exact hd.trans hlog
  rw [ccmThetaChainPrimeDensity,
    ccmThetaChainCross_eq_twice_correlation_of_far u angles delta _ _ hs hz hfar]
  ring

theorem ccmLocalizationPrimeTotal_stabilized {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (angles : List 𝓢(ℝ, ℝ)) (delta : ℝ)
    (hs : ∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ, tsupport v ⊆ Metric.ball c delta)
    (hz : ∀ x, ccmLocalizationRemainder u angles x = 0) (hd : 2 * delta ≤ Real.log 2) :
    ccmLocalizationPrimeTotal u angles =
      2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  rw [ccmLocalizationPrimeTotal_eq_integral]
  simp_rw [ccmThetaChainPrimeDensity_eq_twice_of_small_pieces u angles delta hs hz hd]
  rw [integral_const_mul]
  rfl

/-- The prime total is already fixed at finite scale, with no limiting process. -/
theorem exists_ccmFiniteLocalization_stabilized_prime_total
    (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a) :
    ∃ angles : List 𝓢(ℝ, ℝ),
      (∀ theta ∈ angles, HasCompactSupport theta) ∧
      (∀ v ∈ ccmLocalizationPieces u angles, ∃ c : ℝ,
        tsupport v ⊆ Metric.ball c (Real.log 2 / 4)) ∧
      (∀ x, ccmLocalizationRemainder u angles x = 0) ∧
      ccmLocalizationPrimeTotal u angles =
        2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
          (ccmThetaGroundProfile u).toBoundedContinuousFunction := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨angles, hc, hs, hz⟩ := exists_ccmFiniteLocalization_cover
    (Real.log 2 / 4) (by positivity) u
  exact ⟨angles, hc, hs, hz,
    ccmLocalizationPrimeTotal_stabilized u angles _ hs hz (by linarith)⟩

end RHTower
