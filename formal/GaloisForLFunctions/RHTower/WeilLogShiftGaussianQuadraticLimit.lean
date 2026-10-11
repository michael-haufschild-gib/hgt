import GaloisForLFunctions.RHTower.WeilLogShiftGaussianCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftSignedQuadratic

/-! Every projection has vanishing quadratic transport cost to its Gaussian limit. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry Filter Set
open scoped Topology

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero
    (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => finiteWeilCanonicalGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 0) := by
  by_cases hab : a + b = 0
  · have hb : b = -a := by linarith only [hab]
    subst b
    simp_rw [finiteWeilCanonicalGaussianQuadraticCost_antidiagonal]
    have h := tendsto_finiteWeilCanonicalProjectedProbabilityLaw_second_moment t a (-a)
    rw [finiteWeilProjectedGaussian_second_moment] at h
    simpa only [add_neg_cancel, show (0 : ℝ) ^ 2 = 0 by norm_num, zero_div] using h
  · let v : NNReal := NNReal.mk ((a + b) ^ 2 / 4) (by positivity)
    have hv : v ≠ 0 := by
      apply ne_of_gt
      change (0 : ℝ) < (a + b) ^ 2 / 4
      positivity
    have hae : ∀ᵐ p ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        Tendsto (fun r => quantile (finiteWeilCanonicalProjectedProbabilityLaw r
          (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ) p) atTop
          (𝓝 (quantile (finiteWeilProjectedGaussian a b : Measure ℝ) p)) := by
      apply (ae_restrict_iff' measurableSet_Ioo).mpr
      refine Eventually.of_forall fun p hp => ?_
      exact finiteWeil_gaussian_quantile_tendsto
        (fun r => finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) a b)
        v hv (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t a b) ⟨p, hp⟩
    exact finiteWeil_tendsto_monotoneCoupling_signed_sq
      (fun r => (finiteWeilCanonicalProjectedProbabilityLaw r
        (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ)) (finiteWeilProjectedGaussian a b : Measure ℝ)
      (fun r => finiteWeilCanonicalProjectedProbabilityLaw_integrable r _ a b _)
      (finiteWeilProjectedGaussian_integrable_sq a b) hae
      (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_second_moment t a b)

theorem tendsto_finiteWeilCanonicalProjectedMutualQuadraticCost_zero
    (s t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => ∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + s r) a b : Measure ℝ)
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ)))
      atTop (𝓝 0) := by
  exact tendsto_integral_monotoneCoupling_pair_sq
    (fun r => (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + s r) a b : Measure ℝ))
    (fun r => (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ))
    (finiteWeilProjectedGaussian a b : Measure ℝ)
    (fun r => finiteWeilCanonicalProjectedProbabilityLaw_integrable r _ a b _)
    (fun r => finiteWeilCanonicalProjectedProbabilityLaw_integrable r _ a b _)
    (finiteWeilProjectedGaussian_integrable_sq a b)
    (tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero s a b)
    (tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero t a b)

end RHTower
