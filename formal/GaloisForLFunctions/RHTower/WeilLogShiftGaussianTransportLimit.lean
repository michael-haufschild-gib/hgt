import GaloisForLFunctions.RHTower.WeilLogShiftGaussianLipschitzBound
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianWasserstein
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianQuadraticLimit

/-! Gaussian transport convergence controls rank-dependent, unbounded Lipschitz tests. -/

open MeasureTheory Filter Topology

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalGaussianMeanGap_zero (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => finiteWeilCanonicalGaussianMeanGap r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 0) := by
  have h : Tendsto (fun r => Real.sqrt
      (finiteWeilCanonicalGaussianQuadraticCost r (2 * (r + 1) ^ 2 + t r) a b))
      atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_finiteWeilCanonicalGaussianQuadraticCost_zero t a b)
  rw [Real.sqrt_zero] at h
  exact squeeze_zero (fun r => finiteWeilCanonicalGaussianMeanGap_nonneg r _ a b)
    (fun r => finiteWeilCanonicalGaussianMeanGap_le_sqrt_cost r _ a b) h

theorem tendsto_finiteWeilCanonicalGaussianWasserstein_zero (t : ℕ → ℕ) (a b : ℝ) :
    Tendsto (fun r => finiteWeilCanonicalGaussianWasserstein r (2 * (r + 1) ^ 2 + t r) a b)
      atTop (𝓝 0) :=
  squeeze_zero (fun r => finiteWeilCanonicalGaussianWasserstein_nonneg r _ a b)
    (fun r => finiteWeilCanonicalGaussianWasserstein_le_mean_gap r _ a b)
    (tendsto_finiteWeilCanonicalGaussianMeanGap_zero t a b)

theorem tendsto_finiteWeilCanonicalGaussianLipschitz_integral_gap_zero
    (t : ℕ → ℕ) (a b : ℝ) (L : NNReal) (f : ℕ → {f : ℝ → ℝ // LipschitzWith L f}) :
    Tendsto (fun r =>
      |(∫ x, (f r).val x ∂(finiteWeilCanonicalProjectedProbabilityLaw r
          (2 * (r + 1) ^ 2 + t r) a b : Measure ℝ)) -
        (∫ x, (f r).val x ∂(finiteWeilProjectedGaussian a b : Measure ℝ))|)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalGaussianLipschitz_integral_gap_le_mean r _ a b L (f r))
  simpa only [mul_zero] using
    (tendsto_finiteWeilCanonicalGaussianMeanGap_zero t a b).const_mul (L : ℝ)

end RHTower
