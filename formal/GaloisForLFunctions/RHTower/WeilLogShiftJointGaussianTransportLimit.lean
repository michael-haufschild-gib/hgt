import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianTests
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianTransportLimit

/-! The full Euclidean joint law converges in Wasserstein one to the diagonal Gaussian. -/

open MeasureTheory GaloisForLFunctions.HTGeometry Filter Topology

noncomputable section
namespace RHTower

def finiteWeilCanonicalJointGaussianWasserstein (r k : ℕ) : ℝ :=
  wassersteinOne
    (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))
    (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2)))

theorem finiteWeilCanonicalJointGaussianWasserstein_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalJointGaussianWasserstein r k := by
  letI : Nonempty {π : Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) //
      IsCoupling (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))
        (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) π} :=
    ⟨⟨(finiteWeilCanonicalJointGaussianCoupling r k :
      Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      finiteWeilCanonicalJointGaussianCoupling_isCoupling r k⟩⟩
  unfold finiteWeilCanonicalJointGaussianWasserstein wassersteinOne
  exact le_ciInf fun π => integral_dist_nonneg π.val

theorem finiteWeilCanonicalJointGaussianWasserstein_le_cost (r k : ℕ) :
    finiteWeilCanonicalJointGaussianWasserstein r k ≤ finiteWeilCanonicalJointGaussianCost r k :=
  wassersteinOne_le_integral (finiteWeilCanonicalJointGaussianCoupling_isCoupling r k)

theorem tendsto_finiteWeilCanonicalJointGaussianCost_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalJointGaussianCost r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalJointGaussianCost_nonneg r _)
    (fun r => finiteWeilCanonicalJointGaussianCost_bound r _)
  simpa only [mul_zero, add_zero] using
    (tendsto_finiteWeilCanonicalJointDiagonalGap_zero t).add
      ((tendsto_finiteWeilCanonicalGaussianMeanGap_zero t 1 0).const_mul (2 : ℝ))

theorem tendsto_finiteWeilCanonicalJointGaussianWasserstein_zero (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalJointGaussianWasserstein r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 0) :=
  squeeze_zero (fun r => finiteWeilCanonicalJointGaussianWasserstein_nonneg r _)
    (fun r => finiteWeilCanonicalJointGaussianWasserstein_le_cost r _)
    (tendsto_finiteWeilCanonicalJointGaussianCost_zero t)

theorem tendsto_finiteWeilCanonicalJointGaussianLipschitz_integral_gap_zero
    (t : ℕ → ℕ) (L : NNReal)
    (f : ℕ → {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Tendsto (fun r =>
      |(∫ x, (f r).val x ∂(finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r) :
          Measure (EuclideanSpace ℝ (Fin 2)))) -
        (∫ x, (f r).val x ∂(finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))))|)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun r => abs_nonneg _)
    (fun r => finiteWeilCanonicalJointGaussianLipschitz_integral_gap r _ L (f r))
  simpa only [mul_zero] using (tendsto_finiteWeilCanonicalJointGaussianCost_zero t).const_mul (L : ℝ)

end RHTower
