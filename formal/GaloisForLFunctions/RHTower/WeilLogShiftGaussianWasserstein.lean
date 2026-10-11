import GaloisForLFunctions.RHTower.WeilLogShiftGaussianMeanGap

/-! Actual Wasserstein-one bounds between each projected finite law and its Gaussian target. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalGaussianWasserstein (r k : ℕ) (a b : ℝ) : ℝ :=
  wassersteinOne (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
    (finiteWeilProjectedGaussian a b : Measure ℝ)

theorem finiteWeilCanonicalGaussianWasserstein_nonneg (r k : ℕ) (a b : ℝ) :
    0 ≤ finiteWeilCanonicalGaussianWasserstein r k a b := by
  letI : Nonempty {π : Measure (ℝ × ℝ) //
      IsCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
        (finiteWeilProjectedGaussian a b : Measure ℝ) π} :=
    ⟨⟨(finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)),
      finiteWeilCanonicalGaussianCoupling_isCoupling r k a b⟩⟩
  unfold finiteWeilCanonicalGaussianWasserstein wassersteinOne
  exact le_ciInf fun π => integral_dist_nonneg π.val

theorem finiteWeilCanonicalGaussianWasserstein_le_mean_gap (r k : ℕ) (a b : ℝ) :
    finiteWeilCanonicalGaussianWasserstein r k a b ≤
      finiteWeilCanonicalGaussianMeanGap r k a b := by
  simpa only [finiteWeilCanonicalGaussianWasserstein, finiteWeilCanonicalGaussianMeanGap,
    Real.dist_eq] using
    wassersteinOne_le_integral (finiteWeilCanonicalGaussianCoupling_isCoupling r k a b)

theorem finiteWeilCanonicalGaussianWasserstein_le_sqrt_cost (r k : ℕ) (a b : ℝ) :
    finiteWeilCanonicalGaussianWasserstein r k a b ≤
      Real.sqrt (finiteWeilCanonicalGaussianQuadraticCost r k a b) :=
  (finiteWeilCanonicalGaussianWasserstein_le_mean_gap r k a b).trans
    (finiteWeilCanonicalGaussianMeanGap_le_sqrt_cost r k a b)

end RHTower
