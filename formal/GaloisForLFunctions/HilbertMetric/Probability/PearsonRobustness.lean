import GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Variance-sensitive robustness under a finite likelihood change

The classical order-two bound controls expectation error by the product of
Pearson divergence and baseline variance. The centered form below works for
arbitrary likelihood functions, including unnormalized and signed ones.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Pearson energy of a likelihood relative to a finite probability law. -/
def pearsonEnergy (p : FiniteProbabilityLaw ι) (r : ι → ℝ) : ℝ :=
  ∑ i, p.prob i * (r i - 1) ^ (2 : ℕ)

theorem pearsonEnergy_nonneg (p : FiniteProbabilityLaw ι) (r : ι → ℝ) :
    0 ≤ pearsonEnergy p r :=
  Finset.sum_nonneg fun i _ => mul_nonneg (p.nonneg i) (sq_nonneg _)

/-- Zero Pearson energy detects a unit likelihood on the support. -/
theorem pearsonEnergy_eq_zero_iff (p : FiniteProbabilityLaw ι) (r : ι → ℝ) :
    pearsonEnergy p r = 0 ↔ ∀ i, p.prob i = 0 ∨ r i = 1 := by
  unfold pearsonEnergy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    mul_nonneg (p.nonneg i) (sq_nonneg _))]
  simp only [Finset.mem_univ, forall_const, mul_eq_zero, sq_eq_zero_iff, sub_eq_zero]

/-- Pearson energy separates the likelihood second moment from its mass. -/
theorem pearsonEnergy_eq_secondMoment (p : FiniteProbabilityLaw ι) (r : ι → ℝ) :
    pearsonEnergy p r = finiteWeightedMean p.prob (fun i => r i ^ (2 : ℕ)) -
      2 * finiteWeightedMean p.prob r + 1 := by
  unfold pearsonEnergy finiteWeightedMean
  simp_rw [show ∀ i, p.prob i * (r i - 1) ^ (2 : ℕ) =
    p.prob i * r i ^ (2 : ℕ) - 2 * (p.prob i * r i) + p.prob i by intro i; ring]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_prob]

/-- A finite likelihood change has a variance-sensitive expectation bound,
without a support, positivity, or normalization premise on the likelihood. -/
theorem likelihood_expectation_shift_sq_le (p : FiniteProbabilityLaw ι) (r f : ι → ℝ) :
    (finiteWeightedMean p.prob (fun i => r i * f i) -
        finiteWeightedMean p.prob r * finiteWeightedMean p.prob f) ^ (2 : ℕ) ≤
      pearsonEnergy p r * finiteWeightedVariance p.prob f := by
  have hid : (∑ i, p.prob i * (r i - 1) * (f i - finiteWeightedMean p.prob f)) =
      finiteWeightedMean p.prob (fun i => r i * f i) -
        finiteWeightedMean p.prob r * finiteWeightedMean p.prob f := by
    simp_rw [show ∀ i, p.prob i * (r i - 1) * (f i - finiteWeightedMean p.prob f) =
      p.prob i * (r i * f i) - p.prob i * r i * finiteWeightedMean p.prob f -
        p.prob i * f i + p.prob i * finiteWeightedMean p.prob f by intro i; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, p.sum_prob, one_mul]
    unfold finiteWeightedMean
    ring
  rw [← hid]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i _
    exact mul_nonneg (p.nonneg i) (sq_nonneg (r i - 1))
  · intro i _
    exact mul_nonneg (p.nonneg i) (sq_nonneg (f i - finiteWeightedMean p.prob f))
  · intro i _
    exact le_of_eq (by ring)

/-- Square-root form of the order-two robustness certificate. -/
theorem likelihood_expectation_shift_abs_le (p : FiniteProbabilityLaw ι) (r f : ι → ℝ) :
    |finiteWeightedMean p.prob (fun i => r i * f i) -
        finiteWeightedMean p.prob r * finiteWeightedMean p.prob f| ≤
      Real.sqrt (pearsonEnergy p r * finiteWeightedVariance p.prob f) := by
  have h := Real.sqrt_le_sqrt (likelihood_expectation_shift_sq_le p r f)
  rwa [Real.sqrt_sq_eq_abs] at h

end
end GaloisForLFunctions.HilbertMetric.Probability
