import GaloisForLFunctions.HilbertMetric.Probability.PearsonRobustness
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# Robustness of finite thermal expectations

Finite Gibbs states are faithful at every real inverse temperature. Therefore
Pearson divergence from a Gibbs state bounds the error of every real observable
under an arbitrary competing probability law, with no support premise.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Probability
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The corpus's finite Gibbs state as a probability law. -/
def thermalLaw (β : ℝ) (E : ι → ℝ) : FiniteProbabilityLaw ι where
  prob := finiteGibbsStateWeight β E
  nonneg i := (finiteGibbsStateWeight_pos β E i).le
  sum_prob := sum_finiteGibbsStateWeight_eq_one β E

/-- Pearson divergence of a competing law from a faithful Gibbs state. -/
def thermalPearsonDivergence (β : ℝ) (E : ι → ℝ) (p : FiniteProbabilityLaw ι) : ℝ :=
  pearsonEnergy (thermalLaw β E) (fun i => p.prob i / finiteGibbsStateWeight β E i)

/-- Multiplication by the thermal likelihood ratio recovers the competing law. -/
theorem thermal_likelihood_expectation (β : ℝ) (E : ι → ℝ)
    (p : FiniteProbabilityLaw ι) (f : ι → ℝ) :
    finiteWeightedMean (finiteGibbsStateWeight β E)
        (fun i => (p.prob i / finiteGibbsStateWeight β E i) * f i) =
      finiteWeightedMean p.prob f := by
  unfold finiteWeightedMean
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(finiteGibbsStateWeight_pos β E i).ne']

/-- The thermal likelihood ratio has mean one without a support assumption. -/
theorem thermal_likelihood_mass (β : ℝ) (E : ι → ℝ) (p : FiniteProbabilityLaw ι) :
    finiteWeightedMean (finiteGibbsStateWeight β E)
      (fun i => p.prob i / finiteGibbsStateWeight β E i) = 1 := by
  have h := thermal_likelihood_expectation β E p (fun _ => 1)
  simpa only [mul_one, finiteWeightedMean, p.sum_prob] using h

/-- Order-two robustness for every finite observable and every competing law. -/
theorem thermal_expectation_shift_sq_le (β : ℝ) (E f : ι → ℝ)
    (p : FiniteProbabilityLaw ι) :
    (finiteWeightedMean p.prob f - finiteWeightedMean (finiteGibbsStateWeight β E) f) ^
        (2 : ℕ) ≤
      thermalPearsonDivergence β E p * finiteWeightedVariance (finiteGibbsStateWeight β E) f := by
  have h := likelihood_expectation_shift_sq_le (thermalLaw β E)
    (fun i => p.prob i / finiteGibbsStateWeight β E i) f
  change (finiteWeightedMean (finiteGibbsStateWeight β E)
      (fun i => (p.prob i / finiteGibbsStateWeight β E i) * f i) -
      finiteWeightedMean (finiteGibbsStateWeight β E)
        (fun i => p.prob i / finiteGibbsStateWeight β E i) *
        finiteWeightedMean (finiteGibbsStateWeight β E) f) ^ (2 : ℕ) ≤ _ at h
  rwa [thermal_likelihood_expectation, thermal_likelihood_mass, one_mul] at h

/-- Thermal expectation error obeys the paper's square-root certificate. -/
theorem thermal_expectation_shift_abs_le (β : ℝ) (E f : ι → ℝ)
    (p : FiniteProbabilityLaw ι) :
    |finiteWeightedMean p.prob f - finiteWeightedMean (finiteGibbsStateWeight β E) f| ≤
      Real.sqrt (thermalPearsonDivergence β E p *
        finiteWeightedVariance (finiteGibbsStateWeight β E) f) := by
  have h := Real.sqrt_le_sqrt (thermal_expectation_shift_sq_le β E f p)
  rwa [Real.sqrt_sq_eq_abs] at h

end
end GaloisForLFunctions.HilbertMetric.Probability
