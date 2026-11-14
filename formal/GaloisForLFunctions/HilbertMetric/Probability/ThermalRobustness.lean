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

/-- The finite Gibbs state as a probability law. -/
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

/-- The usual Pearson quotient formula is valid for every competing law. -/
theorem thermalPearsonDivergence_eq (β : ℝ) (E : ι → ℝ) (p : FiniteProbabilityLaw ι) :
    thermalPearsonDivergence β E p =
      (∑ i, p.prob i ^ (2 : ℕ) / finiteGibbsStateWeight β E i) - 1 := by
  unfold thermalPearsonDivergence
  rw [pearsonEnergy_eq_secondMoment]
  change finiteWeightedMean (finiteGibbsStateWeight β E)
      (fun i => (p.prob i / finiteGibbsStateWeight β E i) ^ (2 : ℕ)) -
      2 * finiteWeightedMean (finiteGibbsStateWeight β E)
        (fun i => p.prob i / finiteGibbsStateWeight β E i) + 1 = _
  rw [thermal_likelihood_mass]
  have hsecond : finiteWeightedMean (finiteGibbsStateWeight β E)
      (fun i => (p.prob i / finiteGibbsStateWeight β E i) ^ (2 : ℕ)) =
      ∑ i, p.prob i ^ (2 : ℕ) / finiteGibbsStateWeight β E i := by
    unfold finiteWeightedMean
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(finiteGibbsStateWeight_pos β E i).ne']
  rw [hsecond]
  ring

/-- Changing inverse temperature gives an exact three-partition-function divergence. -/
theorem thermalPearsonDivergence_thermalLaw (β γ : ℝ) (E : ι → ℝ) :
    thermalPearsonDivergence β E (thermalLaw γ E) =
      finiteGibbsPartition β E * finiteGibbsPartition (2 * γ - β) E /
        finiteGibbsPartition γ E ^ (2 : ℕ) - 1 := by
  rw [thermalPearsonDivergence_eq]
  have hterm (i : ι) :
      finiteGibbsStateWeight γ E i ^ (2 : ℕ) / finiteGibbsStateWeight β E i =
      finiteGibbsPartition β E / finiteGibbsPartition γ E ^ (2 : ℕ) *
        Real.exp (-(2 * γ - β) * E i) := by
    unfold finiteGibbsStateWeight
    field_simp [(finiteGibbsPartition_pos β E).ne',
      (finiteGibbsPartition_pos γ E).ne', (Real.exp_pos (-β * E i)).ne']
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change (∑ i, finiteGibbsStateWeight γ E i ^ (2 : ℕ) /
    finiteGibbsStateWeight β E i) - 1 = _
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  change finiteGibbsPartition β E / finiteGibbsPartition γ E ^ (2 : ℕ) *
    finiteGibbsPartition (2 * γ - β) E - 1 = _
  ring

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

/-- Thermal expectation error obeys the square-root divergence--variance certificate. -/
theorem thermal_expectation_shift_abs_le (β : ℝ) (E f : ι → ℝ)
    (p : FiniteProbabilityLaw ι) :
    |finiteWeightedMean p.prob f - finiteWeightedMean (finiteGibbsStateWeight β E) f| ≤
      Real.sqrt (thermalPearsonDivergence β E p *
        finiteWeightedVariance (finiteGibbsStateWeight β E) f) := by
  have h := Real.sqrt_le_sqrt (thermal_expectation_shift_sq_le β E f p)
  rwa [Real.sqrt_sq_eq_abs] at h

/-- Temperature misspecification has a closed variance-sensitive certificate. -/
theorem thermal_temperature_shift_sq_le (β γ : ℝ) (E f : ι → ℝ) :
    (finiteWeightedMean (finiteGibbsStateWeight γ E) f -
        finiteWeightedMean (finiteGibbsStateWeight β E) f) ^ (2 : ℕ) ≤
      (finiteGibbsPartition β E * finiteGibbsPartition (2 * γ - β) E /
        finiteGibbsPartition γ E ^ (2 : ℕ) - 1) *
        finiteWeightedVariance (finiteGibbsStateWeight β E) f := by
  have h := thermal_expectation_shift_sq_le β E f (thermalLaw γ E)
  rwa [thermalPearsonDivergence_thermalLaw] at h

end
end GaloisForLFunctions.HilbertMetric.Probability

#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_likelihood_expectation
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_likelihood_mass
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermalPearsonDivergence_eq
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermalPearsonDivergence_thermalLaw
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_expectation_shift_sq_le
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_expectation_shift_abs_le
#print axioms GaloisForLFunctions.HilbertMetric.Probability.thermal_temperature_shift_sq_le
