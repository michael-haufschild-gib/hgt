import GaloisForLFunctions.HilbertMetric.QuantumInformation.SandwichedVariance
import GaloisForLFunctions.HTGeometry.FiniteUnitaryAdjointAutocorrelationLaw
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedFellerAdmission

/-!
# Unitary affinity and the variance deficit

For a unitary transition matrix, the symmetrized Born quadratic form is
exactly the total population. For probability populations, the geometric
quadratic form and skew information therefore add to one. Equality of the
affinity to one detects commutation with the diagonal state.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HilbertMetric.QuantumInformation
open GaloisForLFunctions.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Probability coordinates expressed in the nonnegative population type. -/
def lawPopulation (p : FiniteProbabilityLaw ι) : ι → ℝ≥0 :=
  fun i => ⟨p.prob i, p.nonneg i⟩

/-- Unitarity makes the Born quadratic form exactly the total state mass. -/
theorem bornQuadratic_unitary (p : ι → ℝ≥0) (U : Matrix.unitaryGroup ι ℂ) :
    bornQuadratic p (U : Matrix ι ι ℂ) = ∑ i, (p i : ℝ) := by
  change (∑ i, ∑ j, ((p i : ℝ) + p j) / 2 * finiteUnitaryEntryWeight U i j) = _
  simp_rw [show ∀ i j, ((p i : ℝ) + p j) / 2 * finiteUnitaryEntryWeight U i j =
    (p i : ℝ) * finiteUnitaryEntryWeight U i j / 2 +
      (p j : ℝ) * finiteUnitaryEntryWeight U i j / 2 by intro i j; ring]
  simp only [Finset.sum_add_distrib]
  have hr : (∑ i, ∑ j, (p i : ℝ) * finiteUnitaryEntryWeight U i j / 2) =
      (∑ i, (p i : ℝ)) / 2 := by
    simp_rw [← Finset.sum_div, ← Finset.mul_sum, sum_finiteUnitaryEntryWeight_row, mul_one]
    rw [Finset.sum_div]
  have hc : (∑ i, ∑ j, (p j : ℝ) * finiteUnitaryEntryWeight U i j / 2) =
      (∑ j, (p j : ℝ)) / 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, ← Finset.mul_sum, sum_finiteUnitaryEntryWeight_column, mul_one]
    rw [Finset.sum_div]
  rw [hr, hc]
  ring

/-- Unitary affinity plus skew information is exactly one. -/
theorem unitary_affinity_add_skew_eq_one (p : FiniteProbabilityLaw ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    sandwichedQuadratic (lawPopulation p) (U : Matrix ι ι ℂ) +
      skewInformation (lawPopulation p) (U : Matrix ι ι ℂ) = 1 := by
  have h := born_sub_sandwiched_eq_skewInformation (lawPopulation p) (U : Matrix ι ι ℂ)
  rw [bornQuadratic_unitary] at h
  have hp : (∑ i, (lawPopulation p i : ℝ)) = 1 := p.sum_prob
  linarith only [h, hp]

/-- Unitary affinity lies in the unit interval. -/
theorem unitary_affinity_mem_unitInterval (p : FiniteProbabilityLaw ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    sandwichedQuadratic (lawPopulation p) (U : Matrix ι ι ℂ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sandwichedQuadratic_nonneg _ _, ?_⟩
  have h := unitary_affinity_add_skew_eq_one p U
  linarith [skewInformation_nonneg (lawPopulation p) (U : Matrix ι ι ℂ)]

/-- Unit affinity occurs precisely when the unitary preserves the state. -/
theorem unitary_affinity_eq_one_iff_commute (p : FiniteProbabilityLaw ι)
    (U : Matrix.unitaryGroup ι ℂ) :
    sandwichedQuadratic (lawPopulation p) (U : Matrix ι ι ℂ) = 1 ↔
      Matrix.diagonal (fun i => (p.prob i : ℂ)) * (U : Matrix ι ι ℂ) =
        (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p.prob i : ℂ)) := by
  have h := unitary_affinity_add_skew_eq_one p U
  have hz : sandwichedQuadratic (lawPopulation p) (U : Matrix ι ι ℂ) = 1 ↔
      skewInformation (lawPopulation p) (U : Matrix ι ι ℂ) = 0 := by
    constructor <;> intro heq <;> linarith only [h, heq]
  rw [hz, skewInformation_eq_zero_iff_commute]
  rfl

end
end GaloisForLFunctions.HilbertMetric.QuantumInformation
