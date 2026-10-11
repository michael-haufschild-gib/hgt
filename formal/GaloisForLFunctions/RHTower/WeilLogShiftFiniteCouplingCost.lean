import GaloisForLFunctions.HTGeometry.ConstitutiveHierarchicalMaximalCoupling
/-! Finite coupling costs, marginal pairings, and weak transport duality. -/

open scoped BigOperators NNReal
noncomputable section
namespace RHTower

def finiteWeilCouplingCost {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) : ℝ :=
  ∑ u, ∑ v, (gamma.plan u v : ℝ) * c u v

theorem finiteWeilCoupling_pairing {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (f : ι → ℝ) :
    (∑ u, (P u : ℝ) * f u) - (∑ v, (Q v : ℝ) * f v) =
      finiteWeilCouplingCost gamma (fun u v => f u - f v) := by
  have hr (u : ι) : (∑ v, (gamma.plan u v : ℝ)) = (P u : ℝ) := by
    simpa only [NNReal.coe_sum] using congrArg NNReal.toReal (gamma.row u)
  have hc (v : ι) : (∑ u, (gamma.plan u v : ℝ)) = (Q v : ℝ) := by
    simpa only [NNReal.coe_sum] using congrArg NNReal.toReal (gamma.col v)
  calc
    _ = (∑ u, ∑ v, (gamma.plan u v : ℝ) * f u) -
        (∑ v, ∑ u, (gamma.plan u v : ℝ) * f v) := by
      simp only [← Finset.sum_mul, hr, hc]
    _ = _ := by
      rw [Finset.sum_comm (f := fun v u => (gamma.plan u v : ℝ) * f v)]
      simp only [finiteWeilCouplingCost, mul_sub, Finset.sum_sub_distrib]

theorem finiteWeilCouplingCost_mono {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c d : ι → ι → ℝ)
    (hcd : ∀ u v, c u v ≤ d u v) : finiteWeilCouplingCost gamma c ≤ finiteWeilCouplingCost gamma d := by
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_left (hcd u v) (gamma.plan u v).coe_nonneg

theorem finiteWeilCoupling_dual_bound {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) (f : ι → ℝ)
    (hcf : ∀ u v, f u - f v ≤ c u v) :
    (∑ u, (P u : ℝ) * f u) - (∑ v, (Q v : ℝ) * f v) ≤ finiteWeilCouplingCost gamma c := by
  rw [finiteWeilCoupling_pairing gamma f]
  exact finiteWeilCouplingCost_mono gamma _ c hcf
end RHTower
