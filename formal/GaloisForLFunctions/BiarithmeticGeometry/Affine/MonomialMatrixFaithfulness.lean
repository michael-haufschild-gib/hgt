import GaloisForLFunctions.HilbertMetric.PolynomialMomentCancellation

/-!
# Matrix actions are determined by polynomial moment vectors

Distinct real monomials admit exact finite coefficient recovery. Applying
that recovery to each matrix row proves that agreement on every moment
vector determines a matrix, even though the moment image has smaller
dimension than its ambient coordinate space.
-/

open Matrix
open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.BiarithmeticGeometry
noncomputable section

/-- Matrices agreeing on every evaluation vector of distinct monomials are equal. -/
theorem matrix_eq_of_monomial_mulVec_eq {ι κ τ : Type*} [Fintype κ] [DecidableEq κ]
    (exponent : κ → (τ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (M N : Matrix ι κ ℝ)
    (h : ∀ x : τ → ℝ, M *ᵥ (fun j => monomialFeature exponent j x) =
      N *ᵥ (fun j => monomialFeature exponent j x)) : M = N := by
  obtain ⟨nodes, dual, _, _, hrec⟩ := exists_injective_nodes_dual_reconstruction
    (monomialFeature exponent) (monomialFeature_linearIndependent exponent hexponent)
  ext a b
  calc
    M a b = ∑ i, dual b i * (∑ j, M a j * monomialFeature exponent j (nodes i)) :=
      (hrec (M a) b).symm
    _ = ∑ i, dual b i * (∑ j, N a j * monomialFeature exponent j (nodes i)) := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact congrFun (h (nodes i)) a
    _ = N a b := hrec (N a) b

#print axioms matrix_eq_of_monomial_mulVec_eq

end
end GaloisForLFunctions.BiarithmeticGeometry
