import GaloisForLFunctions.BiarithmeticGeometry.Affine.MonomialMatrixFaithfulness
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear maps are determined by polynomial moment vectors

Coefficient recovery for distinct monomials determines rectangular matrices.
Passing through the coordinate matrix equivalence gives the corresponding
extensionality principle for linear maps, including coordinate projections.
-/

open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.BiarithmeticGeometry
noncomputable section

/-- Agreement on every evaluation vector of distinct monomials determines a linear map. -/
theorem linearMap_eq_of_monomial_eq {ι κ τ : Type*} [Fintype κ] [DecidableEq κ]
    (exponent : κ → (τ →₀ ℕ)) (hexponent : Function.Injective exponent)
    (T U : (κ → ℝ) →ₗ[ℝ] (ι → ℝ))
    (h : ∀ x : τ → ℝ, T (fun j => monomialFeature exponent j x) =
      U (fun j => monomialFeature exponent j x)) : T = U := by
  apply LinearMap.toMatrix'.injective
  apply matrix_eq_of_monomial_mulVec_eq exponent hexponent
  intro x
  simpa only [LinearMap.toMatrix'_mulVec] using h x

#print axioms linearMap_eq_of_monomial_eq

end
end GaloisForLFunctions.BiarithmeticGeometry
