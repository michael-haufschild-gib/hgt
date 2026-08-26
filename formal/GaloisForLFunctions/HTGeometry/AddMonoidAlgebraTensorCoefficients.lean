import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Coefficients of a group-algebra tensor product

An additive monoid algebra is a wrapper around a finitely supported scalar family.  Tensoring it
with an arbitrary module therefore gives a finitely supported family of module-valued
coefficients.  This file packages that canonical linear equivalence and its pointwise API.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry
namespace AddMonoidAlgebraTensorCoefficients

noncomputable section

variable (k M : Type*) [Field k]

/-- Coefficients identify an additive monoid algebra with its underlying finitely supported
family. -/
noncomputable def coeffLinearEquiv : AddMonoidAlgebra k M ≃ₗ[k] (M →₀ k) where
  toFun := AddMonoidAlgebra.coeff
  invFun := AddMonoidAlgebra.ofCoeff
  map_add' := AddMonoidAlgebra.coeff_add
  map_smul' := AddMonoidAlgebra.coeff_smul
  left_inv _ := rfl
  right_inv _ := rfl

variable {M}

@[simp]
theorem coeffLinearEquiv_single (m : M) (a : k) :
    coeffLinearEquiv k M (AddMonoidAlgebra.single m a) = Finsupp.single m a := rfl

variable (N : Type*) [AddCommGroup N] [Module k N]

/-- Tensoring an additive monoid algebra with a module gives finitely supported module-valued
coefficients. -/
noncomputable def tensorCoeffEquiv :
    AddMonoidAlgebra k M ⊗[k] N ≃ₗ[k] (M →₀ N) := by
  classical
  exact ((coeffLinearEquiv k M).rTensor N).trans
    (TensorProduct.finsuppScalarLeft k N M)

@[simp]
theorem tensorCoeffEquiv_tmul_apply
    (x : AddMonoidAlgebra k M) (y : N) (m : M) :
    tensorCoeffEquiv (M := M) k N (x ⊗ₜ[k] y) m = x.coeff m • y := by
  classical
  simp [tensorCoeffEquiv, LinearEquiv.rTensor_tmul,
    TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  rfl

/-- A group-algebra tensor vanishes exactly when every group-weight coefficient vanishes. -/
theorem eq_zero_iff_tensorCoeffEquiv_apply (z : AddMonoidAlgebra k M ⊗[k] N) :
    z = 0 ↔ ∀ m, tensorCoeffEquiv (M := M) k N z m = 0 := by
  classical
  constructor
  · rintro rfl m
    simp
  · intro h
    apply (tensorCoeffEquiv (M := M) k N).injective
    apply Finsupp.ext
    intro m
    simpa using h m

end
end AddMonoidAlgebraTensorCoefficients
end GaloisForLFunctions.HTGeometry
