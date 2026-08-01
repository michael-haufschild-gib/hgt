import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Scaling and permuting the variables

Sending each variable to a nonzero scalar multiple of another variable, the assignment of targets
being a permutation, is an automorphism of the polynomial ring: undoing it means dividing by the
scalar and applying the inverse permutation.

In particular such a substitution is injective, which is what transports algebraic independence.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- Scaling and permuting the variables. -/
noncomputable def monomialSub (c : σ → K) (e : Equiv.Perm σ) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun j => MvPolynomial.C (c j) * MvPolynomial.X (e j))

theorem monomialSub_X (c : σ → K) (e : Equiv.Perm σ) (j : σ) :
    monomialSub c e (MvPolynomial.X j) =
      MvPolynomial.C (c j) * MvPolynomial.X (e j) := by
  rw [monomialSub, MvPolynomial.aeval_X]

theorem monomialSub_C (c : σ → K) (e : Equiv.Perm σ) (a : K) :
    monomialSub c e (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [monomialSub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

/-- **Scaling and permuting the variables is an automorphism.** -/
noncomputable def monomialSubEquiv {c : σ → K} (hc : ∀ j, c j ≠ 0) (e : Equiv.Perm σ) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (monomialSub c e)
    (monomialSub (fun i => (c (e.symm i))⁻¹) e.symm)
    (by
      refine MvPolynomial.algHom_ext fun j => ?_
      rw [AlgHom.comp_apply, monomialSub_X, map_mul, monomialSub_C, monomialSub_X,
        Equiv.apply_symm_apply, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (hc _), map_one, one_mul]
      rfl)
    (by
      refine MvPolynomial.algHom_ext fun j => ?_
      rw [AlgHom.comp_apply, monomialSub_X, map_mul, monomialSub_C, monomialSub_X,
        Equiv.symm_apply_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (hc _), map_one, one_mul]
      rfl)

theorem monomialSub_injective {c : σ → K} (hc : ∀ j, c j ≠ 0) (e : Equiv.Perm σ) :
    Function.Injective (monomialSub c e) :=
  (monomialSubEquiv hc e).injective

end GaloisForLFunctions.HTGeometry
