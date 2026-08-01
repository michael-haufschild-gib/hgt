import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# A nonsingular linear system solves inside any intermediate field carrying its data

If a square system has all its coefficients and all its constants inside an intermediate field and
its determinant does not vanish, then its solution lies in that intermediate field.  The system has
a solution there because the matrix is invertible over it, and that solution agrees with the given
one because a nonsingular matrix annihilates only zero.
-/

namespace GaloisForLFunctions.HTGeometry

variable {ι K E : Type*} [Fintype ι] [DecidableEq ι] [Field K] [Field E] [Algebra K E]

/-- **Cramer's rule relative to an intermediate field.** -/
theorem mulVec_solution_mem (L : IntermediateField K E) {M : Matrix ι ι E} {u c : ι → E}
    (hM : ∀ r s, M r s ∈ L) (hc : ∀ r, c r ∈ L) (hdet : M.det ≠ 0)
    (hsys : M.mulVec u = c) (r : ι) : u r ∈ L := by
  classical
  set f : L →+* E := (L.val : L →ₐ[K] E).toRingHom with hf
  set M' : Matrix ι ι L := Matrix.of fun a b => ⟨M a b, hM a b⟩ with hM'
  set c' : ι → L := fun a => ⟨c a, hc a⟩ with hc'
  have hmapM : M'.map f = M := by
    ext a b
    rfl
  have hdet' : M'.det ≠ 0 := by
    intro h
    refine hdet ?_
    have hfd : f M'.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hmapM]
    rw [← hfd, h, map_zero]
  have hunit : IsUnit M'.det := hdet'.isUnit
  set v' : ι → L := M'⁻¹.mulVec c' with hv'
  have hsol : M'.mulVec v' = c' := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hpush : M.mulVec (fun a => f (v' a)) = c := by
    funext a
    have h := congrFun hsol a
    have hL : M.mulVec (fun b => f (v' b)) a = f (M'.mulVec v' a) := by
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, ← hmapM, Matrix.map_apply]
    rw [hL, h]
    rfl
  have hzero : M.mulVec (u - fun a => f (v' a)) = 0 := by
    rw [Matrix.mulVec_sub, hsys, hpush, sub_self]
  have heq : u = fun a => f (v' a) := by
    have h := Matrix.eq_zero_of_mulVec_eq_zero hdet hzero
    funext a
    have := congrFun h a
    simpa [sub_eq_zero] using this
  rw [heq]
  exact (v' r).2

end GaloisForLFunctions.HTGeometry
