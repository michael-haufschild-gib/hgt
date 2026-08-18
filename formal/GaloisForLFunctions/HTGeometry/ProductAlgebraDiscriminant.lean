import Mathlib.RingTheory.Discriminant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Change of basis, and the discriminant of a product algebra

Two bookkeeping facts about `Algebra.discr` needed by the induction on the rank of an étale algebra.

* `isUnit_discr_of_isUnit_discr` — the discriminants of two bases differ by the square of the
  determinant of the change-of-basis matrix, which is a unit, so "the discriminant is a unit" is a
  property of the algebra and not of the chosen basis.
* `trace_prod_apply`, `discr_prod_singleton` — the trace form of `A × B` is the orthogonal direct
  sum of those of the factors, so the Gram matrix of a product basis is block diagonal and
  `discr (A × B') = discr A * discr B' = discr B'`.

Together they turn "`B` has unit discriminant and splits off a copy of the base" into "the
complement has unit discriminant", which is the inductive step.
-/


namespace GaloisForLFunctions.HTGeometry

open Matrix

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section BasisChange

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coe_basis_eq_mulVec (b b' : Module.Basis ι A B) :
    ⇑b' = (((b.toMatrix b')ᵀ).map (algebraMap A B)) *ᵥ ⇑b := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  conv_lhs => rw [← b.sum_repr (b' i)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Algebra.smul_def, Matrix.map_apply, Matrix.transpose_apply, Module.Basis.toMatrix_apply]

theorem discr_eq_det_sq_mul (b b' : Module.Basis ι A B) :
    Algebra.discr A b' = ((b.toMatrix b').det) ^ 2 * Algebra.discr A b := by
  conv_lhs => rw [coe_basis_eq_mulVec b b']
  rw [Algebra.discr_of_matrix_mulVec, Matrix.det_transpose]

theorem isUnit_discr_of_isUnit_discr (b b' : Module.Basis ι A B)
    (h : IsUnit (Algebra.discr A b)) : IsUnit (Algebra.discr A b') := by
  rw [discr_eq_det_sq_mul b b']
  exact IsUnit.mul (by
    have hinv : (b.toMatrix b') * (b'.toMatrix b) = 1 :=
      Module.Basis.toMatrix_mul_toMatrix_flip b b'
    have hdet : (b.toMatrix b').det * (b'.toMatrix b).det = 1 := by
      rw [← Matrix.det_mul, hinv, Matrix.det_one]
    exact (isUnit_iff_exists_inv.mpr ⟨_, hdet⟩).pow 2) h

end BasisChange

section Prod

variable {A B' : Type*} [CommRing A] [CommRing B'] [Algebra A B']
  [Module.Free A B'] [Module.Finite A B']

theorem lmul_prod (x : A × B') :
    Algebra.lmul A (A × B') x
      = ((Algebra.lmul A A x.1).prodMap (Algebra.lmul A B' x.2)) := by
  ext y <;> simp [Algebra.lmul]

theorem trace_prod_apply (x : A × B') :
    Algebra.trace A (A × B') x = x.1 + Algebra.trace A B' x.2 := by
  rw [Algebra.trace_apply, lmul_prod, LinearMap.trace_prodMap', ← Algebra.trace_apply,
    ← Algebra.trace_apply, Algebra.trace_self_apply]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem discr_prod_singleton (b' : Module.Basis ι A B') :
    Algebra.discr A ((Module.Basis.singleton Unit A).prod b') = Algebra.discr A b' := by
  classical
  have hblocks : Algebra.traceMatrix A ((Module.Basis.singleton Unit A).prod b')
      = Matrix.fromBlocks (1 : Matrix Unit Unit A) 0 0 (Algebra.traceMatrix A b') := by
    ext i j
    rcases i with u | i <;> rcases j with v | j
    · simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_prod_apply,
        Matrix.one_apply, Prod.ext_iff]
    · simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    · simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    · simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_prod_apply]
  rw [Algebra.discr_def, hblocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul,
    ← Algebra.discr_def]

end Prod

end GaloisForLFunctions.HTGeometry
