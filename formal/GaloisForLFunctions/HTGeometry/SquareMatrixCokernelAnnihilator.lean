import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The determinant annihilates the cokernel of a square matrix

`adjugate M * M = det M • 1`, so `det M • v = M *ᵥ (adjugate M *ᵥ v)` lies in the range of `M` for
every `v`.  Hence the determinant kills the quotient by that range:

```text
det_smul_mem_range_mulVecLin      det M • v ∈ range (M.mulVecLin)
det_smul_eq_zero_of_mem_range_quotient
det_mem_annihilator_quotient      ** det M ∈ Ann (coker M) **
```

This is the inequality half of "the different of a complete intersection is the Jacobian ideal":
the cotangent module of a presentation with `N` generators and `N` relations is the cokernel of the
Jacobian, so the Jacobian determinant lies in its annihilator — and for a monogenic localisation
that annihilator is the different.  Read at a place, it gives `v(𝔇) ≤ v(Jac)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {B : Type*} [CommRing B] {k : ℕ}

/-- **Cramer's rule as a membership.**  The determinant of a square matrix carries every vector
into the range of that matrix. -/
theorem det_smul_mem_range_mulVecLin (M : Matrix (Fin k) (Fin k) B) (v : Fin k → B) :
    M.det • v ∈ LinearMap.range M.mulVecLin := by
  refine ⟨M.adjugate.mulVec v, ?_⟩
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- **The determinant annihilates the cokernel.**  Every element of the quotient by the range of a
square matrix is killed by its determinant. -/
theorem det_smul_eq_zero_of_mem_range_quotient (M : Matrix (Fin k) (Fin k) B)
    (x : (Fin k → B) ⧸ LinearMap.range M.mulVecLin) : M.det • x = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (det_smul_mem_range_mulVecLin M v)

/-- The determinant lies in the annihilator of the cokernel. -/
theorem det_mem_annihilator_quotient (M : Matrix (Fin k) (Fin k) B) :
    M.det ∈ Module.annihilator B ((Fin k → B) ⧸ LinearMap.range M.mulVecLin) :=
  Module.mem_annihilator.mpr fun x => det_smul_eq_zero_of_mem_range_quotient M x

end GaloisForLFunctions.HTGeometry
