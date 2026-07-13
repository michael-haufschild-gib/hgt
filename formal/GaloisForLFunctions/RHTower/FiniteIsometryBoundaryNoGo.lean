import GaloisForLFunctions.RHTower.WeldWeylMultiplicity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A finite isometry has no unilateral boundary defect

The Bost--Connes and archimedean Toeplitz detours naturally produce proper isometries: `SᴴS=1`
but `SSᴴ≠1`.  Such a one-sided shift is intrinsically infinite-dimensional.  On a finite SEM hole
space, a left-unitary square matrix is automatically unitary and invertible.

Therefore the proper-isometry boundary projection cannot descend unchanged to the actual finite
hole space.  A finite source model must replace it by a cyclic closure, whose holonomy is exactly
the already isolated dyadic top-jet anomaly.

This is standard finite linear algebra, recorded as a bridge/no-go rather than new scientific
knowledge.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- Every finite complex matrix satisfying the isometry equation is unitary. -/
theorem finiteMatrix_isometry_is_unitary {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hiso : Uᴴ * U = 1) :
    U * Uᴴ = 1 := by
  exact mul_eq_one_comm.mp hiso

/-- In particular a finite matrix isometry is invertible. -/
theorem finiteMatrix_isometry_det_ne_zero {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) (hiso : Uᴴ * U = 1) :
    U.det ≠ 0 := by
  have hdet := congrArg Matrix.det hiso
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at hdet
  intro hzero
  rw [hzero, star_zero, zero_mul] at hdet
  exact zero_ne_one hdet

/-- **Finite proper-isometry no-go.** No finite square complex matrix has a unilateral isometry
defect. -/
theorem no_finiteMatrix_proper_isometry {d : ℕ}
    (U : Matrix (Fin d) (Fin d) ℂ) :
    ¬ (Uᴴ * U = 1 ∧ U * Uᴴ ≠ 1) := by
  rintro ⟨hiso, hproper⟩
  exact hproper (finiteMatrix_isometry_is_unitary U hiso)

end RHTower
