import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The determinant of the identity with one row replaced

Replacing one row of the identity matrix by a vector gives a matrix whose determinant is the entry
of that vector in the replaced position: all other rows are standard basis vectors, so only that
entry survives.

This is Cramer's rule for the identity, transposed.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **The identity with one row replaced has determinant that row's entry there.** -/
theorem det_updateRow_one (i : n) (v : n → R) :
    (Matrix.updateRow (1 : Matrix n n R) i v).det = v i := by
  have hT : Matrix.transpose (Matrix.updateRow (1 : Matrix n n R) i v) =
      Matrix.updateCol (1 : Matrix n n R) i v := by
    ext a b
    by_cases h : b = i
    · simp [Matrix.updateRow_apply, h, Matrix.transpose_apply]
    · simp only [Matrix.transpose_apply, Matrix.updateRow_apply, Matrix.updateCol_apply,
        if_neg h, Matrix.one_apply]
      exact if_congr eq_comm rfl rfl
  rw [← Matrix.det_transpose, hT, ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

end GaloisForLFunctions.HTGeometry
