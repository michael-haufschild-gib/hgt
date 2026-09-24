import GaloisForLFunctions.HTGeometry.PositiveConeDeterminantMonotone

/-!
# Real determinant monotonicity on the positive cone

A real positive semidefinite matrix is a sum of real rank-one Gram matrices.  Casting each
rank-one factor to the complex numbers preserves this decomposition, so the complex determinant
monotonicity theorem applies to real matrices as well.
-/

open Matrix Finset
open scoped MatrixOrder ComplexOrder

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Complexification preserves positive semidefiniteness of a real matrix. -/
theorem realPosSemidef_complex {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Complex.ofRealHom).PosSemidef := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hA
  let w : Fin m → n → ℂ := fun i j => (v i j : ℂ)
  have heq : A.map Complex.ofRealHom = ∑ i : Fin m, vecMulVec (w i) (star (w i)) := by
    rw [hv]
    ext i j
    simp [Matrix.map_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, w]
  rw [heq]
  exact Matrix.posSemidef_sum Finset.univ (by
    intro i hi
    exact Matrix.posSemidef_vecMulVec_self_star (w i))

/-- If `0 ⪯ A ⪯ C` for real symmetric matrices, then `det A ≤ det C`. -/
theorem real_det_le_det_of_loewner {A C : Matrix n n ℝ}
    (hA : A.PosSemidef) (hC : C.PosSemidef)
    (hAC : (C - A).PosSemidef) : A.det ≤ C.det := by
  have hA' := realPosSemidef_complex hA
  have hC' := realPosSemidef_complex hC
  have hAC' : (C.map Complex.ofRealHom - A.map Complex.ofRealHom).PosSemidef := by
    convert realPosSemidef_complex hAC using 1
    ext i j
    simp
  have h := det_le_det_of_loewner hA' hC' hAC'
  have hdetA : (A.map Complex.ofRealHom).det = (A.det : ℂ) :=
    (Complex.ofRealHom.map_det A).symm
  have hdetC : (C.map Complex.ofRealHom).det = (C.det : ℂ) :=
    (Complex.ofRealHom.map_det C).symm
  rw [hdetA, hdetC] at h
  exact Complex.real_le_real.mp h

end GaloisForLFunctions.HTGeometry
