import Mathlib

/-! # Exact rank-four Hankel determinant and its last-entry dependence -/
namespace GaloisForLFunctions.HTGeometry
set_option maxRecDepth 4096

/-- Four-by-four Hankel determinant in scalar cofactor form. -/
def hankelFourDet {K : Type*} [CommRing K] (a b c d e f g : K) : K :=
  (a*c*e-a*d^2-b^2*e+2*b*c*d-c^3)*g -
    ((c*e-d^2)*d^2 + 2*(c*d-b*e)*d*e + 2*(b*d-c^2)*d*f +
      (a*e-c^2)*e^2 + 2*(b*c-a*d)*e*f + (a*c-b^2)*f^2)

/-- Literal matrix determinant, with no nonzero or positivity premise. -/
theorem det_hankelFour {K : Type*} [CommRing K] (a b c d e f g : K) :
    Matrix.det !![a,b,c,d; b,c,d,e; c,d,e,f; d,e,f,g] = hankelFourDet a b c d e f g := by
  have hcast : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  rw [Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    hcast, Fin.lt_def, Fin.le_def, Fin.isValue, -Fin.val_fin_lt, -Fin.val_fin_le, -Fin.val_pos_iff]
  unfold hankelFourDet
  ring

/-- A correction to the last moment multiplies precisely the leading determinant. -/
theorem hankelFourDet_last_add {K : Type*} [CommRing K] (a b c d e f g u : K) :
    hankelFourDet a b c d e f (g+u) = hankelFourDet a b c d e f g +
      u*(a*c*e-a*d^2-b^2*e+2*b*c*d-c^3) := by
  unfold hankelFourDet
  ring

end GaloisForLFunctions.HTGeometry
