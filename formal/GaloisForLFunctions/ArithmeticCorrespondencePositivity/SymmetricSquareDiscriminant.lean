import GaloisForLFunctions.HTGeometry.SymmetricSquareMatrix

/-!
# The quadratic form of a symmetric-square transfer

The rank-three period representation used in §3.3 of arXiv:2611.13126
preserves a conic. In the corpus's integral symmetric-product coordinates,
its discriminant scales by the square of the rank-two determinant. This
also gives the precise quadratic-form scaling of every Hecke companion.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open HTGeometry

variable {R : Type*} [CommRing R]

/-- Discriminant in symmetric-product coordinates. -/
def symmetricDiscriminant (v : Fin 3 → R) : R := v 1 ^ 2 - 4 * v 0 * v 2

/-- The symmetric square carries the determinant-squared similitude character. -/
theorem symmetricSquare_discriminant (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 3 → R) :
    symmetricDiscriminant ((symmetricSquareMatrix M).mulVec v) =
      M.det ^ 2 * symmetricDiscriminant v := by
  simp [symmetricDiscriminant, symmetricSquareMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.det_fin_two]
  ring

/-- A symmetric product has discriminant equal to the square of the original exterior product. -/
theorem symmetricPair_discriminant (x y : Fin 2 → R) :
    symmetricDiscriminant (symmetricPair x y) = (x 0 * y 1 - x 1 * y 0) ^ 2 := by
  simp [symmetricDiscriminant, symmetricPair]
  ring

/-- Every square vector lies on the invariant period conic. -/
theorem symmetricPair_self_discriminant (x : Fin 2 → R) :
    symmetricDiscriminant (symmetricPair x x) = 0 := by
  rw [symmetricPair_discriminant]
  ring

/-- A Hecke transfer with determinant `p` scales the conic form by `p²`. -/
theorem heckeCompanion_symmetricSquare_discriminant (a p : R) (v : Fin 3 → R) :
    symmetricDiscriminant
      ((symmetricSquareMatrix (!![a, -p; 1, 0] : Matrix (Fin 2) (Fin 2) R)).mulVec v) =
      p ^ 2 * symmetricDiscriminant v := by
  rw [symmetricSquare_discriminant]
  simp [Matrix.det_fin_two]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity

#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.symmetricSquare_discriminant
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.symmetricPair_discriminant
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.symmetricPair_self_discriminant
#print axioms GaloisForLFunctions.ArithmeticCorrespondencePositivity.heckeCompanion_symmetricSquare_discriminant
