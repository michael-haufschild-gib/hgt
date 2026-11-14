import GaloisForLFunctions.RepresentationLifting.QuadraticSequence
import Mathlib.Data.Matrix.Basis

/-!
# Equivariance of the characteristic-two quadratic sequence

The tensor projection, polarization norm, and pure-square inclusion intertwine the
existing symmetric-square matrices with tensor-square and Frobenius-twisted actions.
Thus the coordinate exact sequence is compatible with every matrix action.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open HTGeometry

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The tensor-square action, expressed as congruence of coefficient matrices. -/
def tensorSquareAction (A : Matrix ι ι R) : Module.End R (Matrix ι ι R) where
  toFun T := A * T * A.transpose
  map_add' T U := by simp only [mul_add, add_mul]
  map_smul' c T := by simp

omit [Fintype ι] in
theorem tensorProjection_vecMulVec (x y : ι → R) :
    tensorProjection (Matrix.vecMulVec x y) = symmetricPairCoordinates x y := by
  ext p
  induction p with
  | _ i j => rfl

theorem tensorSquareAction_vecMulVec (A : Matrix ι ι R) (x y : ι → R) :
    tensorSquareAction A (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (A.mulVec x) (A.mulVec y) := by
  simp [tensorSquareAction, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_transpose]

/-- Tensor multiplication is natural for the existing symmetric-square representation. -/
theorem tensorProjection_intertwines (A T : Matrix ι ι R) :
    tensorProjection (tensorSquareAction A T) =
      (symmetricSquareMatrixGeneral A).mulVec (tensorProjection T) := by
  induction T using Matrix.induction_on' with
  | h_zero => simp
  | h_add T U hT hU => simp only [map_add, Matrix.mulVec_add, hT, hU]
  | h_std_basis i j a =>
      have hs : Matrix.single i j a =
          Matrix.vecMulVec (Pi.single i a) (Pi.single j 1) := by
        ext k l
        by_cases hik : i = k <;> by_cases hjl : j = l <;>
          simp [Matrix.vecMulVec, Pi.single_apply, hik, hjl, eq_comm]
      rw [hs, tensorSquareAction_vecMulVec, tensorProjection_vecMulVec,
        tensorProjection_vecMulVec, symmetricPairCoordinates_mulVec]

variable [CharP R 2]

omit [Fintype ι] in
theorem tensorNorm_projection (T : Matrix ι ι R) :
    tensorNorm (tensorProjection T) = T + T.transpose := by
  ext i j
  by_cases hij : i = j
  · subst j; simp [CharTwo.add_self_eq_zero]
  · simp [hij]

/-- Polarization intertwines symmetric-square and tensor-square actions. -/
theorem tensorNorm_intertwines [LinearOrder ι] (A : Matrix ι ι R) (q : Sym2 ι → R) :
    tensorNorm ((symmetricSquareMatrixGeneral A).mulVec q) =
      tensorSquareAction A (tensorNorm q) := by
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [← tensorProjection_intertwines, tensorNorm_projection, tensorNorm_projection, map_add]
  change A * T * A.transpose + (A * T * A.transpose).transpose =
    A * T * A.transpose + A * T.transpose * A.transpose
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, mul_assoc]

omit [Fintype ι] [CharP R 2] in
theorem tensorProjection_diagonal (x : ι → R) :
    tensorProjection (Matrix.diagonal x) = squareDiagonal x := by
  ext p
  induction p with
  | _ i j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [hij, Ne.symm hij]

theorem tensorProjection_transformed_diagonal (A : Matrix ι ι R) (x : ι → R) :
    tensorProjection (tensorSquareAction A (Matrix.diagonal x)) =
      squareDiagonal ((A.map (fun a => a ^ 2)).mulVec x) := by
  have he (i j : ι) : tensorSquareAction A (Matrix.diagonal x) i j =
      ∑ k, A i k * x k * A j k := by
    change (A * Matrix.diagonal x * A.transpose) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  ext p
  induction p with
  | _ i j =>
      by_cases hij : i = j
      · subst j
        simp only [tensorProjection_mk, squareDiagonal_mk, ↓reduceIte, he,
          Matrix.mulVec, dotProduct, Matrix.map_apply]
        apply Finset.sum_congr rfl
        intro k _
        ring
      · have hs : tensorSquareAction A (Matrix.diagonal x) j i =
            tensorSquareAction A (Matrix.diagonal x) i j := by
          rw [he, he]
          apply Finset.sum_congr rfl
          intro k _
          ring
        simp only [tensorProjection_mk, squareDiagonal_mk, hij, ↓reduceIte]
        rw [hs, CharTwo.add_self_eq_zero]

/-- The pure-square subspace carries the action obtained by squaring every matrix entry. -/
theorem squareDiagonal_intertwines (A : Matrix ι ι R) (x : ι → R) :
    (symmetricSquareMatrixGeneral A).mulVec (squareDiagonal x) =
      squareDiagonal ((A.map (fun a => a ^ 2)).mulVec x) := by
  rw [← tensorProjection_diagonal, ← tensorProjection_intertwines,
    tensorProjection_transformed_diagonal]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.tensorProjection_intertwines
#print axioms GaloisForLFunctions.RepresentationLifting.tensorNorm_intertwines
#print axioms GaloisForLFunctions.RepresentationLifting.squareDiagonal_intertwines
