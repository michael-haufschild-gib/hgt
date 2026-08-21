import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixInvariants
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable

/-!
# Hasse detection for separable matrix characteristic polynomials

Characteristic polynomials commute with scalar extension, and separability is reflected by a
field extension.  Therefore a globally defined matrix has no repeated geometric eigenvalues
exactly when its completed matrices have no repeated geometric eigenvalues.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Separability of a matrix characteristic polynomial is reflected by coefficientwise field
scalar extension. -/
theorem matrix_charpoly_separable_iff_map {K : Type u} {L : Type v} {n : Type w}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.charpoly.Separable ↔ (M.map (algebraMap K L)).charpoly.Separable := by
  rw [Matrix.charpoly_map]
  exact polynomial_separable_iff_map (L := L) M.charpoly

/-- A number-field matrix has separable characteristic polynomial exactly when every completed
matrix does. -/
theorem numberFieldMatrix_charpoly_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n K) :
    M.charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      (M.map (algebraMap K (completion K p))).charpoly.Separable := by
  constructor
  · intro h p
    exact (matrix_charpoly_separable_iff_map (L := completion K p) M).mp h
  · intro h
    exact (matrix_charpoly_separable_iff_map (L := completion K (witnessPlace K)) M).mpr
      (h (witnessPlace K))

/-- An `F(t)`-matrix has separable characteristic polynomial exactly when every finite and
infinite completed matrix does. -/
theorem rationalFunctionMatrix_charpoly_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (n : Type w) [Fintype n] [DecidableEq n]
    (M : Matrix n n (RatFunc F)) :
    M.charpoly.Separable ↔ ∀ p : RationalFunctionPlace F,
      (M.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p))).charpoly.Separable := by
  constructor
  · intro h p
    exact (matrix_charpoly_separable_iff_map (L := rationalFunctionCompletion F p) M).mp h
  · intro h
    exact (matrix_charpoly_separable_iff_map
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) M).mpr
      (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
