import GaloisForLFunctions.HTGeometry.MatrixPrincipalSymbolCoefficientFlatness
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Abelian rigidity of a flat matrix principal-symbol tower

The determinant horizon hides a stronger constraint.  Fix a law direction whose symbols are
invertible.  In the coefficient convention forced by iterated derivations, flatness makes the
symbols at every layer commute after normalization by that direction.  Thus a flat finite-rank
principal tower carries only a commutative normalized observable algebra.  Noncommutativity is an
exact obstruction to flatness, hence forces nonzero principal curvature somewhere.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K g ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- The coefficient symbol at layer `n`, normalized on the left by a regular reference law. -/
def coefficientNormalizedMatrixPrincipalSymbol
    (symbol : ℕ → g → Matrix ι ι K) (e : g) (n : ℕ) (A : g) :
    Matrix ι ι K :=
  (symbol n e)⁻¹ * symbol n A

/-- One flat square with the reference law transports a symbol to the next layer. -/
theorem matrixCoefficientPrincipalSymbol_transport
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) :
    symbol (n + 1) A =
      coefficientNormalizedMatrixPrincipalSymbol symbol e n A * symbol (n + 1) e := by
  have hunit : IsUnit (symbol n e).det := isUnit_iff_ne_zero.mpr (he n)
  unfold coefficientNormalizedMatrixPrincipalSymbol
  calc
    symbol (n + 1) A =
        (symbol n e)⁻¹ * (symbol n e * symbol (n + 1) A) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
    _ = (symbol n e)⁻¹ * (symbol n A * symbol (n + 1) e) := by
      rw [hflat n A e]
    _ = ((symbol n e)⁻¹ * symbol n A) * symbol (n + 1) e := by
      rw [Matrix.mul_assoc]

/-- Normalized coefficient symbols are transported between layers by conjugation. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_succ_eq_conj
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A : g) :
    coefficientNormalizedMatrixPrincipalSymbol symbol e (n + 1) A =
      (symbol (n + 1) e)⁻¹ *
        coefficientNormalizedMatrixPrincipalSymbol symbol e n A *
          symbol (n + 1) e := by
  unfold coefficientNormalizedMatrixPrincipalSymbol
  rw [matrixCoefficientPrincipalSymbol_transport symbol hflat e he n A]
  simp only [Matrix.mul_assoc]

/-- **Abelian rigidity.**  At every layer, all normalized symbols of a flat coefficient tower
commute pairwise. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g) :
    Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B) := by
  have hnextUnit : IsUnit (symbol (n + 1) e) :=
    Matrix.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr (he (n + 1)))
  have hcross := hflat n A B
  rw [matrixCoefficientPrincipalSymbol_transport symbol hflat e he n A,
    matrixCoefficientPrincipalSymbol_transport symbol hflat e he n B] at hcross
  have hcancel :
      symbol n B * coefficientNormalizedMatrixPrincipalSymbol symbol e n A =
        symbol n A * coefficientNormalizedMatrixPrincipalSymbol symbol e n B := by
    apply hnextUnit.mul_right_cancel
    simpa only [Matrix.mul_assoc] using hcross
  have hleft := congrArg
    (fun M : Matrix ι ι K ↦ (symbol n e)⁻¹ * M) hcancel
  show coefficientNormalizedMatrixPrincipalSymbol symbol e n A *
      coefficientNormalizedMatrixPrincipalSymbol symbol e n B =
    coefficientNormalizedMatrixPrincipalSymbol symbol e n B *
      coefficientNormalizedMatrixPrincipalSymbol symbol e n A
  simpa only [coefficientNormalizedMatrixPrincipalSymbol, Matrix.mul_assoc] using hleft.symm

/-- The whole normalized law family is pairwise commuting at every layer. -/
theorem coefficientNormalizedMatrixPrincipalSymbol_pairwise_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (hflat : MatrixCoefficientPrincipalSymbolFlat symbol)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) :
    Pairwise (fun A B ↦ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) := by
  intro A B _
  exact coefficientNormalizedMatrixPrincipalSymbol_commute symbol hflat e he n A B

/-- **Noncommutativity forces curvature.**  A noncommuting pair of normalized observables rules
out flatness of the complete principal-symbol tower. -/
theorem not_matrixCoefficientPrincipalSymbolFlat_of_normalized_not_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g)
    (hnc : ¬ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) :
    ¬ MatrixCoefficientPrincipalSymbolFlat symbol := by
  intro hflat
  exact hnc <|
    coefficientNormalizedMatrixPrincipalSymbol_commute symbol hflat e he n A B

/-- In curvature language, a noncommuting normalized pair forces a nonzero coefficient curvature
at some layer and pair of law directions. -/
theorem exists_matrixCoefficientPrincipalCurvature_ne_zero_of_normalized_not_commute
    (symbol : ℕ → g → Matrix ι ι K)
    (e : g) (he : ∀ n, (symbol n e).det ≠ 0)
    (n : ℕ) (A B : g)
    (hnc : ¬ Commute
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n A)
      (coefficientNormalizedMatrixPrincipalSymbol symbol e n B)) :
    ∃ m C D, matrixCoefficientPrincipalCurvature symbol m C D ≠ 0 := by
  have hnflat := not_matrixCoefficientPrincipalSymbolFlat_of_normalized_not_commute
    symbol e he n A B hnc
  rw [matrixCoefficientPrincipalSymbolFlat_iff_curvature_zero] at hnflat
  push_neg at hnflat
  exact hnflat

end

end GaloisForLFunctions.HTGeometry
