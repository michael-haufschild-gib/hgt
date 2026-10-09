import GaloisForLFunctions.HTGeometry.PaperRectangularRankNormalLine
import GaloisForLFunctions.HTGeometry.GenericDeterminantalSmooth

/-!
# Source Rees normal lines in the native square determinantal interface

Identify the two existing native definitions of the generic minor ideal,
then transport the fully proved rectangular application to `detIdeal` and
`genericVarMatrix`, the corpus's matrix-rank geometry interface.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable (K : Type*) [Field K]

/-- The square determinantal interface agrees with the native rectangular minor ideal. -/
theorem paperSquareRankIdeal_eq (r extra : ℕ) :
    detIdeal (genericVarMatrix K (r + 1 + extra)) (r + 1) =
      paperRectangularRankIdeal K r extra extra := by
  apply le_antisymm
  · apply detIdeal_le
    intro rows cols
    exact RHTower.deningerMatrixMinorDet_mem _ _ rows cols
  · rw [paperRectangularRankIdeal, RHTower.deningerMatrixMinorIdeal, Ideal.span_le]
    rintro p ⟨rows, cols, rfl⟩
    exact minor_mem_detIdeal (genericVarMatrix K _) rows cols

/-- Actual normal-line data in the existing square rank-geometry interface. -/
def paperSquareRankNormalData (r extra : ℕ) :
    PaperHomogeneousNormalData K (Fin (r + 1 + extra) × Fin (r + 1 + extra))
      (detIdeal (genericVarMatrix K (r + 1 + extra)) (r + 1)) := by
  rw [paperSquareRankIdeal_eq]
  exact paperRectangularRankNormalData K r extra extra

/-- Exact ideal order of the leading determinant in the square determinantal ideal. -/
theorem paperSquarePrincipalMinor_pow_exact (r extra n : ℕ) :
    paperRectangularPrincipalMinor K r extra extra ^ n ∈
        detIdeal (genericVarMatrix K (r + 1 + extra)) (r + 1) ^ n ∧
    paperRectangularPrincipalMinor K r extra extra ^ n ∉
        detIdeal (genericVarMatrix K (r + 1 + extra)) (r + 1) ^ (n + 1) := by
  rw [paperSquareRankIdeal_eq]
  exact paperRectangularPrincipalMinor_pow_exact K r extra extra n

/-- Polynomial normal-direction substitution in the native square associated graded ring. -/
def paperSquareRankNormalPolynomialMap (r extra : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded
      (detIdeal (genericVarMatrix K (r + 1 + extra)) (r + 1)) :=
  (paperSquareRankNormalData K r extra).polynomialMap

/-- The native square rank normal direction has no scalar polynomial relation. -/
theorem paperSquareRankNormalPolynomialMap_injective (r extra : ℕ) :
    Function.Injective (paperSquareRankNormalPolynomialMap K r extra) :=
  (paperSquareRankNormalData K r extra).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
