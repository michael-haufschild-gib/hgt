import GaloisForLFunctions.HTGeometry.PaperGenericMinorWeights
import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalLine

/-!
# Polynomial normal lines for rectangular generic rank conditions

The native ideal of all `(r+1)`-minors of a generic
`(r+1+rowExtra) × (r+1+colExtra)` matrix receives the paper's exact Rees
kernel and nonnegative-weight mechanism. Every field, rank and rectangular
window is covered by explicit native determinant data.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

noncomputable section

abbrev PaperRectangularRankRing (K : Type*) [CommSemiring K] (r rowExtra colExtra : ℕ) :=
  MvPolynomial (Fin (r + 1 + rowExtra) × Fin (r + 1 + colExtra)) K

variable (K : Type*) [Field K]

/-- The existing native determinantal ideal in generic rectangular matrix coordinates. -/
def paperRectangularRankIdeal (r rowExtra colExtra : ℕ) :
    Ideal (PaperRectangularRankRing K r rowExtra colExtra) :=
  deningerMatrixMinorIdeal (r + 1)
    (Matrix.mvPolynomialX (Fin (r + 1 + rowExtra)) (Fin (r + 1 + colExtra)) K)

/-- The leading square minor inside the rectangular generic matrix. -/
def paperRectangularPrincipalMinor (r rowExtra colExtra : ℕ) :
    PaperRectangularRankRing K r rowExtra colExtra :=
  ((Matrix.mvPolynomialX (Fin (r + 1 + rowExtra)) (Fin (r + 1 + colExtra)) K).submatrix
    (Fin.castAdd rowExtra) (Fin.castAdd colExtra)).det

/-- Every normal-line obligation is discharged by generic minor proofs. -/
def paperRectangularRankNormalData (r rowExtra colExtra : ℕ) :
    PaperHomogeneousNormalData K (Fin (r + 1 + rowExtra) × Fin (r + 1 + colExtra))
      (paperRectangularRankIdeal K r rowExtra colExtra) where
  generator := paperRectangularPrincipalMinor K r rowExtra colExtra
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := deningerMatrixMinorDet_mem _ _ _ _
  generator_ne_zero := paperVariableMinor_ne_zero K _ _ _
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
  homogeneous := paperIsWeightedHomogeneous_int (paperVariableMinor_homogeneous K _ _ _)
  order_bound := paperVariableMinorIdeal_weightOrder K _ _ _

/-- Powers of the leading minor have exact order in the full rectangular rank ideal. -/
theorem paperRectangularPrincipalMinor_pow_exact (r rowExtra colExtra n : ℕ) :
    paperRectangularPrincipalMinor K r rowExtra colExtra ^ n ∈
        paperRectangularRankIdeal K r rowExtra colExtra ^ n ∧
    paperRectangularPrincipalMinor K r rowExtra colExtra ^ n ∉
        paperRectangularRankIdeal K r rowExtra colExtra ^ (n + 1) :=
  ⟨(paperRectangularRankNormalData K r rowExtra colExtra).pow_mem n,
    (paperRectangularRankNormalData K r rowExtra colExtra).pow_not_mem_succ n⟩

/-- No two successive ideal powers stabilize. -/
theorem paperRectangularRankIdeal_powers_ne (r rowExtra colExtra n : ℕ) :
    paperRectangularRankIdeal K r rowExtra colExtra ^ n ≠
      paperRectangularRankIdeal K r rowExtra colExtra ^ (n + 1) := by
  intro h
  exact (paperRectangularPrincipalMinor_pow_exact K r rowExtra colExtra n).2
    (h ▸ (paperRectangularPrincipalMinor_pow_exact K r rowExtra colExtra n).1)

/-- The leading determinant's class in the actual rectangular associated graded ring. -/
def paperRectangularRankNormalDirection (r rowExtra colExtra : ℕ) :
    PaperIdealAssociatedGraded (paperRectangularRankIdeal K r rowExtra colExtra) :=
  (paperRectangularRankNormalData K r rowExtra colExtra).direction

/-- The rectangular rank normal direction is never nilpotent. -/
theorem paperRectangularRankNormalDirection_not_isNilpotent (r rowExtra colExtra : ℕ) :
    ¬ IsNilpotent (paperRectangularRankNormalDirection K r rowExtra colExtra) :=
  (paperRectangularRankNormalData K r rowExtra colExtra).direction_not_isNilpotent

/-- Polynomial substitution into the native rectangular rank associated graded ring. -/
def paperRectangularRankNormalPolynomialMap (r rowExtra colExtra : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (paperRectangularRankIdeal K r rowExtra colExtra) :=
  (paperRectangularRankNormalData K r rowExtra colExtra).polynomialMap

/-- No polynomial relation in the chosen normal direction can vanish. -/
theorem paperRectangularRankNormalPolynomialMap_eq_zero_iff
    (r rowExtra colExtra : ℕ) (p : Polynomial K) :
    paperRectangularRankNormalPolynomialMap K r rowExtra colExtra p = 0 ↔ p = 0 :=
  (paperRectangularRankNormalData K r rowExtra colExtra).polynomialMap_eq_zero_iff p

/-- An actual polynomial ring embeds into every generic rectangular rank associated graded ring. -/
theorem paperRectangularRankNormalPolynomialMap_injective (r rowExtra colExtra : ℕ) :
    Function.Injective (paperRectangularRankNormalPolynomialMap K r rowExtra colExtra) :=
  (paperRectangularRankNormalData K r rowExtra colExtra).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
