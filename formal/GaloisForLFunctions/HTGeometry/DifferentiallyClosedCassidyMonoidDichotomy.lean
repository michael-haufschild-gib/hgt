import GaloisForLFunctions.HTGeometry.CassidyMonoidDichotomy
import GaloisForLFunctions.HTGeometry.DifferentiallyClosedAlgClosed
import GaloisForLFunctions.HTGeometry.DifferentiallyClosedNoUniversalJetRelation

/-!
# Cassidy's monoid dichotomy over a differentially closed field

Differential closedness supplies every ambient field condition required by the determinant-one
Cassidy endgame: characteristic zero, algebraic closedness of the field and its differential
constants, and absence of a universal linear jet relation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

universe u

variable {C : Type u} [Field C] [Algebra ℚ C] [Differential C]

/-- **Cassidy's determinant-one monoid dichotomy with all ambient differential-field premises
discharged by differential closedness.** -/
theorem cassidy_monoid_dichotomy_of_isDifferentiallyClosed [IsDifferentiallyClosed C]
    {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hHone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ H)
    (hHdet : ∀ h ∈ H, h.det = 1)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 →
      Z ∈ Submodule.span C
        ((matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone) : Submodule _ _) : Set _))
    (G : Set (Matrix (Fin 2) (Fin 2) C))
    (hGdetK : ∀ g ∈ G, g.det ∈ differentialConstants C)
    (hGdet0 : ∀ g ∈ G, g.det ≠ 0)
    (hGinv : ∀ g ∈ G, ∃ g' : Matrix (Fin 2) (Fin 2) C, g * g' = 1 ∧
      ∀ A ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone),
        g * A * g' ∈ matrixTangentM (matrixVanishingIdeal H)
          (subset_matrixZeroSet_vanishingIdeal H hHone)) :
    (∀ g : Matrix (Fin 2) (Fin 2) C, g.det = 1 →
        g ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H))
      ∨ ∃ (n : ℕ) (Lop : ℕ → C) (i₀ : ℕ), i₀ ∈ Finset.range (n + 1) ∧ Lop i₀ ≠ 0 ∧
          ∀ g ∈ G, ∀ i j, g i j ∈ linearJetSolutions n Lop := by
  letI : CharZero C := algebraRat.charZero C
  letI : IsAlgClosed C := isAlgClosed_of_isDifferentiallyClosed C
  letI : IsAlgClosed (differentialConstants C) := isAlgClosed_differentialConstants C
  exact cassidy_monoid_dichotomy noUniversalJetRelation_of_isDifferentiallyClosed
    hH hHone hHdet hdense G hGdetK hGdet0 hGinv

end

end GaloisForLFunctions.HTGeometry
