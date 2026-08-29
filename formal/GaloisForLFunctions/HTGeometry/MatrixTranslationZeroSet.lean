import GaloisForLFunctions.HTGeometry.MatrixTranslationPolynomial

/-!
# The zero set of the vanishing ideal of a matrix monoid is a monoid

The classical two-step argument, with no topology: right translation by a point of the set carries
the vanishing ideal into itself, so every point of the zero set kills it there; the resulting left
translate again lies in the vanishing ideal, and the second point of the zero set finishes.

* `matrixVanishingIdeal`, `subset_matrixZeroSet_vanishingIdeal`;
* `leftTranslate_mem_matrixVanishingIdeal`;
* `mul_mem_matrixZeroSet_vanishingIdeal`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

attribute [local instance] differentialPolynomialOverDifferential

variable {C : Type*} [Field C] [Differential C]

/-- The vanishing ideal of a set of matrices. -/
def matrixVanishingIdeal (H : Set (Matrix (Fin 2) (Fin 2) C)) :
    Set (DifferentialPolynomial (Fin 2 × Fin 2) C) :=
  {P | ∀ h ∈ H, differentialPolynomialEvalOver (K := C)
    (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0}

theorem subset_matrixZeroSet_vanishingIdeal (H : Set (Matrix (Fin 2) (Fin 2) C)) :
    H ⊆ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) :=
  fun h hh _P hP => hP h hh

/-- **Left translation by a point of the zero set preserves the vanishing ideal of a monoid.**
Right translation by a point of the monoid preserves the ideal, so a point of the zero set kills the
translate; that is exactly the statement that the left translate vanishes on the monoid. -/
theorem leftTranslate_mem_matrixVanishingIdeal {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    {a : Matrix (Fin 2) (Fin 2) C}
    (ha : a ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H))
    {P : DifferentialPolynomial (Fin 2 × Fin 2) C} (hP : P ∈ matrixVanishingIdeal H) :
    matrixLeftTranslate a P ∈ matrixVanishingIdeal H := by
  intro h hh
  rw [evalOver_matrixLeftTranslate_self, ← evalOver_matrixRightTranslate_self]
  refine ha _ ?_
  intro k hk
  rw [evalOver_matrixRightTranslate_self]
  exact hP _ (hH k hk h hh)

/-- **The zero set of the vanishing ideal of a multiplicative set is multiplicative.** -/
theorem mul_mem_matrixZeroSet_vanishingIdeal {H : Set (Matrix (Fin 2) (Fin 2) C)}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    {a b : Matrix (Fin 2) (Fin 2) C}
    (ha : a ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H))
    (hb : b ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H)) :
    a * b ∈ matrixZeroSet (C := C) (A := C) (matrixVanishingIdeal H) := by
  intro P hP
  have hstep := hb _ (leftTranslate_mem_matrixVanishingIdeal hH ha hP)
  rw [evalOver_matrixLeftTranslate_self] at hstep
  exact hstep

end

end GaloisForLFunctions.HTGeometry
