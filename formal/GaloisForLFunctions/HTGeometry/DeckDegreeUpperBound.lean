import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Fixed

/-!
# A deck degree count needs only its upper bound

A subfield contained in the fixed field of a finite group of automorphisms has degree at least the
order of that group: Artin's theorem computes the degree of the fixed field exactly, and enlarging
the base field can only lower the degree.  So the equality of extension degree and group order --
the geometric input of a Galois-descent argument -- follows from the inequality in the direction
that a degree estimate supplies.

For a radical or isogeny prefix that direction is a direct computation, so this halves the geometric
content of a deck-descent hypothesis.  Artin's theorem is used in the form that does not assume the
whole extension finite over the base, which is essential for differential fields.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **A subfield of a fixed field has degree at least the order of the group.** -/
theorem card_le_finrank_of_le_fixedField (Γ : Subgroup (F ≃ₐ[K] F)) [Fintype Γ]
    (E : IntermediateField K F) [FiniteDimensional E F]
    (hfix : E ≤ IntermediateField.fixedField Γ) :
    Nat.card Γ ≤ Module.finrank E F := by
  have hfix' : Module.finrank (IntermediateField.fixedField Γ) F = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card Γ F
  calc Nat.card Γ = Module.finrank (IntermediateField.fixedField Γ) F := hfix'.symm
    _ ≤ Module.finrank E F := IntermediateField.finrank_le_of_le_left hfix

/-- **The deck degree equality from its upper bound.**  A subfield inside the fixed field of a finite
automorphism group whose extension degree does not exceed the order of the group realizes that order
exactly. -/
theorem finrank_eq_card_of_le_fixedField_of_finrank_le (Γ : Subgroup (F ≃ₐ[K] F)) [Fintype Γ]
    (E : IntermediateField K F) [FiniteDimensional E F]
    (hfix : E ≤ IntermediateField.fixedField Γ)
    (hle : Module.finrank E F ≤ Nat.card Γ) :
    Module.finrank E F = Nat.card Γ :=
  le_antisymm hle (card_le_finrank_of_le_fixedField Γ E hfix)

/-- **A subfield inside a fixed field, of the group's degree, is the fixed field.** -/
theorem eq_fixedField_of_finrank_le (Γ : Subgroup (F ≃ₐ[K] F)) [Fintype Γ]
    (E : IntermediateField K F) [FiniteDimensional E F]
    (hfix : E ≤ IntermediateField.fixedField Γ)
    (hle : Module.finrank E F ≤ Nat.card Γ) :
    E = IntermediateField.fixedField Γ := by
  have hdeg : Module.finrank E F = Nat.card Γ :=
    finrank_eq_card_of_le_fixedField_of_finrank_le Γ E hfix hle
  have hfixdeg : Module.finrank (IntermediateField.fixedField Γ) F = Nat.card Γ := by
    rw [Nat.card_eq_fintype_card]
    exact FixedPoints.finrank_eq_card Γ F
  refine IntermediateField.eq_of_le_of_finrank_le' hfix ?_
  rw [hdeg, hfixdeg]

end GaloisForLFunctions.HTGeometry
