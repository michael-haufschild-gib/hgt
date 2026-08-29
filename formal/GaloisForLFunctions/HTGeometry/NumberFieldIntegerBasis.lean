import GaloisForLFunctions.HTGeometry.NumberFieldIntegerCoveringRadius

/-!
# Canonical finite indexing of a number field's ring of integers

This file removes an arbitrary-basis premise from later reduction arguments.  Mathlib supplies the
free `ℤ`-basis `RingOfIntegers.basis K`, indexed by a choice type.  Its cardinality is the field
degree, so reindexing gives a fixed basis indexed by `Fin (finrank ℚ K)`.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField Module.Free
open scoped Classical NumberField

noncomputable section

/-- The basis index of `𝓞 K` is equivalent to the finite field-degree index. -/
def numberFieldIntegerBasisIndexEquiv (K : Type*) [Field K] [NumberField K] :
    ChooseBasisIndex ℤ (𝓞 K) ≃ Fin (Module.finrank ℚ K) := by
  classical
  apply Fintype.equivOfCardEq
  rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, Fintype.card_fin]

/-- A fixed integral basis of `𝓞 K`, indexed by `Fin (finrank ℚ K)`. -/
def numberFieldIntegerBasis (K : Type*) [Field K] [NumberField K] :
    Module.Basis (Fin (Module.finrank ℚ K)) ℤ (𝓞 K) :=
  (RingOfIntegers.basis K).reindex (numberFieldIntegerBasisIndexEquiv K)

@[simp]
theorem numberFieldIntegerBasis_apply (K : Type*) [Field K] [NumberField K]
    (i : Fin (Module.finrank ℚ K)) :
    numberFieldIntegerBasis K i =
      RingOfIntegers.basis K ((numberFieldIntegerBasisIndexEquiv K).symm i) := by
  simp [numberFieldIntegerBasis]

end

end GaloisForLFunctions.HTGeometry
