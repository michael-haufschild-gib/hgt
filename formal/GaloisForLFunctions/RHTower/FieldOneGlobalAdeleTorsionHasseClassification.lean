import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.RHTower.FieldOneGlobalAdeleTorsionHasse

/-!
# Classification inside finite adelic torsion layers

The finite-layer adelic Hasse quotient is evaluated on representatives.  Equality of torsion
characters is congruence modulo character-neutral global classes, and every torsion character has a
representative unique modulo those classes.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The finite-layer adelic quotient equivalence is induced by the torsion character. -/
@[simp] theorem fieldOneGlobalAdeleClassNTorsionHasseQuotientEquiv_mk
    (n : ℕ) (x : fieldOneGlobalAdeleClassNTorsionPreimage n) :
    fieldOneGlobalAdeleClassNTorsionHasseQuotientEquiv n
        (QuotientAddGroup.mk x) =
      fieldOneGlobalAdeleClassNTorsionCharacter n x := by
  simp only [fieldOneGlobalAdeleClassNTorsionHasseQuotientEquiv,
    AddEquiv.trans_apply, QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

/-- Two finite-layer adelic classes have the same torsion character exactly when they differ by a
character-neutral global class. -/
theorem fieldOneGlobalAdeleClassNTorsion_congr_hasse_iff
    (n : ℕ) (x y : fieldOneGlobalAdeleClassNTorsionPreimage n) :
    x - y ∈ (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n).range ↔
      fieldOneGlobalAdeleClassNTorsionCharacter n x =
        fieldOneGlobalAdeleClassNTorsionCharacter n y :=
  addHasse_congr_iff
    (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n)
    (fieldOneGlobalAdeleClassNTorsionCharacter n)
    (fieldOneGlobalAdeleClassNTorsionHasse_exact n) x y

/-- Every circle torsion character has an adelic representative, unique modulo character-neutral
global classes. -/
theorem fieldOneGlobalAdeleClassNTorsion_exists_unique_mod_zeroSum
    (n : ℕ) (z : unitAddCircleNTorsion n) :
    ∃ x : fieldOneGlobalAdeleClassNTorsionPreimage n,
      fieldOneGlobalAdeleClassNTorsionCharacter n x = z ∧
      ∀ y : fieldOneGlobalAdeleClassNTorsionPreimage n,
        fieldOneGlobalAdeleClassNTorsionCharacter n y = z ↔
          y - x ∈ (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n).range :=
  addHasse_exists_unique_mod_global
    (fieldOneGlobalAdeleZeroSumToNTorsionPreimage n)
    (fieldOneGlobalAdeleClassNTorsionCharacter n)
    (fieldOneGlobalAdeleClassNTorsionHasse_exact n)
    (fieldOneGlobalAdeleClassNTorsionCharacter_surjective n) z

end
end GaloisForLFunctions.RHTower
