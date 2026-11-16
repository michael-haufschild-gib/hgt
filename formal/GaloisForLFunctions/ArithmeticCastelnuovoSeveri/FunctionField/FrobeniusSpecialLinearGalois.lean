import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusSpecialLinearDegree
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusSpecialLinearAction
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.SpecialLinearTwoCardinality

/-!
# The determinant-one Galois group of the invariant extension

The faithful determinant-one substitutions supply `q(q²-1)` relative
automorphisms. This equals the exact invariant-field degree, so the
extension is Galois and these substitutions exhaust its automorphisms.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Matrix ArithmeticHarmonicAnalysis
variable (K E : Type*) [Field K] [Fintype K] [Field E] [Algebra K E]
    (γ : Eˣ) (R : ℕ)
local notation "q" => Fintype.card K
local notation "L" => FrobeniusSpecialLinearField K E γ R
local notation "J" => frobeniusSpecialLinearInvariantField K E γ R

/-- The relative automorphism group has the exact determinant-one group order. -/
theorem frobeniusSpecialLinearInvariant_card_aut :
    Nat.card (L ≃ₐ[J] L) = q * (q ^ 2 - 1) := by
  apply le_antisymm
  · have h : Nat.card (L ≃ₐ[J] L) ≤ Module.finrank J L := by
      rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    exact h.trans_eq (frobeniusSpecialLinearInvariant_finrank K E γ R)
  · have h := Nat.card_le_card_of_injective (frobeniusSpecialLinearRelativeAut K E γ R)
      (frobeniusSpecialLinearRelativeAut_injective K E γ R)
    rw [specialLinearTwo_card, Nat.card_eq_fintype_card] at h
    exact h

/-- The radical field is Galois over its explicit rational invariant subfield. -/
theorem frobeniusSpecialLinearInvariant_isGalois : IsGalois J L :=
  IsGalois.of_card_aut_eq_finrank J L
    ((frobeniusSpecialLinearInvariant_card_aut K E γ R).trans
      (frobeniusSpecialLinearInvariant_finrank K E γ R).symm)

/-- Every relative automorphism comes from exactly one determinant-one matrix. -/
theorem frobeniusSpecialLinearRelativeAction_bijective :
    Function.Bijective (frobeniusSpecialLinearRelativeAction K E γ R) := by
  apply (frobeniusSpecialLinearRelativeAction_injective K E γ R).bijective_of_nat_card_le
  rw [frobeniusSpecialLinearInvariant_card_aut, specialLinearTwo_card, Nat.card_eq_fintype_card]

/-- The full Galois group over the explicit invariant is the determinant-one matrix group. -/
def frobeniusSpecialLinearGaloisEquiv : SpecialLinearGroup (Fin 2) K ≃* (L ≃ₐ[J] L) :=
  MulEquiv.ofBijective (frobeniusSpecialLinearRelativeAction K E γ R)
    (frobeniusSpecialLinearRelativeAction_bijective K E γ R)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
