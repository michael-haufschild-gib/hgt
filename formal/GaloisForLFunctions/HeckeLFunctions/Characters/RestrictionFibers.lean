import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysDivisibleExtension
import GaloisForLFunctions.RHTower.Deninger.DeningerFiniteCharacterBasis

/-!
# Fibres of complex-character restriction

Every character of a subgroup of an abelian group extends to the whole group.
The extensions of a fixed character are in bijection with the characters of the
quotient: dividing two extensions removes their common restriction. For a finite
quotient their number is exactly the quotient order, without a splitting assumption.
This is the extension mechanism of Proposition 3.12 of arXiv:2610.23742.
-/

noncomputable section
namespace GaloisForLFunctions.HeckeLFunctions.CharacterExtensions

variable {G : Type*} [CommGroup G] (H : Subgroup G)

/-- Complex characters restrict onto every subgroup character. -/
theorem restriction_surjective :
    Function.Surjective (MonoidHom.restrictHom H ℂˣ) := by
  intro ψ
  obtain ⟨χ, hχ⟩ := RHTower.deningerExtend_of_rootableBy H.subtype
    Subtype.val_injective ψ
  exact ⟨χ, hχ⟩

/-- All extensions of a fixed character form one copy of the quotient character group. -/
def extensionEquiv (ψ : H →* ℂˣ) :
    {χ : G →* ℂˣ // χ.comp H.subtype = ψ} ≃ (G ⧸ H →* ℂˣ) :=
  (MonoidHom.fiberEquivKerOfSurjective (restriction_surjective H) ψ).trans
    (MonoidHom.restrictHomKerEquiv ℂˣ H).toEquiv

/-- There is an extension for every subgroup character, even when the quotient is infinite. -/
theorem extensions_nonempty (ψ : H →* ℂˣ) :
    Nonempty {χ : G →* ℂˣ // χ.comp H.subtype = ψ} :=
  ⟨(extensionEquiv H ψ).symm 1⟩

/-- A finite-index subgroup character has exactly as many extensions as the index. -/
theorem card_extensions [Finite (G ⧸ H)] (ψ : H →* ℂˣ) :
    Nat.card {χ : G →* ℂˣ // χ.comp H.subtype = ψ} = Nat.card (G ⧸ H) := by
  rw [Nat.card_congr (extensionEquiv H ψ), RHTower.deningerCharacter_card]

#print axioms extensionEquiv
#print axioms extensions_nonempty
#print axioms card_extensions

end GaloisForLFunctions.HeckeLFunctions.CharacterExtensions
