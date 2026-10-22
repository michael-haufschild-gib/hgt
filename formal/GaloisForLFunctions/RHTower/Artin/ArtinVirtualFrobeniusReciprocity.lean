import GaloisForLFunctions.RHTower.Artin.ArtinCharacterMultiplicity

/-!
# Frobenius reciprocity for concrete virtual Artin characters

This file extends the actual-representation Frobenius reciprocity pairing to the concrete
virtual-character carrier, then identifies the resulting integral monomial coefficient with the
linear-character multiplicity after restriction.  It contains no analytic order character or
effectivity assertion.
-/

open scoped BigOperators Classical

noncomputable section

universe u

namespace GaloisForLFunctions

/-- The finite character pairing is symmetric. -/
theorem characterPairing_comm (G : Type u) [Group G] [Fintype G]
    (χ ψ : G → ℂ) :
    characterPairing G χ ψ = characterPairing G ψ χ := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv G) (fun g => ψ g * χ g⁻¹)
    (fun g => χ g * ψ g⁻¹) ?_
  intro g
  simp [mul_comm]

/-- Frobenius reciprocity for the pairing of a concrete virtual character with an induced linear
character. -/
theorem virtualCharacter_monomial_pairing_restriction
    (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) (θ : VirtualCharacter G) :
    characterPairing G θ.val (monomialVirtualCharacter G H χ).val =
      characterPairing H (VirtualCharacter.restrict G H.subtype θ).val
        (linearVirtualCharacter H χ).val := by
  change characterPairing G θ.val (monomialVirtualCharacter G H χ).val =
    characterPairing H (characterRestrictFunction G H.subtype θ.val)
      (linearVirtualCharacter H χ).val
  refine AddSubgroup.closure_induction (p := fun f _ =>
    characterPairing G f (monomialVirtualCharacter G H χ).val =
      characterPairing H (characterRestrictFunction G H.subtype f)
        (linearVirtualCharacter H χ).val) ?_ ?_ ?_ ?_ θ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    change characterPairing G V.character (monomialGenuineCharacter G H χ).val =
      characterPairing H (Representation.character (V.ρ.comp H.subtype))
        (linearGenuineCharacter H χ).val
    rw [characterPairing_comm G]
    calc
      characterPairing G (monomialGenuineCharacter G H χ).val V.character =
          characterPairing H (linearCharacterRepresentation χ).character
            (Representation.character (V.ρ.comp H.subtype)) :=
        monomialCharacter_pairing_eq_restricted G H χ V.ρ
      _ = characterPairing H (Representation.character (V.ρ.comp H.subtype))
          (linearGenuineCharacter H χ).val := by
        change characterPairing H (linearCharacterRepresentation χ).character
          (Representation.character (V.ρ.comp H.subtype)) =
            characterPairing H (Representation.character (V.ρ.comp H.subtype))
              (linearCharacterRepresentation χ).character
        exact characterPairing_comm H _ _
  · simp
  · intro f g _ _ hf hg
    simpa only [map_add, characterPairing_add_left, characterPairing_add_right] using
      congrArg₂ (· + ·) hf hg
  · intro f _ hf
    simpa only [map_neg, characterPairing_neg_left, characterPairing_neg_right] using
      congrArg Neg.neg hf

/-- The integral multiplicity of a monomial character is exactly the integral multiplicity of its
linear source after restriction. -/
theorem monomialMultiplicity_eq_restriction_linearMultiplicity
    (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) (θ : VirtualCharacter G) :
    monomialMultiplicity G θ H χ =
      virtualMultiplicity H (VirtualCharacter.restrict G H.subtype θ)
        (linearVirtualCharacter H χ) := by
  apply Int.cast_injective (α := ℂ)
  change (virtualMultiplicity G θ (monomialVirtualCharacter G H χ) : ℂ) =
    (virtualMultiplicity H (VirtualCharacter.restrict G H.subtype θ)
      (linearVirtualCharacter H χ) : ℂ)
  rw [virtualMultiplicity_cast, virtualMultiplicity_cast]
  exact virtualCharacter_monomial_pairing_restriction G H χ θ

end GaloisForLFunctions
