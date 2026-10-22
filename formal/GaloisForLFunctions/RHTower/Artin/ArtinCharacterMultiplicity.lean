import GaloisForLFunctions.RHTower.Artin.ArtinMonomialCharacter

/-!
# Canonical multiplicities of genuine and virtual characters

Pairing-integrality witnesses are unique because natural and integer casts into `ℂ` are
injective. Extracting those witnesses gives canonical multiplicity functions. The virtual
multiplicity is biadditive, compatible with negation, and nonnegative on genuine characters.
-/

noncomputable section

universe u

namespace GaloisForLFunctions

variable (G : Type u) [Group G] [Fintype G]

/-- Canonical natural-valued pairing multiplicity of two genuine characters. -/
def genuineMultiplicity (χ ψ : GenuineCharacter G) : ℕ :=
  (genuineCharacterPairing_eq_natCast G χ ψ).choose

@[simp]
theorem genuineMultiplicity_cast (χ ψ : GenuineCharacter G) :
    (genuineMultiplicity G χ ψ : ℂ) = characterPairing G χ.val ψ.val :=
  (genuineCharacterPairing_eq_natCast G χ ψ).choose_spec.symm

/-- Canonical integer-valued pairing multiplicity of two virtual characters. -/
def virtualMultiplicity (χ ψ : VirtualCharacter G) : ℤ :=
  (virtualCharacterPairing_eq_intCast G χ ψ).choose

@[simp]
theorem virtualMultiplicity_cast (χ ψ : VirtualCharacter G) :
    (virtualMultiplicity G χ ψ : ℂ) = characterPairing G χ.val ψ.val :=
  (virtualCharacterPairing_eq_intCast G χ ψ).choose_spec.symm

/-- Virtual multiplicity of two genuine characters is the integer cast of their genuine
multiplicity. -/
theorem virtualMultiplicity_toVirtual (χ ψ : GenuineCharacter G) :
    virtualMultiplicity G (GenuineCharacter.toVirtual G χ) (GenuineCharacter.toVirtual G ψ) =
      (genuineMultiplicity G χ ψ : ℤ) := by
  apply Int.cast_injective (α := ℂ)
  rw [virtualMultiplicity_cast]
  change characterPairing G χ.val ψ.val = ((genuineMultiplicity G χ ψ : ℤ) : ℂ)
  rw [Int.cast_natCast, genuineMultiplicity_cast]

/-- Genuine-character multiplicities are nonnegative when viewed as virtual multiplicities. -/
theorem virtualMultiplicity_toVirtual_nonneg (χ ψ : GenuineCharacter G) :
    0 ≤ virtualMultiplicity G (GenuineCharacter.toVirtual G χ)
      (GenuineCharacter.toVirtual G ψ) := by
  rw [virtualMultiplicity_toVirtual]
  exact Int.natCast_nonneg _

theorem virtualMultiplicity_add_left (χ₁ χ₂ ψ : VirtualCharacter G) :
    virtualMultiplicity G (χ₁ + χ₂) ψ =
      virtualMultiplicity G χ₁ ψ + virtualMultiplicity G χ₂ ψ := by
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_add, virtualMultiplicity_cast, AddSubgroup.coe_add,
    characterPairing_add_left]

theorem virtualMultiplicity_add_right (χ ψ₁ ψ₂ : VirtualCharacter G) :
    virtualMultiplicity G χ (ψ₁ + ψ₂) =
      virtualMultiplicity G χ ψ₁ + virtualMultiplicity G χ ψ₂ := by
  apply Int.cast_injective (α := ℂ)
  simp only [Int.cast_add, virtualMultiplicity_cast, AddSubgroup.coe_add,
    characterPairing_add_right]

theorem virtualMultiplicity_neg_left (χ ψ : VirtualCharacter G) :
    virtualMultiplicity G (-χ) ψ = -virtualMultiplicity G χ ψ := by
  apply Int.cast_injective (α := ℂ)
  rw [virtualMultiplicity_cast]
  change characterPairing G (-χ.val) ψ.val = ((-virtualMultiplicity G χ ψ : ℤ) : ℂ)
  rw [characterPairing_neg_left, Int.cast_neg, virtualMultiplicity_cast]

theorem virtualMultiplicity_neg_right (χ ψ : VirtualCharacter G) :
    virtualMultiplicity G χ (-ψ) = -virtualMultiplicity G χ ψ := by
  apply Int.cast_injective (α := ℂ)
  rw [virtualMultiplicity_cast]
  change characterPairing G χ.val (-ψ.val) = ((-virtualMultiplicity G χ ψ : ℤ) : ℂ)
  rw [characterPairing_neg_right, Int.cast_neg, virtualMultiplicity_cast]

/-- Multiplicity of a virtual character against a concrete monomial character. -/
def monomialMultiplicity (θ : VirtualCharacter G) (H : Subgroup G)
    (χ : LinearCharacter H) : ℤ :=
  virtualMultiplicity G θ (monomialVirtualCharacter G H χ)

theorem monomialMultiplicity_add (θ₁ θ₂ : VirtualCharacter G) (H : Subgroup G)
    (χ : LinearCharacter H) :
    monomialMultiplicity G (θ₁ + θ₂) H χ =
      monomialMultiplicity G θ₁ H χ + monomialMultiplicity G θ₂ H χ :=
  virtualMultiplicity_add_left G θ₁ θ₂ (monomialVirtualCharacter G H χ)

/-- Every genuine character has nonnegative multiplicity against every monomial character. -/
theorem monomialMultiplicity_genuine_nonneg (θ : GenuineCharacter G) (H : Subgroup G)
    (χ : LinearCharacter H) :
    0 ≤ monomialMultiplicity G (GenuineCharacter.toVirtual G θ) H χ := by
  exact virtualMultiplicity_toVirtual_nonneg G θ (monomialGenuineCharacter G H χ)

end GaloisForLFunctions
