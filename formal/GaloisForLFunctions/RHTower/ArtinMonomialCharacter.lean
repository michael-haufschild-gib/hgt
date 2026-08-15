import GaloisForLFunctions.RHTower.ArtinFrobeniusReciprocity

/-!
# Linear and monomial characters for the Artin program

A complex linear character is represented concretely by a homomorphism into `ℂˣ`. Its actual
one-dimensional representation acts by scalar multiplication. Inducing this representation from
a subgroup constructs the monomial genuine and virtual characters used by Brauer induction.
-/

noncomputable section

universe u v

namespace GaloisForLFunctions

/-- Concrete complex linear character of a group. -/
abbrev LinearCharacter (H : Type u) [Group H] := H →* ℂˣ

/-- Actual one-dimensional representation attached to a complex linear character. -/
def linearCharacterRepresentation {H : Type u} [Group H] (χ : LinearCharacter H) :
    Representation ℂ H ℂ where
  toFun h := LinearMap.mulLeft ℂ (χ h : ℂ)
  map_one' := by
    ext
    simp
  map_mul' h k := by
    ext
    simp

/-- Character of the scalar-multiplication representation is the original linear character. -/
theorem linearCharacterRepresentation_character {H : Type u} [Group H]
    (χ : LinearCharacter H) (h : H) :
    (linearCharacterRepresentation χ).character h = (χ h : ℂ) := by
  change LinearMap.trace ℂ ℂ (LinearMap.mulLeft ℂ (χ h : ℂ)) = (χ h : ℂ)
  have hmul : LinearMap.mulLeft ℂ (χ h : ℂ) =
      (χ h : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) := by
    ext
    simp
  rw [hmul, map_smul]
  simp

/-- The concrete genuine character associated to a linear character. -/
def linearGenuineCharacter (G : Type u) [Group G] [Fintype G]
    (χ : LinearCharacter G) : GenuineCharacter G :=
  ⟨(linearCharacterRepresentation χ).character,
    AddSubmonoid.subset_closure
      (representation_character_mem_fdCharacterSet G (linearCharacterRepresentation χ))⟩

/-- The concrete virtual character associated to a linear character. -/
def linearVirtualCharacter (G : Type u) [Group G] [Fintype G]
    (χ : LinearCharacter G) : VirtualCharacter G :=
  GenuineCharacter.toVirtual G (linearGenuineCharacter G χ)

/-- A concrete genuine linear character has its expected pointwise values. -/
@[simp]
theorem linearGenuineCharacter_apply (G : Type u) [Group G] [Fintype G]
    (χ : LinearCharacter G) (g : G) :
    (linearGenuineCharacter G χ).val g = (χ g : ℂ) :=
  linearCharacterRepresentation_character χ g

/-- A concrete virtual linear character has its expected pointwise values. -/
@[simp]
theorem linearVirtualCharacter_apply (G : Type u) [Group G] [Fintype G]
    (χ : LinearCharacter G) (g : G) :
    (linearVirtualCharacter G χ).val g = (χ g : ℂ) :=
  linearGenuineCharacter_apply G χ g

@[simp]
theorem linearCharacterRepresentation_character_one {H : Type u} [Group H]
    (χ : LinearCharacter H) :
    (linearCharacterRepresentation χ).character 1 = 1 := by
  simp

/-- Genuine monomial character induced from a concrete linear character of a subgroup. -/
def monomialGenuineCharacter (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) : GenuineCharacter G :=
  inducedGenuineCharacter G H (linearCharacterRepresentation χ)

/-- Canonical virtual character underlying a genuine monomial character. -/
def monomialVirtualCharacter (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) : VirtualCharacter G :=
  inducedVirtualCharacter G H (linearCharacterRepresentation χ)

@[simp]
theorem monomialGenuineCharacter_apply (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) (g : G) :
    (monomialGenuineCharacter G H χ).val g =
      (Representation.ind H.subtype (linearCharacterRepresentation χ)).character g := rfl

@[simp]
theorem monomialVirtualCharacter_apply (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H) (g : G) :
    (monomialVirtualCharacter G H χ).val g =
      (Representation.ind H.subtype (linearCharacterRepresentation χ)).character g := rfl

open scoped Classical in
/-- Frobenius reciprocity specialized to a monomial character generator. -/
theorem monomialCharacter_pairing_eq_restricted
    (G : Type u) [Group G] [Fintype G]
    (H : Subgroup G) (χ : LinearCharacter H)
    {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) :
    characterPairing G (monomialGenuineCharacter G H χ).val σ.character =
      characterPairing H (linearCharacterRepresentation χ).character
        (Representation.character (σ.comp H.subtype)) :=
  characterPairing_induced_restricted H.subtype (linearCharacterRepresentation χ) σ

end GaloisForLFunctions
