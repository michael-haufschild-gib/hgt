import GaloisForLFunctions.RHTower.ArtinVirtualCharacter
import Mathlib.RepresentationTheory.FiniteIndex

/-!
# Actual induced representations and their concrete characters

Mathlib's induced representation can have a carrier in the group universe, whereas `FDRep ℂ G`
requires a carrier in the scalar universe. The small-model bridge proves that the actual induced
character nevertheless belongs to the concrete `FDRep` character generator set without narrowing
the universe of the finite group or the original representation.
-/

noncomputable section

universe u w

namespace GaloisForLFunctions

variable (G : Type u) [Group G] [Fintype G]

/-- Standard induced representation on `(ℂ[G] ⊗ V)_H`. -/
def inducedRepresentation (H : Subgroup G) {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) :
    Representation ℂ G (Representation.IndV H.subtype ρ) :=
  Representation.ind H.subtype ρ

/-- The character of an actual induced representation is a concrete `FDRep` character generator,
after universe-safe coordinate smallification. -/
theorem inducedRepresentation_character_mem_fdCharacterSet (H : Subgroup G)
    {V : Type w} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) :
    (inducedRepresentation G H ρ).character ∈ fdCharacterSet G :=
  representation_character_mem_fdCharacterSet G (inducedRepresentation G H ρ)

/-- Genuine character supplied by an actual induced representation. -/
def inducedGenuineCharacter (H : Subgroup G) {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) : GenuineCharacter G :=
  ⟨(inducedRepresentation G H ρ).character,
    AddSubmonoid.subset_closure (inducedRepresentation_character_mem_fdCharacterSet G H ρ)⟩

/-- Virtual character supplied canonically by an actual induced representation. -/
def inducedVirtualCharacter (H : Subgroup G) {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) : VirtualCharacter G :=
  GenuineCharacter.toVirtual G (inducedGenuineCharacter G H ρ)

@[simp]
theorem inducedGenuineCharacter_apply (H : Subgroup G) {V : Type w} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) (g : G) :
    (inducedGenuineCharacter G H ρ).val g =
      (Representation.ind H.subtype ρ).character g := rfl

@[simp]
theorem inducedVirtualCharacter_apply (H : Subgroup G) {V : Type w} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ H V) (g : G) :
    (inducedVirtualCharacter G H ρ).val g =
      (Representation.ind H.subtype ρ).character g := rfl

end GaloisForLFunctions
