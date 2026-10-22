import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Concrete virtual characters for the Artin program

Genuine characters are additive-monoid closure of characters of actual finite-dimensional complex
representations. Virtual characters are corresponding additive-group closure. This gives concrete
carriers for Brauer induction, monomial characters, and Heilbronn order characters; membership is
generated from actual `FDRep` objects rather than asserted through an abstract proposition.
-/

noncomputable section

universe u v w

namespace GaloisForLFunctions

variable (G : Type u) [Group G]

/-- Character functions of actual finite-dimensional complex representations of `G`. -/
def fdCharacterSet : Set (G → ℂ) :=
  Set.range fun V : FDRep ℂ G ↦ V.character

/-- Transport any finite-dimensional complex representation, regardless of carrier universe, to
the canonical small coordinate space `Fin (finrank ℂ V) → ℂ`. -/
def smallModelRepresentation {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Module.finBasis ℂ V).equivFun.conjRingEquiv).toMonoidHom.comp ρ

/-- Coordinate transport is an equivalence of the original representation with its small model. -/
def smallModelEquiv {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ρ.Equiv (smallModelRepresentation G ρ) := by
  apply Representation.Equiv.mk (Module.finBasis ℂ V).equivFun
  intro g
  ext x
  simp [smallModelRepresentation]

/-- Canonical `FDRep` model of an arbitrary finite-dimensional complex representation. -/
def smallModelFDRep {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) : FDRep ℂ G :=
  FDRep.of (smallModelRepresentation G ρ)

/-- Passing to the canonical small model does not change the character. -/
theorem smallModelFDRep_character {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    (smallModelFDRep G ρ).character = ρ.character := by
  exact (Representation.char_iso (smallModelEquiv G ρ)).symm

/-- The character of every finite-dimensional complex representation, in any carrier universe,
belongs to the concrete `FDRep` generator set. -/
theorem representation_character_mem_fdCharacterSet {V : Type w} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ρ.character ∈ fdCharacterSet G :=
  ⟨smallModelFDRep G ρ, smallModelFDRep_character G ρ⟩

/-- Genuine characters, constructed as finite sums of actual `FDRep` characters. -/
def genuineCharacterMonoid : AddSubmonoid (G → ℂ) :=
  AddSubmonoid.closure (fdCharacterSet G)

/-- Virtual characters, constructed as integer linear combinations of actual `FDRep` characters. -/
def virtualCharacterGroup : AddSubgroup (G → ℂ) :=
  AddSubgroup.closure (fdCharacterSet G)

/-- Concrete genuine complex characters of `G`. -/
abbrev GenuineCharacter := genuineCharacterMonoid G

/-- Concrete virtual complex characters of `G`. -/
abbrev VirtualCharacter := virtualCharacterGroup G

/-- Every genuine character is canonically a virtual character. -/
theorem genuineCharacterMonoid_le_virtualCharacterGroup :
    (genuineCharacterMonoid G : Set (G → ℂ)) ⊆ virtualCharacterGroup G := by
  intro χ hχ
  induction hχ using AddSubmonoid.closure_induction with
  | mem χ hχ => exact AddSubgroup.subset_closure hχ
  | zero => exact (virtualCharacterGroup G).zero_mem
  | add χ ψ _ _ hχ hψ => exact (virtualCharacterGroup G).add_mem hχ hψ

/-- Canonical inclusion of genuine characters into virtual characters. -/
def GenuineCharacter.toVirtual (χ : GenuineCharacter G) : VirtualCharacter G :=
  ⟨χ, genuineCharacterMonoid_le_virtualCharacterGroup G χ.property⟩

/-- Additive precomposition on complex-valued functions. -/
def characterRestrictFunction {H : Type v} [Group H] (φ : H →* G) :
    (G → ℂ) →+ (H → ℂ) where
  toFun f := f ∘ φ
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction of an actual finite-dimensional representation along a group homomorphism. -/
def restrictFDRep {H : Type v} [Group H] (φ : H →* G) (V : FDRep ℂ G) : FDRep ℂ H :=
  FDRep.of (V.ρ.comp φ)

@[simp]
theorem restrictFDRep_character {H : Type v} [Group H] (φ : H →* G)
    (V : FDRep ℂ G) (h : H) :
    (restrictFDRep G φ V).character h = V.character (φ h) := rfl

/-- Restriction preserves concrete virtual characters because it restricts every actual
representation generator and commutes with addition and negation. -/
def VirtualCharacter.restrict {H : Type v} [Group H] (φ : H →* G)
    (χ : VirtualCharacter G) : VirtualCharacter H := by
  refine ⟨characterRestrictFunction G φ χ.val, ?_⟩
  change characterRestrictFunction G φ χ.val ∈ virtualCharacterGroup H
  refine AddSubgroup.closure_induction (p := fun f _ ↦
    characterRestrictFunction G φ f ∈ virtualCharacterGroup H) ?_ ?_ ?_ ?_ χ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    apply AddSubgroup.subset_closure
    exact ⟨restrictFDRep G φ V, by funext h; rfl⟩
  · exact (virtualCharacterGroup H).zero_mem
  · intro f g _ _ hf hg
    exact (virtualCharacterGroup H).add_mem hf hg
  · intro f _ hf
    exact (virtualCharacterGroup H).neg_mem hf

/-- Restriction preserves concrete genuine characters. -/
def GenuineCharacter.restrict {H : Type v} [Group H] (φ : H →* G)
    (χ : GenuineCharacter G) : GenuineCharacter H := by
  refine ⟨characterRestrictFunction G φ χ.val, ?_⟩
  change characterRestrictFunction G φ χ.val ∈ genuineCharacterMonoid H
  refine AddSubmonoid.closure_induction (motive := fun f _ ↦
    characterRestrictFunction G φ f ∈ genuineCharacterMonoid H) ?_ ?_ ?_ χ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    apply AddSubmonoid.subset_closure
    exact ⟨restrictFDRep G φ V, by funext h; rfl⟩
  · exact (genuineCharacterMonoid H).zero_mem
  · intro f g _ _ hf hg
    exact (genuineCharacterMonoid H).add_mem hf hg

@[simp]
theorem VirtualCharacter.restrict_apply {H : Type v} [Group H] (φ : H →* G)
    (χ : VirtualCharacter G) (h : H) :
    (VirtualCharacter.restrict G φ χ).val h = χ.val (φ h) := rfl

@[simp]
theorem GenuineCharacter.restrict_apply {H : Type v} [Group H] (φ : H →* G)
    (χ : GenuineCharacter G) (h : H) :
    (GenuineCharacter.restrict G φ χ).val h = χ.val (φ h) := rfl

@[simp]
theorem GenuineCharacter.toVirtual_restrict {H : Type v} [Group H] (φ : H →* G)
    (χ : GenuineCharacter G) :
    GenuineCharacter.toVirtual H (GenuineCharacter.restrict G φ χ) =
      VirtualCharacter.restrict G φ (GenuineCharacter.toVirtual G χ) := rfl

/-- Every concrete virtual character is invariant under conjugation. -/
theorem VirtualCharacter.conj_invariant (χ : VirtualCharacter G) (g h : G) :
    χ.val (h * g * h⁻¹) = χ.val g := by
  refine AddSubgroup.closure_induction (p := fun f _ ↦
    f (h * g * h⁻¹) = f g) ?_ ?_ ?_ ?_ χ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    exact FDRep.char_conj V g h
  · rfl
  · intro f k _ _ hf hk
    simpa using congrArg₂ (· + ·) hf hk
  · intro f _ hf
    simpa using congrArg Neg.neg hf

/-- Degree at the identity of a genuine character is a natural number. -/
theorem GenuineCharacter.one_eq_natCast (χ : GenuineCharacter G) :
    ∃ n : ℕ, χ.val 1 = (n : ℂ) := by
  refine AddSubmonoid.closure_induction (motive := fun f _ ↦
    ∃ n : ℕ, f 1 = (n : ℂ)) ?_ ?_ ?_ χ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    exact ⟨Module.finrank ℂ V, FDRep.char_one V⟩
  · exact ⟨0, by simp⟩
  · intro f k _ _ hf hk
    obtain ⟨m, hm⟩ := hf
    obtain ⟨n, hn⟩ := hk
    exact ⟨m + n, by simp [hm, hn]⟩

/-- Degree at the identity of a virtual character is an integer. -/
theorem VirtualCharacter.one_eq_intCast (χ : VirtualCharacter G) :
    ∃ z : ℤ, χ.val 1 = (z : ℂ) := by
  refine AddSubgroup.closure_induction (p := fun f _ ↦
    ∃ z : ℤ, f 1 = (z : ℂ)) ?_ ?_ ?_ ?_ χ.property
  · intro f hf
    obtain ⟨V, rfl⟩ := hf
    exact ⟨Module.finrank ℂ V, by simp⟩
  · exact ⟨0, by simp⟩
  · intro f k _ _ hf hk
    obtain ⟨m, hm⟩ := hf
    obtain ⟨n, hn⟩ := hk
    exact ⟨m + n, by simp [hm, hn]⟩
  · intro f _ hf
    obtain ⟨m, hm⟩ := hf
    exact ⟨-m, by simp [hm]⟩

end GaloisForLFunctions
