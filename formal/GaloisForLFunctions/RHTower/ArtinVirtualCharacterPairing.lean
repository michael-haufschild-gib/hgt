import GaloisForLFunctions.RHTower.ArtinVirtualCharacter
import Mathlib.RepresentationTheory.FinGroupCharZero

/-!
# Integral pairing of concrete virtual characters

The normalized finite-group character pairing is identified with the dimension of an actual
equivariant-Hom space on `FDRep` generators. Double closure induction then proves natural-valued
pairing for genuine characters and integer-valued pairing for virtual characters.
-/

open scoped BigOperators

noncomputable section

universe u v w

namespace GaloisForLFunctions

variable (G : Type u) [Group G] [Fintype G]

/-- Normalized character pairing, ordered so actual representation characters pair to
`finrank (V ⟶ W)`. -/
def characterPairing (χ ψ : G → ℂ) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, ψ g * χ g⁻¹

/-- The normalized pairing of characters of arbitrary finite-dimensional representations is the
dimension of their intertwining space. Carrier universes may differ. -/
theorem representationCharacterPairing_eq_finrank
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    characterPairing G ρ.character σ.character =
      (Module.finrank ℂ (ρ.IntertwiningMap σ) : ℂ) := by
  letI := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ

/-- The normalized pairing of two actual characters is the dimension of their equivariant-Hom
space. -/
theorem fdCharacterPairing_eq_finrank (V W : FDRep ℂ G) :
    characterPairing G V.character W.character =
      (Module.finrank ℂ (V ⟶ W) : ℂ) := by
  letI := invertibleOfNonzero (NeZero.ne (Nat.card G : ℂ))
  exact FDRep.scalar_product_char_eq_finrank_equivariant V W

@[simp]
theorem characterPairing_zero_left (ψ : G → ℂ) :
    characterPairing G 0 ψ = 0 := by
  simp [characterPairing]

@[simp]
theorem characterPairing_zero_right (χ : G → ℂ) :
    characterPairing G χ 0 = 0 := by
  simp [characterPairing]

@[simp]
theorem characterPairing_add_left (χ₁ χ₂ ψ : G → ℂ) :
    characterPairing G (χ₁ + χ₂) ψ =
      characterPairing G χ₁ ψ + characterPairing G χ₂ ψ := by
  simp [characterPairing, mul_add, Finset.sum_add_distrib]

@[simp]
theorem characterPairing_add_right (χ ψ₁ ψ₂ : G → ℂ) :
    characterPairing G χ (ψ₁ + ψ₂) =
      characterPairing G χ ψ₁ + characterPairing G χ ψ₂ := by
  simp [characterPairing, add_mul, mul_add, Finset.sum_add_distrib]

@[simp]
theorem characterPairing_neg_left (χ ψ : G → ℂ) :
    characterPairing G (-χ) ψ = -characterPairing G χ ψ := by
  simp [characterPairing]

@[simp]
theorem characterPairing_neg_right (χ ψ : G → ℂ) :
    characterPairing G χ (-ψ) = -characterPairing G χ ψ := by
  simp [characterPairing]

/-- The pairing of two concrete genuine characters is a natural number. -/
theorem genuineCharacterPairing_eq_natCast (χ ψ : GenuineCharacter G) :
    ∃ n : ℕ, characterPairing G χ.val ψ.val = (n : ℂ) := by
  refine AddSubmonoid.closure_induction (motive := fun f _ ↦
    ∀ ψ : GenuineCharacter G, ∃ n : ℕ, characterPairing G f ψ.val = (n : ℂ))
      ?_ ?_ ?_ χ.property ψ
  · intro f hf ψ
    obtain ⟨V, rfl⟩ := hf
    refine AddSubmonoid.closure_induction (motive := fun f _ ↦
      ∃ n : ℕ, characterPairing G V.character f = (n : ℂ)) ?_ ?_ ?_ ψ.property
    · intro f hf
      obtain ⟨W, rfl⟩ := hf
      exact ⟨Module.finrank ℂ (V ⟶ W), fdCharacterPairing_eq_finrank G V W⟩
    · exact ⟨0, by simp⟩
    · intro f k _ _ hf hk
      obtain ⟨m, hm⟩ := hf
      obtain ⟨n, hn⟩ := hk
      exact ⟨m + n, by simp [hm, hn]⟩
  · intro ψ
    exact ⟨0, by simp⟩
  · intro f k _ _ hf hk ψ
    obtain ⟨m, hm⟩ := hf ψ
    obtain ⟨n, hn⟩ := hk ψ
    exact ⟨m + n, by simp [hm, hn]⟩

/-- The pairing of two concrete virtual characters is an integer. -/
theorem virtualCharacterPairing_eq_intCast (χ ψ : VirtualCharacter G) :
    ∃ z : ℤ, characterPairing G χ.val ψ.val = (z : ℂ) := by
  refine AddSubgroup.closure_induction (p := fun f _ ↦
    ∀ ψ : VirtualCharacter G, ∃ z : ℤ, characterPairing G f ψ.val = (z : ℂ))
      ?_ ?_ ?_ ?_ χ.property ψ
  · intro f hf ψ
    obtain ⟨V, rfl⟩ := hf
    refine AddSubgroup.closure_induction (p := fun f _ ↦
      ∃ z : ℤ, characterPairing G V.character f = (z : ℂ)) ?_ ?_ ?_ ?_ ψ.property
    · intro f hf
      obtain ⟨W, rfl⟩ := hf
      exact ⟨(Module.finrank ℂ (V ⟶ W) : ℤ), by
        simpa using fdCharacterPairing_eq_finrank G V W⟩
    · exact ⟨0, by simp⟩
    · intro f k _ _ hf hk
      obtain ⟨m, hm⟩ := hf
      obtain ⟨n, hn⟩ := hk
      exact ⟨m + n, by simp [hm, hn]⟩
    · intro f _ hf
      obtain ⟨m, hm⟩ := hf
      exact ⟨-m, by simp [hm]⟩
  · intro ψ
    exact ⟨0, by simp⟩
  · intro f k _ _ hf hk ψ
    obtain ⟨m, hm⟩ := hf ψ
    obtain ⟨n, hn⟩ := hk ψ
    exact ⟨m + n, by simp [hm, hn]⟩
  · intro f _ hf ψ
    obtain ⟨m, hm⟩ := hf ψ
    exact ⟨-m, by simp [hm]⟩

end GaloisForLFunctions
