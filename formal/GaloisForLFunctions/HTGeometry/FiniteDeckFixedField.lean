import GaloisForLFunctions.HTGeometry.DeckClosureStableCore

/-!
# Finite deck quotients determine iterate images

For a finite-depth quotient, two geometric facts determine its rational function field:

* every deck transformation fixes the pullback image;
* extension degree equals deck-group cardinality.

Artin's fixed-field degree theorem then identifies the pullback image with the full deck fixed
field.  Applying this at every depth removes the image/fixed-field equality hypothesis from the
stable deck-closure theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A finite-depth iterate image is the full deck fixed field when deck transformations fix that
image and its extension degree is exactly the deck-group cardinality. -/
theorem iterateImage_eq_fixedField_of_finiteDeckDegree
    (phi : L →ₐ[K] L)
    (deck : ℕ → Subgroup (L ≃ₐ[K] L))
    (hfinite : ∀ n, Finite (deck n))
    (hfiniteDimensional : ∀ n,
      FiniteDimensional (IntermediateField.map (phi ^ n) ⊤) L)
    (hfixed : ∀ n (sigma : L ≃ₐ[K] L), sigma ∈ deck n → ∀ x : L,
      sigma ((phi ^ n) x) = (phi ^ n) x)
    (hdegree : ∀ n,
      Module.finrank (IntermediateField.map (phi ^ n) ⊤) L = Nat.card (deck n))
    (n : ℕ) :
    IntermediateField.map (phi ^ n) ⊤ = IntermediateField.fixedField (deck n) := by
  letI : Finite (deck n) := hfinite n
  letI : FiniteDimensional (IntermediateField.map (phi ^ n) ⊤) L :=
    hfiniteDimensional n
  apply eq_fixedField_of_le_of_finite_of_finrank_eq_card
  · intro z hz
    rw [IntermediateField.mem_fixedField_iff]
    intro sigma hsigma
    rw [IntermediateField.mem_map] at hz
    obtain ⟨x, -, rfl⟩ := hz
    exact hfixed n sigma hsigma x
  · exact hdegree n

/-- Stable tail equals the total finite-deck fixed field using quotient invariance and degree data,
without assuming any finite-depth image/fixed-field equality. -/
theorem stableRangeCore_eq_fixedField_iSup_of_finiteDeckDegree
    (phi : L →ₐ[K] L)
    (deck : ℕ → Subgroup (L ≃ₐ[K] L))
    (hfinite : ∀ n, Finite (deck n))
    (hfiniteDimensional : ∀ n,
      FiniteDimensional (IntermediateField.map (phi ^ n) ⊤) L)
    (hfixed : ∀ n (sigma : L ≃ₐ[K] L), sigma ∈ deck n → ∀ x : L,
      sigma ((phi ^ n) x) = (phi ^ n) x)
    (hdegree : ∀ n,
      Module.finrank (IntermediateField.map (phi ^ n) ⊤) L = Nat.card (deck n)) :
    stableRangeCore phi = IntermediateField.fixedField (⨆ n, deck n) := by
  apply stableRangeCore_eq_fixedField_iSup phi deck
  exact iterateImage_eq_fixedField_of_finiteDeckDegree
    phi deck hfinite hfiniteDimensional hfixed hdegree

end

end GaloisForLFunctions.HTGeometry
