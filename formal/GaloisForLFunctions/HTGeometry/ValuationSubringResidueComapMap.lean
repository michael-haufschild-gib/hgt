import GaloisForLFunctions.HTGeometry.ValuationSubringComapDVR

/-!
# Residue maps along exact valuation contractions

An exact pullback equality of valuation subrings gives a canonical local inclusion and hence a
canonical embedding of residue fields.  Its action on literal residue classes is recorded
explicitly for iterated valuation constructions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical residue-field map induced by a field embedding and exact valuation contraction. -/
def valuationSubringResidueMapOfComapEq
    {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (A : ValuationSubring F) (B : ValuationSubring E)
    (h : B.comap f = A) :
    IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B := by
  rw [← h]
  exact IsLocalRing.ResidueField.map (valuationSubringComapInclusion f B)

/-- The contraction residue map sends reduction of a source element to reduction of its field
image. -/
theorem valuationSubringResidueMapOfComapEq_residue
    {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (A : ValuationSubring F) (B : ValuationSubring E)
    (h : B.comap f = A) (x : F) (hx : x ∈ A) :
    let hfx : f x ∈ B := by
      change x ∈ B.comap f
      rw [h]
      exact hx
    valuationSubringResidueMapOfComapEq f A B h
        (IsLocalRing.residue A (⟨x, hx⟩ : A)) =
      IsLocalRing.residue B (⟨f x, hfx⟩ : B) := by
  subst A
  rfl

/-- Exact-contraction residue transport is an embedding of fields. -/
theorem valuationSubringResidueMapOfComapEq_injective
    {F E : Type*} [Field F] [Field E]
    (f : F →+* E) (A : ValuationSubring F) (B : ValuationSubring E)
    (h : B.comap f = A) :
    Function.Injective (valuationSubringResidueMapOfComapEq f A B h) :=
  RingHom.injective _

end

end GaloisForLFunctions.HTGeometry
