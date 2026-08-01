import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Automorphisms are determined on a generating set

The elements on which two algebra automorphisms agree form an intermediate field, so two
automorphisms agreeing on a generating set are equal.

This is the engine behind every rigidity step for Galois groups: an automorphism of a splitting
field is determined by where it sends the roots.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The elements on which two algebra automorphisms agree. -/
def algEquivEqualizer (σ τ : L ≃ₐ[F] L) : IntermediateField F L where
  carrier := {x | σ x = τ x}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, map_add, ha, hb]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, map_inv₀, ha]
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_setOf_eq, AlgEquiv.commutes]

@[simp]
theorem mem_algEquivEqualizer {σ τ : L ≃ₐ[F] L} {x : L} :
    x ∈ algEquivEqualizer σ τ ↔ σ x = τ x := Iff.rfl

/-- **Two automorphisms agreeing on a generating set are equal.** -/
theorem algEquiv_ext_of_adjoin_eq_top {S : Set L}
    (hS : IntermediateField.adjoin F S = ⊤) {σ τ : L ≃ₐ[F] L}
    (h : ∀ x ∈ S, σ x = τ x) : σ = τ := by
  have hle : IntermediateField.adjoin F S ≤ algEquivEqualizer σ τ := by
    rw [IntermediateField.adjoin_le_iff]
    exact h
  rw [hS] at hle
  exact AlgEquiv.ext fun x => hle (IntermediateField.mem_top (x := x))

/-- **An automorphism fixing a generating set pointwise is the identity.** -/
theorem algEquiv_eq_refl_of_adjoin_eq_top {S : Set L}
    (hS : IntermediateField.adjoin F S = ⊤) {σ : L ≃ₐ[F] L}
    (h : ∀ x ∈ S, σ x = x) : σ = AlgEquiv.refl :=
  algEquiv_ext_of_adjoin_eq_top hS h

/-! ## Rigidity over a compositum -/

/-- **Two automorphisms agreeing on each of two intermediate fields whose compositum is everything
are equal.** -/
theorem algEquiv_ext_of_sup_eq_top {E M : IntermediateField F L} (hEM : E ⊔ M = ⊤)
    {σ τ : L ≃ₐ[F] L} (hE : ∀ x ∈ E, σ x = τ x) (hM : ∀ x ∈ M, σ x = τ x) : σ = τ := by
  have hle : E ⊔ M ≤ algEquivEqualizer σ τ := sup_le hE hM
  rw [hEM] at hle
  exact AlgEquiv.ext fun x => hle (IntermediateField.mem_top (x := x))

/-- **The restriction map to one factor of a compositum is injective on the automorphisms fixing
the other factor.**  This is the injectivity half of natural irrationalities. -/
theorem algEquiv_eq_refl_of_sup_eq_top {E M : IntermediateField F L} (hEM : E ⊔ M = ⊤)
    {σ : L ≃ₐ[F] L} (hE : ∀ x ∈ E, σ x = x) (hM : ∀ x ∈ M, σ x = x) :
    σ = AlgEquiv.refl :=
  algEquiv_ext_of_sup_eq_top hEM hE hM

end GaloisForLFunctions.HTGeometry
