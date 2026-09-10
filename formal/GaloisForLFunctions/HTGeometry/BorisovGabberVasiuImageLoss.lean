import GaloisForLFunctions.HTGeometry.StableDifferentialCore
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Image

open Function Set
namespace GaloisForLFunctions.HTGeometry

/-- The loss at any depth descends from an initially missing point (Lemma 3.2(4)). -/
theorem bgv_iterate_loss_subset {α : Type*} (f : α → α) (n : ℕ) :
    range f^[n] \ range f^[n + 1] ⊆ f^[n] '' (range f)ᶜ := by
  rintro z ⟨⟨x, rfl⟩, hx⟩
  refine ⟨x, ?_, rfl⟩
  rintro ⟨y, rfl⟩
  exact hx ⟨y, Function.iterate_succ_apply f n y⟩

/-- Injectivity prevents any loss from merging with a surviving image. -/
theorem bgv_embedding_iterate_loss {α : Type*} (f : α ↪ α) (n : ℕ) :
    range (f : α → α)^[n] \ range (f : α → α)^[n + 1] =
      (f : α → α)^[n] '' (range f)ᶜ := by
  apply Set.Subset.antisymm (bgv_iterate_loss_subset f n)
  rintro z ⟨x, hx, rfl⟩
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro ⟨y, hy⟩
  rw [Function.iterate_succ_apply] at hy
  exact hx ⟨y, (f.injective.iterate n) hy⟩

/-- An injective endomorphism stabilizes at a finite stage exactly when it is onto already. -/
theorem bgv_embedding_range_stabilizes_iff {α : Type*} (f : α ↪ α) (n : ℕ) :
    range (f : α → α)^[n] = range (f : α → α)^[n + 1] ↔ Surjective f := by
  constructor
  · intro h x
    have hx : (f : α → α)^[n] x ∈ range (f : α → α)^[n + 1] := h ▸ mem_range_self x
    obtain ⟨y, hy⟩ := hx
    rw [Function.iterate_succ_apply] at hy
    exact ⟨y, (f.injective.iterate n) hy⟩
  · intro h
    rw [(h.iterate n).range_eq, (h.iterate (n + 1)).range_eq]

/-- Finite-stage stabilization of field pullback images is exactly surjectivity. -/
theorem bgv_field_range_stabilizes_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (φ : F →ₐ[K] F) (n : ℕ) :
    range (φ ^ n : F →ₐ[K] F) = range (φ ^ (n + 1) : F →ₐ[K] F) ↔ Surjective φ := by
  simp only [AlgHom.coe_pow]
  exact bgv_embedding_range_stabilizes_iff (⟨φ, φ.injective⟩ : F ↪ F) n

/-- The stable core reaches any finite image field exactly when the whole map is onto. -/
theorem bgv_stableRangeCore_finite_stage_iff
    {K F : Type*} [Field K] [Field F] [Algebra K F] (φ : F →ₐ[K] F) (n : ℕ) :
    (stableRangeCore φ : Set F) = range (φ ^ n : F →ₐ[K] F) ↔ Surjective φ := by
  constructor
  · intro h
    apply (bgv_field_range_stabilizes_iff φ n).mp
    apply Set.Subset.antisymm
    · intro x hx
      have hxcore : x ∈ stableRangeCore φ := by
        change x ∈ (stableRangeCore φ : Set F)
        rw [h]
        exact hx
      exact (mem_stableRangeCore_iff φ x).mp hxcore (n + 1)
    · rintro x ⟨y, rfl⟩
      refine ⟨φ y, ?_⟩
      simp only [AlgHom.coe_pow, Function.iterate_succ_apply]
  · intro h
    ext x
    constructor
    · intro _
      change ∃ y, (φ ^ n) y = x
      simpa only [AlgHom.coe_pow] using (h.iterate n) x
    · intro _
      apply (mem_stableRangeCore_iff φ x).mpr
      intro m
      simpa only [AlgHom.coe_pow] using (h.iterate m) x

end GaloisForLFunctions.HTGeometry
