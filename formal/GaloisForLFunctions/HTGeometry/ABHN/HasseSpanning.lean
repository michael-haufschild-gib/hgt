/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapBaseChange

/-!
# Hasse detection of spanning families

Scalar extension reflects whether an arbitrary global family spans a vector space.  This yields
completion-wise Hasse tests for systems of linear generators, including the spanning half of a
basis, without requiring finiteness of the index type.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- A family spans after a field scalar extension exactly when it spans before scalar extension. -/
theorem span_range_eq_top_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    {ι : Type x} (v : ι → M) :
    Submodule.span K (Set.range v) = ⊤ ↔
      Submodule.span L (Set.range fun i ↦ (1 : L) ⊗ₜ[K] v i) = ⊤ := by
  have himage : (TensorProduct.mk K L M 1) '' Set.range v =
      Set.range fun i ↦ (1 : L) ⊗ₜ[K] v i := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩, rfl⟩
  constructor
  · intro h
    rw [← Submodule.baseChange_top (R := K) (M := M) (A := L), ← h,
      Submodule.baseChange_span, himage]
  · intro h
    apply Submodule.baseChange_injective (A := L)
    rw [Submodule.baseChange_span, himage, h, Submodule.baseChange_top]

/-- A family over a number field spans exactly when its scalar extensions span at every completed
place. -/
theorem numberField_span_range_eq_top_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    {ι : Type x} (v : ι → M) :
    Submodule.span K (Set.range v) = ⊤ ↔ ∀ p : NumberFieldPlace K,
      Submodule.span (completion K p)
        (Set.range fun i ↦ (1 : completion K p) ⊗ₜ[K] v i) = ⊤ := by
  constructor
  · intro h p
    exact (span_range_eq_top_iff_baseChange (L := completion K p) v).mp h
  · intro h
    exact (span_range_eq_top_iff_baseChange (L := completion K (witnessPlace K)) v).mpr
      (h (witnessPlace K))

/-- A family over `F(t)` spans exactly when its scalar extensions span at every finite and
infinite completion. -/
theorem rationalFunction_span_range_eq_top_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    {ι : Type x} (v : ι → M) :
    Submodule.span (RatFunc F) (Set.range v) = ⊤ ↔ ∀ p : RationalFunctionPlace F,
      Submodule.span (rationalFunctionCompletion F p)
        (Set.range fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] v i) = ⊤ := by
  constructor
  · intro h p
    exact (span_range_eq_top_iff_baseChange (L := rationalFunctionCompletion F p) v).mp h
  · intro h
    exact (span_range_eq_top_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) v).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
