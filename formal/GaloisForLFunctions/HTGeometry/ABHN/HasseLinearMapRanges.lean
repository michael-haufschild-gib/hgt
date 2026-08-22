/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapKernels

/-!
# Hasse detection for ranges of linear maps

Faithful flatness gives a completion-wise Hasse test for whether a specified global submodule is
the image of a linear map.  Alongside kernel detection, this verifies both generator and relation
submodules of a linear presentation locally.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- A submodule over a number field is the range of a linear map exactly when its completed scalar
extension is the corresponding local range at every place. -/
theorem numberField_submodule_eq_range_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (T : Submodule K N) (f : M →ₗ[K] N) :
    T = LinearMap.range f ↔ ∀ p : NumberFieldPlace K,
      T.baseChange (completion K p) = LinearMap.range (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    rw [h, linearMap_range_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := completion K (witnessPlace K))
    rw [linearMap_range_baseChange]
    exact h (witnessPlace K)

/-- A submodule over `F(t)` is the range of a linear map exactly when its finite and infinite
completed scalar extensions are the corresponding local ranges. -/
theorem rationalFunction_submodule_eq_range_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (T : Submodule (RatFunc F) N) (f : M →ₗ[RatFunc F] N) :
    T = LinearMap.range f ↔ ∀ p : RationalFunctionPlace F,
      T.baseChange (rationalFunctionCompletion F p) =
        LinearMap.range (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    rw [h, linearMap_range_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := rationalFunctionCompletion F .infinite)
    rw [linearMap_range_baseChange]
    exact h .infinite

/-- A number-field submodule is a given range exactly when this holds at one completion. -/
theorem numberField_submodule_eq_range_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (T : Submodule K N) (f : M →ₗ[K] N) :
    T = LinearMap.range f ↔ ∃ p : NumberFieldPlace K,
      T.baseChange (completion K p) = LinearMap.range (f.baseChange (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K, by rw [h, linearMap_range_baseChange]⟩
  · rintro ⟨p, hp⟩
    apply Submodule.baseChange_injective (A := completion K p)
    rw [linearMap_range_baseChange]
    exact hp

/-- An `F(t)`-submodule is a given range exactly when this holds at one completion. -/
theorem rationalFunction_submodule_eq_range_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (T : Submodule (RatFunc F) N) (f : M →ₗ[RatFunc F] N) :
    T = LinearMap.range f ↔ ∃ p : RationalFunctionPlace F,
      T.baseChange (rationalFunctionCompletion F p) =
        LinearMap.range (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite, by rw [h, linearMap_range_baseChange]⟩
  · rintro ⟨p, hp⟩
    apply Submodule.baseChange_injective (A := rationalFunctionCompletion F p)
    rw [linearMap_range_baseChange]
    exact hp

end GaloisForLFunctions.HTGeometry.ABHN
