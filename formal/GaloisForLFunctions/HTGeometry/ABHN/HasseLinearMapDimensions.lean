/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRanks
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRanges

/-!
# Hasse comparison of kernel and image dimensions

Scalar extension carries kernels and ranges to their corresponding local submodules.  Their
finranks are consequently completion-invariant, giving local tests for the nullity and image
dimension of a fixed linear map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

open scoped TensorProduct

/-- Field scalar extension preserves the finrank of a linear-map kernel. -/
theorem linearMap_ker_finrank_baseChange {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) :
    Module.finrank L (LinearMap.ker (f.baseChange L)) = Module.finrank K (LinearMap.ker f) := by
  rw [← linearMap_ker_baseChange]
  exact submodule_finrank_baseChange (L := L) (LinearMap.ker f)

/-- Field scalar extension preserves the finrank of a linear-map range. -/
theorem linearMap_range_finrank_baseChange {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) :
    Module.finrank L (LinearMap.range (f.baseChange L)) = Module.finrank K (LinearMap.range f) := by
  rw [← linearMap_range_baseChange]
  exact submodule_finrank_baseChange (L := L) (LinearMap.range f)

/-- A number-field linear map has the same kernel finrank at every completed place. -/
theorem numberField_linearMap_ker_finrank_completion (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker (f.baseChange (completion K p))) =
      Module.finrank K (LinearMap.ker f) :=
  linearMap_ker_finrank_baseChange (L := completion K p) f

/-- A number-field linear map has the same range finrank at every completed place. -/
theorem numberField_linearMap_range_finrank_completion (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.range (f.baseChange (completion K p))) =
      Module.finrank K (LinearMap.range f) :=
  linearMap_range_finrank_baseChange (L := completion K p) f

/-- An `F(t)`-linear map has the same kernel finrank at every finite and infinite completed
place. -/
theorem rationalFunction_linearMap_ker_finrank_completion (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      (LinearMap.ker (f.baseChange (rationalFunctionCompletion F p))) =
      Module.finrank (RatFunc F) (LinearMap.ker f) :=
  linearMap_ker_finrank_baseChange (L := rationalFunctionCompletion F p) f

/-- An `F(t)`-linear map has the same range finrank at every finite and infinite completed
place. -/
theorem rationalFunction_linearMap_range_finrank_completion (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      (LinearMap.range (f.baseChange (rationalFunctionCompletion F p))) =
      Module.finrank (RatFunc F) (LinearMap.range f) :=
  linearMap_range_finrank_baseChange (L := rationalFunctionCompletion F p) f

/-- A number-field linear map has kernel finrank `n` exactly when all completed scalar extensions
have kernel finrank `n`. -/
theorem numberField_linearMap_ker_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.ker f) = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.ker (f.baseChange (completion K p))) = n := by
  constructor
  · intro h p
    rw [numberField_linearMap_ker_finrank_completion K f p, h]
  · intro h
    rw [← numberField_linearMap_ker_finrank_completion K f (witnessPlace K)]
    exact h (witnessPlace K)

/-- A number-field linear map has range finrank `n` exactly when all completed scalar extensions
have range finrank `n`. -/
theorem numberField_linearMap_range_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.range f) = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.range (f.baseChange (completion K p))) = n := by
  constructor
  · intro h p
    rw [numberField_linearMap_range_finrank_completion K f p, h]
  · intro h
    rw [← numberField_linearMap_range_finrank_completion K f (witnessPlace K)]
    exact h (witnessPlace K)

/-- An `F(t)`-linear map has kernel finrank `n` exactly when all finite and infinite completed
scalar extensions have kernel finrank `n`. -/
theorem rationalFunction_linearMap_ker_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker f) = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (LinearMap.ker (f.baseChange (rationalFunctionCompletion F p))) = n := by
  constructor
  · intro h p
    rw [rationalFunction_linearMap_ker_finrank_completion F f p, h]
  · intro h
    rw [← rationalFunction_linearMap_ker_finrank_completion F f .infinite]
    exact h .infinite

/-- An `F(t)`-linear map has range finrank `n` exactly when all finite and infinite completed
scalar extensions have range finrank `n`. -/
theorem rationalFunction_linearMap_range_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.range f) = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (LinearMap.range (f.baseChange (rationalFunctionCompletion F p))) = n := by
  constructor
  · intro h p
    rw [rationalFunction_linearMap_range_finrank_completion F f p, h]
  · intro h
    rw [← rationalFunction_linearMap_range_finrank_completion F f .infinite]
    exact h .infinite

/-- A prescribed kernel dimension of a number-field linear map can be certified at one
completion. -/
theorem numberField_linearMap_ker_finrank_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.ker f) = n ↔ ∃ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.ker (f.baseChange (completion K p))) = n := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberField_linearMap_ker_finrank_completion K f (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberField_linearMap_ker_finrank_completion K f p).symm.trans hp

/-- A prescribed range dimension of a number-field linear map can be certified at one
completion. -/
theorem numberField_linearMap_range_finrank_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (LinearMap.range f) = n ↔ ∃ p : NumberFieldPlace K,
      Module.finrank (completion K p) (LinearMap.range (f.baseChange (completion K p))) = n := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberField_linearMap_range_finrank_completion K f (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberField_linearMap_range_finrank_completion K f p).symm.trans hp

/-- A prescribed kernel dimension of an `F(t)`-linear map can be certified at one completion. -/
theorem rationalFunction_linearMap_ker_finrank_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker f) = n ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (LinearMap.ker (f.baseChange (rationalFunctionCompletion F p))) = n := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunction_linearMap_ker_finrank_completion F f .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunction_linearMap_ker_finrank_completion F f p).symm.trans hp

/-- A prescribed range dimension of an `F(t)`-linear map can be certified at one completion. -/
theorem rationalFunction_linearMap_range_finrank_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.range f) = n ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        (LinearMap.range (f.baseChange (rationalFunctionCompletion F p))) = n := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunction_linearMap_range_finrank_completion F f .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunction_linearMap_range_finrank_completion F f p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
