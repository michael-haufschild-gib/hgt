/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality

/-!
# Hasse principle for linear-map solvability

A fixed inhomogeneous linear equation over a global field has a global solution exactly when its
scalar extension has a solution at every completion.  The local preimages need not agree; faithful
flat descent of membership in the global range recovers one global preimage.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- A fixed linear equation has a solution exactly when its scalar extension has a solution. -/
theorem linearMap_exists_preimage_iff_baseChange {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (y : N) :
    (∃ x, f x = y) ↔ ∃ z, f.baseChange L z = (1 : L) ⊗ₜ[K] y := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(1 : L) ⊗ₜ[K] x, ?_⟩
    rw [LinearMap.baseChange_tmul, hx]
  · rintro ⟨z, hz⟩
    have hlocal : (1 : L) ⊗ₜ[K] y ∈ (LinearMap.range f).baseChange L := by
      rw [linearMap_range_baseChange]
      exact ⟨z, hz⟩
    exact (submodule_mem_baseChange_iff (L := L) (LinearMap.range f) y).mpr hlocal

/-- A fixed linear equation over a number field has a solution exactly when its completed scalar
extension has a solution at every place. -/
theorem numberField_linearMap_exists_preimage_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (y : N) :
    (∃ x, f x = y) ↔ ∀ p : NumberFieldPlace K,
      ∃ z, f.baseChange (completion K p) z = (1 : completion K p) ⊗ₜ[K] y := by
  constructor
  · intro h p
    exact (linearMap_exists_preimage_iff_baseChange (L := completion K p) f y).mp h
  · intro h
    exact (linearMap_exists_preimage_iff_baseChange
      (L := completion K (witnessPlace K)) f y).mpr (h (witnessPlace K))

/-- A fixed linear equation over `F(t)` has a solution exactly when its completed scalar extension
has a solution at every finite and infinite place. -/
theorem rationalFunction_linearMap_exists_preimage_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (y : N) :
    (∃ x, f x = y) ↔ ∀ p : RationalFunctionPlace F,
      ∃ z, f.baseChange (rationalFunctionCompletion F p) z =
        (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] y := by
  constructor
  · intro h p
    exact (linearMap_exists_preimage_iff_baseChange (L := rationalFunctionCompletion F p) f y).mp h
  · intro h
    exact (linearMap_exists_preimage_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f y).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
