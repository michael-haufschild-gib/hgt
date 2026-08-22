/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleQuotients

/-!
# Hasse comparison of linear-map cokernels

The cokernel after field scalar extension is canonically the scalar extension of the global
cokernel.  Its finrank is the number of independent linear obstructions, so this invariant is
unchanged by every supported completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

open scoped TensorProduct

/-- The cokernel after field scalar extension is the scalar extension of the global cokernel. -/
noncomputable def linearMapCokernelBaseChangeEquiv {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) :
    ((L ⊗[K] N) ⧸ (LinearMap.range (f.baseChange L))) ≃ₗ[L]
      (L ⊗[K] (N ⧸ LinearMap.range f)) := by
  rw [← linearMap_range_baseChange]
  exact submoduleQuotientBaseChangeEquiv (L := L) (LinearMap.range f)

/-- Field scalar extension preserves the finrank of a linear-map cokernel. -/
theorem linearMap_cokernel_finrank_baseChange {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) :
    Module.finrank L ((L ⊗[K] N) ⧸ (LinearMap.range (f.baseChange L))) =
      Module.finrank K (N ⧸ LinearMap.range f) := by
  calc
    Module.finrank L ((L ⊗[K] N) ⧸ (LinearMap.range (f.baseChange L))) =
        Module.finrank L (L ⊗[K] (N ⧸ LinearMap.range f)) :=
      (linearMapCokernelBaseChangeEquiv (L := L) f).finrank_eq
    _ = Module.finrank K (N ⧸ LinearMap.range f) := Module.finrank_baseChange

/-- The cokernel of a number-field linear map has the same finrank at every completed place. -/
theorem numberField_linearMap_cokernel_finrank_completion (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) ((completion K p ⊗[K] N) ⧸
      (LinearMap.range (f.baseChange (completion K p)))) =
      Module.finrank K (N ⧸ LinearMap.range f) :=
  linearMap_cokernel_finrank_baseChange (L := completion K p) f

/-- The cokernel of an `F(t)`-linear map has the same finrank at every finite and infinite
completed place. -/
theorem rationalFunction_linearMap_cokernel_finrank_completion (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) ((rationalFunctionCompletion F p ⊗[RatFunc F] N) ⧸
      (LinearMap.range (f.baseChange (rationalFunctionCompletion F p)))) =
      Module.finrank (RatFunc F) (N ⧸ LinearMap.range f) :=
  linearMap_cokernel_finrank_baseChange (L := rationalFunctionCompletion F p) f

/-- A number-field linear map has cokernel finrank `n` exactly when its scalar extension at every
completed place has cokernel finrank `n`. -/
theorem numberField_linearMap_cokernel_finrank_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (N ⧸ LinearMap.range f) = n ↔ ∀ p : NumberFieldPlace K,
      Module.finrank (completion K p) ((completion K p ⊗[K] N) ⧸
        (LinearMap.range (f.baseChange (completion K p)))) = n := by
  constructor
  · intro h p
    rw [numberField_linearMap_cokernel_finrank_completion K f p, h]
  · intro h
    rw [← numberField_linearMap_cokernel_finrank_completion K f (witnessPlace K)]
    exact h (witnessPlace K)

/-- An `F(t)`-linear map has cokernel finrank `n` exactly when its scalar extension at every
finite and infinite completed place has cokernel finrank `n`. -/
theorem rationalFunction_linearMap_cokernel_finrank_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (N ⧸ LinearMap.range f) = n ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p)
        ((rationalFunctionCompletion F p ⊗[RatFunc F] N) ⧸
          (LinearMap.range (f.baseChange (rationalFunctionCompletion F p)))) = n := by
  constructor
  · intro h p
    rw [rationalFunction_linearMap_cokernel_finrank_completion F f p, h]
  · intro h
    rw [← rationalFunction_linearMap_cokernel_finrank_completion F f .infinite]
    exact h .infinite

/-- A prescribed cokernel dimension of a number-field linear map can be certified at one
completion. -/
theorem numberField_linearMap_cokernel_finrank_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (n : ℕ) :
    Module.finrank K (N ⧸ LinearMap.range f) = n ↔ ∃ p : NumberFieldPlace K,
      Module.finrank (completion K p) ((completion K p ⊗[K] N) ⧸
        (LinearMap.range (f.baseChange (completion K p)))) = n := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberField_linearMap_cokernel_finrank_completion K f (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberField_linearMap_cokernel_finrank_completion K f p).symm.trans hp

/-- A prescribed cokernel dimension of an `F(t)`-linear map can be certified at one completion. -/
theorem rationalFunction_linearMap_cokernel_finrank_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) (n : ℕ) :
    Module.finrank (RatFunc F) (N ⧸ LinearMap.range f) = n ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          ((rationalFunctionCompletion F p ⊗[RatFunc F] N) ⧸
            (LinearMap.range (f.baseChange (rationalFunctionCompletion F p)))) = n := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunction_linearMap_cokernel_finrank_completion F f .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunction_linearMap_cokernel_finrank_completion F f p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
