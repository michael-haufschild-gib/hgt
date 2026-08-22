/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality

/-!
# Hasse detection for nilpotent linear endomorphisms

Scalar extension preserves every power of a linear endomorphism, and faithful flatness reflects
its vanishing.  Nilpotence is therefore detected at all completions of a global field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Nilpotence of a linear endomorphism is reflected by every field scalar extension. -/
theorem linearMap_isNilpotent_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    IsNilpotent f ↔ IsNilpotent (f.baseChange L) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← LinearMap.baseChange_pow, hn, LinearMap.baseChange_zero]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply (linearMap_eq_iff_baseChange_eq (L := L) (f ^ n) 0).mpr
    rw [LinearMap.baseChange_pow, hn, LinearMap.baseChange_zero]

/-- A linear endomorphism over a number field is nilpotent exactly when every completed scalar
extension is nilpotent. -/
theorem numberField_linearMap_isNilpotent_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    IsNilpotent f ↔ ∀ p : NumberFieldPlace K, IsNilpotent (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_isNilpotent_iff_baseChange (L := completion K p) f).mp h
  · intro h
    exact (linearMap_isNilpotent_iff_baseChange
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- A linear endomorphism over `F(t)` is nilpotent exactly when every finite and infinite
completed scalar extension is nilpotent. -/
theorem rationalFunction_linearMap_isNilpotent_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    IsNilpotent f ↔ ∀ p : RationalFunctionPlace F,
      IsNilpotent (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_isNilpotent_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_isNilpotent_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- Nilpotence of a number-field endomorphism can be certified at one completion. -/
theorem numberField_linearMap_isNilpotent_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (f : M →ₗ[K] M) :
    IsNilpotent f ↔ ∃ p : NumberFieldPlace K, IsNilpotent (f.baseChange (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_isNilpotent_iff_baseChange (L := completion K (witnessPlace K)) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_isNilpotent_iff_baseChange (L := completion K p) f).mpr hp

/-- Nilpotence of an `F(t)`-endomorphism can be certified at one completion. -/
theorem rationalFunction_linearMap_isNilpotent_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (f : M →ₗ[RatFunc F] M) :
    IsNilpotent f ↔ ∃ p : RationalFunctionPlace F,
      IsNilpotent (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_isNilpotent_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_isNilpotent_iff_baseChange
      (L := rationalFunctionCompletion F p) f).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
