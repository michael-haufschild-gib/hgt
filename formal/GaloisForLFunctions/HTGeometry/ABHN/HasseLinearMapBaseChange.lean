/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleMembership

/-!
# Hasse detection for linear maps

Scalar extension of vector spaces over global fields reflects the range, injectivity, surjectivity,
and bijectivity of a fixed linear map.  This gives completion-wise Hasse tests for arbitrary
linear transformations, including nonsquare maps and maps between modules not arising from a
matrix presentation.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- Scalar extension commutes with the range of a linear map. -/
theorem linearMap_range_baseChange {K : Type u} {L : Type v} {M : Type w} {N : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    (LinearMap.range f).baseChange L = LinearMap.range (f.baseChange L) := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      rw [map_add]
      exact (LinearMap.range (f.baseChange L)).add_mem hx hy
    | tmul l x =>
      rw [LinearMap.baseChange_tmul]
      obtain ⟨m, hm⟩ := x.property
      refine ⟨l ⊗ₜ[K] m, ?_⟩
      rw [LinearMap.baseChange_tmul, hm]
      rfl
  · rintro y ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => exact (LinearMap.range f).baseChange L |>.zero_mem
    | add x y hx hy =>
      rw [map_add]
      exact (LinearMap.range f).baseChange L |>.add_mem hx hy
    | tmul l m =>
      rw [LinearMap.baseChange_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem l ⟨m, rfl⟩

/-- Surjectivity of a linear map is reflected by every field scalar extension. -/
theorem linearMap_surjective_iff_baseChange_surjective {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Surjective f ↔ Function.Surjective (f.baseChange L) := by
  constructor
  · exact LinearMap.baseChange_surjective L
  · intro h
    apply LinearMap.range_eq_top.mp
    apply (Submodule.baseChange_injective (A := L))
    rw [linearMap_range_baseChange, LinearMap.range_eq_top.mpr h, Submodule.baseChange_top]

/-- Injectivity of a linear map is reflected by every field scalar extension. -/
theorem linearMap_injective_iff_baseChange_injective {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Injective f ↔ Function.Injective (f.baseChange L) := by
  constructor
  · intro h
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap f h
  · intro h x y hxy
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
    apply h
    change (1 : L) ⊗ₜ[K] f x = 1 ⊗ₜ[K] f y
    exact congrArg (fun z => (1 : L) ⊗ₜ[K] z) hxy

/-- Bijectivity of a linear map is reflected by every field scalar extension. -/
theorem linearMap_bijective_iff_baseChange_bijective {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Bijective f ↔ Function.Bijective (f.baseChange L) := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    exact ⟨(linearMap_injective_iff_baseChange_injective (L := L) f).mp hinj,
      (linearMap_surjective_iff_baseChange_surjective (L := L) f).mp hsurj⟩
  · rintro ⟨hinj, hsurj⟩
    exact ⟨(linearMap_injective_iff_baseChange_injective (L := L) f).mpr hinj,
      (linearMap_surjective_iff_baseChange_surjective (L := L) f).mpr hsurj⟩

/-- A linear map over a number field is injective exactly when every completed base change is
injective. -/
theorem numberFieldLinearMap_injective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Injective f ↔ ∀ p : NumberFieldPlace K,
      Function.Injective (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_injective_iff_baseChange_injective (L := completion K p) f).mp h
  · intro h
    exact (linearMap_injective_iff_baseChange_injective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- A linear map over a number field is surjective exactly when every completed base change is
surjective. -/
theorem numberFieldLinearMap_surjective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Surjective f ↔ ∀ p : NumberFieldPlace K,
      Function.Surjective (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_surjective_iff_baseChange_surjective (L := completion K p) f).mp h
  · intro h
    exact (linearMap_surjective_iff_baseChange_surjective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- A linear map over a number field is bijective exactly when every completed base change is
bijective. -/
theorem numberFieldLinearMap_bijective_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    Function.Bijective f ↔ ∀ p : NumberFieldPlace K,
      Function.Bijective (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_bijective_iff_baseChange_bijective (L := completion K p) f).mp h
  · intro h
    exact (linearMap_bijective_iff_baseChange_bijective
      (L := completion K (witnessPlace K)) f).mpr (h (witnessPlace K))

/-- A linear map over `F(t)` is injective exactly when every finite and infinite completed base
change is injective. -/
theorem rationalFunctionLinearMap_injective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    Function.Injective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Injective (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_injective_iff_baseChange_injective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_injective_iff_baseChange_injective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- A linear map over `F(t)` is surjective exactly when every finite and infinite completed base
change is surjective. -/
theorem rationalFunctionLinearMap_surjective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    Function.Surjective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Surjective (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_surjective_iff_baseChange_surjective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_surjective_iff_baseChange_surjective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

/-- A linear map over `F(t)` is bijective exactly when every finite and infinite completed base
change is bijective. -/
theorem rationalFunctionLinearMap_bijective_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f : M →ₗ[RatFunc F] N) :
    Function.Bijective f ↔ ∀ p : RationalFunctionPlace F,
      Function.Bijective (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_bijective_iff_baseChange_bijective
      (L := rationalFunctionCompletion F p) f).mp h
  · intro h
    exact (linearMap_bijective_iff_baseChange_bijective
      (L := rationalFunctionCompletion F .infinite) f).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
