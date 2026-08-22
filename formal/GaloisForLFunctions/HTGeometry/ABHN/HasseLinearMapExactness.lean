/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapSolvability

/-!
# Hasse detection for exact linear complexes

Faithfully flat scalar extension reflects exactness of two consecutive linear maps.  Thus a
global linear complex is exact at its middle term exactly when all of its completed scalar
extensions are exact there.  This packages the local--global test for vanishing of a linear
homology group without choosing bases or matrices.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x y

/-- Exactness of two consecutive linear maps is reflected by every field scalar extension. -/
theorem linearMap_exact_iff_baseChange_exact {K : Type u} {L : Type v}
    {M : Type w} {N : Type x} {P : Type y} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P) :
    Function.Exact f g ↔ Function.Exact (f.baseChange L) (g.baseChange L) := by
  simpa only [LinearMap.baseChange_eq_ltensor] using
    (Module.FaithfullyFlat.lTensor_exact_iff_exact K L f g).symm

/-- A linear complex over a number field is exact at its middle term exactly when all completed
scalar extensions are exact there. -/
theorem numberFieldLinearMap_exact_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P) :
    Function.Exact f g ↔ ∀ p : NumberFieldPlace K,
      Function.Exact (f.baseChange (completion K p)) (g.baseChange (completion K p)) := by
  constructor
  · intro h p
    exact (linearMap_exact_iff_baseChange_exact (L := completion K p) f g).mp h
  · intro h
    exact (linearMap_exact_iff_baseChange_exact
      (L := completion K (witnessPlace K)) f g).mpr (h (witnessPlace K))

/-- A linear complex over `F(t)` is exact at its middle term exactly when all finite and infinite
completed scalar extensions are exact there. -/
theorem rationalFunctionLinearMap_exact_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    [AddCommGroup P] [Module (RatFunc F) P] (f : M →ₗ[RatFunc F] N)
    (g : N →ₗ[RatFunc F] P) :
    Function.Exact f g ↔ ∀ p : RationalFunctionPlace F,
      Function.Exact (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (linearMap_exact_iff_baseChange_exact
      (L := rationalFunctionCompletion F p) f g).mp h
  · intro h
    exact (linearMap_exact_iff_baseChange_exact
      (L := rationalFunctionCompletion F .infinite) f g).mpr (h .infinite)

/-- Exactness of a number-field linear complex can be certified at one completion. -/
theorem numberFieldLinearMap_exact_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] (f : M →ₗ[K] N) (g : N →ₗ[K] P) :
    Function.Exact f g ↔ ∃ p : NumberFieldPlace K,
      Function.Exact (f.baseChange (completion K p)) (g.baseChange (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_exact_iff_baseChange_exact (L := completion K (witnessPlace K)) f g).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_exact_iff_baseChange_exact (L := completion K p) f g).mpr hp

/-- Exactness of an `F(t)`-linear complex can be certified at one completion. -/
theorem rationalFunctionLinearMap_exact_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x} {P : Type y}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    [AddCommGroup P] [Module (RatFunc F) P] (f : M →ₗ[RatFunc F] N)
    (g : N →ₗ[RatFunc F] P) :
    Function.Exact f g ↔ ∃ p : RationalFunctionPlace F,
      Function.Exact (f.baseChange (rationalFunctionCompletion F p))
        (g.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_exact_iff_baseChange_exact
        (L := rationalFunctionCompletion F .infinite) f g).mp h⟩
  · rintro ⟨p, hp⟩
    exact (linearMap_exact_iff_baseChange_exact
      (L := rationalFunctionCompletion F p) f g).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
