/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapExactness

/-!
# Hasse detection for kernels of linear maps

Flat scalar extension carries the kernel of a linear map to the kernel of its scalar extension.
Faithful flatness therefore gives a completion-wise Hasse test for whether a specified global
submodule is precisely the relation module of a linear map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- Scalar extension commutes with the kernel of a linear map over fields. -/
theorem linearMap_ker_baseChange {K : Type u} {L : Type v} {M : Type w} {N : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    (LinearMap.ker f).baseChange L = LinearMap.ker (f.baseChange L) := by
  calc
    (LinearMap.ker f).baseChange L =
        (LinearMap.range (LinearMap.ker f).subtype).baseChange L := by
      rw [Submodule.range_subtype]
    _ = LinearMap.range ((LinearMap.ker f).subtype.baseChange L) :=
      linearMap_range_baseChange (LinearMap.ker f).subtype
    _ = LinearMap.ker (f.baseChange L) :=
      (LinearMap.exact_iff.mp
        ((linearMap_exact_iff_baseChange_exact (L := L) (LinearMap.ker f).subtype f).mp
          (LinearMap.exact_subtype_ker_map f))).symm

/-- A submodule over a number field is the kernel of a linear map exactly when its completed
scalar extension is the corresponding local kernel at every place. -/
theorem numberField_submodule_eq_ker_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (S : Submodule K M) (f : M →ₗ[K] N) :
    S = LinearMap.ker f ↔ ∀ p : NumberFieldPlace K,
      S.baseChange (completion K p) = LinearMap.ker (f.baseChange (completion K p)) := by
  constructor
  · intro h p
    rw [h, linearMap_ker_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := completion K (witnessPlace K))
    rw [h (witnessPlace K), linearMap_ker_baseChange]

/-- A submodule over `F(t)` is the kernel of a linear map exactly when its finite and infinite
completed scalar extensions are the corresponding local kernels. -/
theorem rationalFunction_submodule_eq_ker_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (S : Submodule (RatFunc F) M) (f : M →ₗ[RatFunc F] N) :
    S = LinearMap.ker f ↔ ∀ p : RationalFunctionPlace F,
      S.baseChange (rationalFunctionCompletion F p) =
        LinearMap.ker (f.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    rw [h, linearMap_ker_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := rationalFunctionCompletion F .infinite)
    rw [h .infinite, linearMap_ker_baseChange]

end GaloisForLFunctions.HTGeometry.ABHN
