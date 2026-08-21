/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapRanges

/-!
# Hasse detection for equalizers of linear maps

Scalar extension commutes with the common-solution submodule of two linear maps.  Faithful
flatness then detects whether a proposed global submodule is their equalizer from all completed
scalar extensions.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w x

/-- Scalar extension commutes with the equalizer of two linear maps over fields. -/
theorem linearMap_eqLocus_baseChange {K : Type u} {L : Type v} {M : Type w} {N : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f g : M →ₗ[K] N) :
    (LinearMap.eqLocus f g).baseChange L =
      LinearMap.eqLocus (f.baseChange L) (g.baseChange L) := by
  rw [LinearMap.eqLocus_eq_ker_sub, LinearMap.eqLocus_eq_ker_sub,
    ← LinearMap.baseChange_sub]
  exact linearMap_ker_baseChange (f - g)

/-- A submodule over a number field is the equalizer of two linear maps exactly when its completed
scalar extension is the corresponding local equalizer at every place. -/
theorem numberField_submodule_eq_eqLocus_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (S : Submodule K M) (f g : M →ₗ[K] N) :
    S = LinearMap.eqLocus f g ↔ ∀ p : NumberFieldPlace K,
      S.baseChange (completion K p) =
        LinearMap.eqLocus (f.baseChange (completion K p)) (g.baseChange (completion K p)) := by
  constructor
  · intro h p
    rw [h, linearMap_eqLocus_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := completion K (witnessPlace K))
    rw [linearMap_eqLocus_baseChange]
    exact h (witnessPlace K)

/-- A submodule over `F(t)` is the equalizer of two linear maps exactly when its finite and
infinite completed scalar extensions are the corresponding local equalizers. -/
theorem rationalFunction_submodule_eq_eqLocus_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} {N : Type x}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (S : Submodule (RatFunc F) M) (f g : M →ₗ[RatFunc F] N) :
    S = LinearMap.eqLocus f g ↔ ∀ p : RationalFunctionPlace F,
      S.baseChange (rationalFunctionCompletion F p) =
        LinearMap.eqLocus (f.baseChange (rationalFunctionCompletion F p))
          (g.baseChange (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    rw [h, linearMap_eqLocus_baseChange]
  · intro h
    apply Submodule.baseChange_injective (A := rationalFunctionCompletion F .infinite)
    rw [linearMap_eqLocus_baseChange]
    exact h .infinite

end GaloisForLFunctions.HTGeometry.ABHN
