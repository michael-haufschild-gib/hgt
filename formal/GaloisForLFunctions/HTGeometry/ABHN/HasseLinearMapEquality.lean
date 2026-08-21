/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSubmoduleRelations

/-!
# Hasse detection of linear-map equality

Equality of fixed global linear maps is reflected by scalar extension.  Thus completed local
operator identities jointly certify the corresponding global identity for arbitrary linear maps.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- Two linear maps are equal exactly when their scalar extensions are equal. -/
theorem linearMap_eq_iff_baseChange_eq {K : Type u} {L : Type v} {M : Type w} {N : Type x}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f g : M →ₗ[K] N) :
    f = g ↔ f.baseChange L = g.baseChange L := by
  constructor
  · intro h
    exact congrArg (LinearMap.baseChange L) h
  · intro h
    ext m
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) N
    have happly := LinearMap.congr_fun h ((1 : L) ⊗ₜ[K] m)
    change (1 : L) ⊗ₜ[K] f m = 1 ⊗ₜ[K] g m at happly
    exact happly

/-- Two linear maps over a number field are equal exactly when all of their completed base
changes are equal. -/
theorem numberField_linearMap_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f g : M →ₗ[K] N) :
    f = g ↔ ∀ p : NumberFieldPlace K,
      f.baseChange (completion K p) = g.baseChange (completion K p) := by
  constructor
  · intro h p
    exact (linearMap_eq_iff_baseChange_eq (L := completion K p) f g).mp h
  · intro h
    exact (linearMap_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) f g).mpr (h (witnessPlace K))

/-- Two linear maps over `F(t)` are equal exactly when all of their finite and infinite completed
base changes are equal. -/
theorem rationalFunction_linearMap_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module (RatFunc F) M] [AddCommGroup N] [Module (RatFunc F) N]
    (f g : M →ₗ[RatFunc F] N) :
    f = g ↔ ∀ p : RationalFunctionPlace F,
      f.baseChange (rationalFunctionCompletion F p) =
        g.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (linearMap_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) f g).mp h
  · intro h
    exact (linearMap_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) f g).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
