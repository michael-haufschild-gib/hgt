/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks
import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Hasse detection for simple vector spaces

A module over a field is simple precisely when it has finrank one.  Since field scalar extension
preserves finrank, simplicity of the underlying field module is detected at every completion.
This concerns plain vector spaces, not irreducibility for an additional algebra action.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- A vector space is simple exactly when any field scalar extension is simple. -/
theorem isSimpleModule_iff_tensorProduct_isSimpleModule {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    IsSimpleModule K M ↔ IsSimpleModule L (L ⊗[K] M) := by
  rw [isSimpleModule_iff_finrank_eq_one, isSimpleModule_iff_finrank_eq_one,
    module_finrank_tensorProduct]

/-- A vector space over a number field is simple exactly when every completed scalar extension is
simple. -/
theorem numberField_isSimpleModule_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    IsSimpleModule K M ↔ ∀ p : NumberFieldPlace K,
      IsSimpleModule (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h p
    exact (isSimpleModule_iff_tensorProduct_isSimpleModule (L := completion K p)).mp h
  · intro h
    exact (isSimpleModule_iff_tensorProduct_isSimpleModule
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A vector space over `F(t)` is simple exactly when every finite and infinite completed scalar
extension is simple. -/
theorem rationalFunction_isSimpleModule_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    IsSimpleModule (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      IsSimpleModule (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h p
    exact (isSimpleModule_iff_tensorProduct_isSimpleModule
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (isSimpleModule_iff_tensorProduct_isSimpleModule
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
