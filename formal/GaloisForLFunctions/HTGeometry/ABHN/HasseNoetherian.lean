/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness

/-!
# Hasse detection for Noetherian modules

Faithfully flat field scalar extension both preserves and reflects the ascending-chain condition
on submodules.  Consequently, one completion detects this module property, while the stated Hasse
forms quantify over every completed place.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- A module is Noetherian exactly when any field scalar extension is Noetherian. -/
theorem module_isNoetherian_iff_tensorProduct_isNoetherian {K : Type u} {L : Type v}
    {M : Type w} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    IsNoetherian K M ↔ IsNoetherian L (L ⊗[K] M) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat h

/-- A module over a number field is Noetherian exactly when its scalar extension at every place
is Noetherian. -/
theorem numberField_module_isNoetherian_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    IsNoetherian K M ↔ ∀ p : NumberFieldPlace K,
      IsNoetherian (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h p
    exact (module_isNoetherian_iff_tensorProduct_isNoetherian (L := completion K p)).mp h
  · intro h
    exact (module_isNoetherian_iff_tensorProduct_isNoetherian
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A module over `F(t)` is Noetherian exactly when its scalar extension at every finite and
infinite place is Noetherian. -/
theorem rationalFunction_module_isNoetherian_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    IsNoetherian (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      IsNoetherian (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h p
    exact (module_isNoetherian_iff_tensorProduct_isNoetherian
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (module_isNoetherian_iff_tensorProduct_isNoetherian
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
