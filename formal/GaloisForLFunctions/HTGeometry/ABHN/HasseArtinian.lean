/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseNoetherian
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Hasse detection for Artinian modules

Over a field, the ascending and descending chain conditions on submodules are equivalent.
Combining this with Noetherian descent makes the descending-chain condition detectable after
field scalar extension and hence after every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- A module over a field is Artinian exactly when any field scalar extension is Artinian. -/
theorem module_isArtinian_iff_tensorProduct_isArtinian {K : Type u} {L : Type v}
    {M : Type w} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    IsArtinian K M ↔ IsArtinian L (L ⊗[K] M) := by
  constructor
  · intro h
    apply (IsSemiprimaryRing.isNoetherian_iff_isArtinian (R := L) (M := L ⊗[K] M)).mp
    apply (module_isNoetherian_iff_tensorProduct_isNoetherian (L := L)).mp
    exact (IsSemiprimaryRing.isNoetherian_iff_isArtinian (R := K) (M := M)).mpr h
  · intro h
    exact Submodule.IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat h

/-- A module over a number field is Artinian exactly when its scalar extension at every place
is Artinian. -/
theorem numberField_module_isArtinian_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    IsArtinian K M ↔ ∀ p : NumberFieldPlace K,
      IsArtinian (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h p
    exact (module_isArtinian_iff_tensorProduct_isArtinian (L := completion K p)).mp h
  · intro h
    exact (module_isArtinian_iff_tensorProduct_isArtinian
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A module over `F(t)` is Artinian exactly when its scalar extension at every finite and
infinite place is Artinian. -/
theorem rationalFunction_module_isArtinian_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    IsArtinian (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      IsArtinian (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h p
    exact (module_isArtinian_iff_tensorProduct_isArtinian
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (module_isArtinian_iff_tensorProduct_isArtinian
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- The Artinian property of a number-field module can be certified at one completion. -/
theorem numberField_module_isArtinian_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    IsArtinian K M ↔ ∃ p : NumberFieldPlace K,
      IsArtinian (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (module_isArtinian_iff_tensorProduct_isArtinian
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_isArtinian_iff_tensorProduct_isArtinian (L := completion K p)).mpr hp

/-- The Artinian property of an `F(t)`-module can be certified at one completion. -/
theorem rationalFunction_module_isArtinian_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    IsArtinian (RatFunc F) M ↔ ∃ p : RationalFunctionPlace F,
      IsArtinian (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (module_isArtinian_iff_tensorProduct_isArtinian
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_isArtinian_iff_tensorProduct_isArtinian
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
