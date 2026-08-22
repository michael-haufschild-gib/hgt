/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseFiniteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Hasse detection of flat modules

Flatness is reflected by faithfully flat scalar extension.  Consequently a module over either
global-field model is flat exactly when all of its completed scalar extensions are flat.  This is
the module-theoretic local--global condition underlying the flatness clauses in smooth and étale
algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Flatness of a module is reflected by every field scalar extension. -/
theorem module_flat_iff_tensorProduct_flat
    {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] :
    Module.Flat K M ↔ Module.Flat L (L ⊗[K] M) := by
  constructor
  · intro h
    letI : Module.Flat K M := h
    infer_instance
  · intro h
    letI : Module.Flat L (L ⊗[K] M) := h
    exact Module.Flat.of_flat_tensorProduct K M L

/-- A module over a number field is flat exactly when all completed scalar extensions are flat. -/
theorem numberField_module_flat_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    Module.Flat K M ↔ ∀ p : NumberFieldPlace K,
      Module.Flat (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h p
    exact (module_flat_iff_tensorProduct_flat (L := completion K p)).mp h
  · intro h
    exact (module_flat_iff_tensorProduct_flat
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A module over `F(t)` is flat exactly when all finite and infinite completed scalar extensions
are flat. -/
theorem rationalFunction_module_flat_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    Module.Flat (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      Module.Flat (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h p
    exact (module_flat_iff_tensorProduct_flat
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (module_flat_iff_tensorProduct_flat
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- Flatness of a number-field module can be certified at one completion. -/
theorem numberField_module_flat_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    Module.Flat K M ↔ ∃ p : NumberFieldPlace K,
      Module.Flat (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (module_flat_iff_tensorProduct_flat (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_flat_iff_tensorProduct_flat (L := completion K p)).mpr hp

/-- Flatness of an `F(t)`-module can be certified at one completion. -/
theorem rationalFunction_module_flat_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    Module.Flat (RatFunc F) M ↔ ∃ p : RationalFunctionPlace F,
      Module.Flat (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (module_flat_iff_tensorProduct_flat
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_flat_iff_tensorProduct_flat
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
