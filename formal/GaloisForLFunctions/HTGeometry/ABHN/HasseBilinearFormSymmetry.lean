/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealQuotients
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Hasse detection of symmetry for bilinear forms

A bilinear form is symmetric exactly when any field scalar extension is symmetric. The reverse
direction is obtained by testing the extended form on tensors with scalar coefficient one.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Symmetry of a bilinear form is reflected by field scalar extension. -/
theorem bilinForm_isSymm_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) :
    B.IsSymm ↔ (B.baseChange L).IsSymm := by
  constructor
  · intro h
    exact LinearMap.BilinForm.isSymm_iff.mpr
      (LinearMap.BilinForm.IsSymm.baseChange L (LinearMap.BilinForm.isSymm_iff.mp h))
  · intro h
    refine ⟨?_⟩
    intro x y
    apply FaithfulSMul.algebraMap_injective K L
    simpa [Algebra.smul_def] using h.eq (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y)

/-- A specified bilinear pairing vanishes exactly when the pairing of its pure-tensor images
vanishes after field scalar extension. -/
theorem bilinForm_apply_eq_zero_iff_baseChange_tmul
    {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L]
    [AddCommGroup M] [Module K M] (B : LinearMap.BilinForm K M) (x y : M) :
    B x y = 0 ↔ B.baseChange L (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) = 0 := by
  constructor
  · intro h
    simp [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, h]
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    simpa [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def] using h

/-- A prescribed bilinear orthogonality equation over a number field holds exactly when its
pure-tensor images are orthogonal at every completed place. -/
theorem numberField_bilinForm_apply_eq_zero_iff_forall_place
    (K : Type u) [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (x y : M) : B x y = 0 ↔
      ∀ p : NumberFieldPlace K,
        B.baseChange (completion K p) (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) = 0 := by
  constructor
  · intro h p
    exact (bilinForm_apply_eq_zero_iff_baseChange_tmul
      (L := completion K p) B x y).mp h
  · intro h
    exact (bilinForm_apply_eq_zero_iff_baseChange_tmul
      (L := completion K (witnessPlace K)) B x y).mpr (h (witnessPlace K))

/-- A prescribed bilinear orthogonality equation over `F(t)` holds exactly when its pure-tensor
images are orthogonal at every finite and infinite completed place. -/
theorem rationalFunction_bilinForm_apply_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) (x y : M) : B x y = 0 ↔
      ∀ p : RationalFunctionPlace F,
        B.baseChange (rationalFunctionCompletion F p)
          (1 ⊗ₜ[RatFunc F] x) (1 ⊗ₜ[RatFunc F] y) = 0 := by
  constructor
  · intro h p
    exact (bilinForm_apply_eq_zero_iff_baseChange_tmul
      (L := rationalFunctionCompletion F p) B x y).mp h
  · intro h
    exact (bilinForm_apply_eq_zero_iff_baseChange_tmul
      (L := rationalFunctionCompletion F .infinite) B x y).mpr (h .infinite)

/-- Symmetry of a bilinear form over a number field is detected at every completed place. -/
theorem numberField_bilinForm_isSymm_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) :
    B.IsSymm ↔ ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsSymm := by
  constructor
  · intro h p
    exact (bilinForm_isSymm_iff_baseChange (L := completion K p) B).mp h
  · intro h
    exact (bilinForm_isSymm_iff_baseChange (L := completion K (witnessPlace K)) B).mpr
      (h (witnessPlace K))

/-- Symmetry of a bilinear form over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_bilinForm_isSymm_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M) :
    B.IsSymm ↔ ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsSymm := by
  constructor
  · intro h p
    exact (bilinForm_isSymm_iff_baseChange (L := rationalFunctionCompletion F p) B).mp h
  · intro h
    exact (bilinForm_isSymm_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) B).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
