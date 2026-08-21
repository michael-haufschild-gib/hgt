/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality

/-!
# Hasse certification of alternating and reflexive bilinear forms

Alternation and reflexivity descend through field scalar extension.  Consequently, the indicated
property at every completion, or at one selected completion, certifies it globally.  These are
one-way certification statements; preservation in the other direction is not asserted here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Alternation of a bilinear form descends through field scalar extension. -/
theorem bilinForm_isAlt_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : (B.baseChange L).IsAlt) : B.IsAlt := by
  intro x
  apply FaithfulSMul.algebraMap_injective K L
  simpa [Algebra.smul_def] using h (1 ⊗ₜ[K] x)

/-- Reflexivity of a bilinear form descends through field scalar extension. -/
theorem bilinForm_isRefl_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : (B.baseChange L).IsRefl) : B.IsRefl := by
  intro x y hxy
  apply FaithfulSMul.algebraMap_injective K L
  have hlocal := h (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y) (by
    simp [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def, hxy])
  simpa [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def] using hlocal

/-- Alternation of a bilinear form over a number field follows from alternation at every completed
place. -/
theorem numberField_bilinForm_isAlt_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsAlt) : B.IsAlt := by
  exact bilinForm_isAlt_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Reflexivity of a bilinear form over a number field follows from reflexivity at every completed
place. -/
theorem numberField_bilinForm_isRefl_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).IsRefl) : B.IsRefl := by
  exact bilinForm_isRefl_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Alternation of a bilinear form over `F(t)` follows from alternation at every finite and
infinite completed place. -/
theorem rationalFunction_bilinForm_isAlt_of_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsAlt) : B.IsAlt := by
  exact bilinForm_isAlt_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B
    (h RationalFunctionPlace.infinite)

/-- Reflexivity of a bilinear form over `F(t)` follows from reflexivity at every finite and
infinite completed place. -/
theorem rationalFunction_bilinForm_isRefl_of_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).IsRefl) : B.IsRefl := by
  exact bilinForm_isRefl_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B
    (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
