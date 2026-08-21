/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseSpanning

/-!
# Hasse detection of linear independence

Scalar extension reflects linear independence of arbitrary vector families.  Together with the
spanning results, this supplies completion-wise Hasse tests for both defining conditions of a
basis, without finite-dimensional or finite-index assumptions.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

/-- A family is linearly independent exactly when its canonical scalar extension is linearly
independent. -/
theorem linearIndependent_one_tmul_iff {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    {ι : Type x} (v : ι → M) :
    LinearIndependent K v ↔ LinearIndependent L (fun i ↦ (1 : L) ⊗ₜ[K] v i) := by
  classical
  constructor
  · exact Module.Flat.linearIndependent_one_tmul
  · intro h
    rw [linearIndependent_iff_injective_finsuppLinearCombination] at h ⊢
    have hcomp : Function.Injective
        (LinearMap.lTensor L (Finsupp.linearCombination K v) ∘ₗ
          (TensorProduct.finsuppScalarRight K K L ι).symm.toLinearMap) := by
      rw [← Finsupp.linearCombination_one_tmul K L M ι]
      exact h
    have hltensor : Function.Injective (LinearMap.lTensor L (Finsupp.linearCombination K v)) := by
      intro x y hxy
      apply (TensorProduct.finsuppScalarRight K K L ι).injective
      apply hcomp
      change LinearMap.lTensor L (Finsupp.linearCombination K v)
          ((TensorProduct.finsuppScalarRight K K L ι).symm
            (TensorProduct.finsuppScalarRight K K L ι x)) =
        LinearMap.lTensor L (Finsupp.linearCombination K v)
          ((TensorProduct.finsuppScalarRight K K L ι).symm
            (TensorProduct.finsuppScalarRight K K L ι y))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact hxy
    apply (linearMap_injective_iff_baseChange_injective
      (L := L) (Finsupp.linearCombination K v)).mpr
    rw [LinearMap.baseChange_eq_ltensor]
    exact hltensor

/-- A family over a number field is linearly independent exactly when its scalar extension is
linearly independent at every completed place. -/
theorem numberField_linearIndependent_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    {ι : Type x} (v : ι → M) :
    LinearIndependent K v ↔ ∀ p : NumberFieldPlace K,
      LinearIndependent (completion K p) (fun i ↦ (1 : completion K p) ⊗ₜ[K] v i) := by
  constructor
  · intro h p
    exact (linearIndependent_one_tmul_iff (L := completion K p) v).mp h
  · intro h
    exact (linearIndependent_one_tmul_iff (L := completion K (witnessPlace K)) v).mpr
      (h (witnessPlace K))

/-- A family over `F(t)` is linearly independent exactly when its scalar extension is linearly
independent at every finite and infinite completion. -/
theorem rationalFunction_linearIndependent_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    {ι : Type x} (v : ι → M) :
    LinearIndependent (RatFunc F) v ↔ ∀ p : RationalFunctionPlace F,
      LinearIndependent (rationalFunctionCompletion F p)
        (fun i ↦ (1 : rationalFunctionCompletion F p) ⊗ₜ[RatFunc F] v i) := by
  constructor
  · intro h p
    exact (linearIndependent_one_tmul_iff (L := rationalFunctionCompletion F p) v).mp h
  · intro h
    exact (linearIndependent_one_tmul_iff
      (L := rationalFunctionCompletion F .infinite) v).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
