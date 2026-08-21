/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormSymmetry
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Hasse certification of nondegeneracy for bilinear forms

Nondegeneracy of a bilinear form descends through any field extension.  Hence nondegeneracy at
every completion, or at a single selected completion, certifies nondegeneracy over the global
field.  The converse is not asserted here: for arbitrary possibly infinite-dimensional modules,
dualization need not commute with scalar extension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Nondegeneracy of a bilinear form descends through field scalar extension. -/
theorem bilinForm_nondegenerate_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M) (h : (B.baseChange L).Nondegenerate) : B.Nondegenerate := by
  constructor
  · intro x hx
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
    simp only [TensorProduct.mk_apply, TensorProduct.tmul_zero]
    apply h.1
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => rw [map_add, hy, hz, add_zero]
    | tmul l y => simp [LinearMap.BilinForm.baseChange_tmul, hx y]
  · intro y hy
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
    simp only [TensorProduct.mk_apply, TensorProduct.tmul_zero]
    apply h.2
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, add_zero]
    | tmul l x => simp [LinearMap.BilinForm.baseChange_tmul, hy x]

/-- Nondegeneracy over a number field follows when every completed base change is nondegenerate.
-/
theorem numberField_bilinForm_nondegenerate_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).Nondegenerate) :
    B.Nondegenerate := by
  exact bilinForm_nondegenerate_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Nondegeneracy over `F(t)` follows when every finite and infinite completed base change is
nondegenerate. -/
theorem rationalFunction_bilinForm_nondegenerate_of_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B : LinearMap.BilinForm (RatFunc F) M)
    (h : ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).Nondegenerate) : B.Nondegenerate := by
  exact bilinForm_nondegenerate_of_baseChange
    (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B
    (h RationalFunctionPlace.infinite)

end GaloisForLFunctions.HTGeometry.ABHN
