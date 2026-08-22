/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormSymmetry
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Hasse certification of nondegeneracy for bilinear forms

Nondegeneracy of a bilinear form descends through any field extension. On finite-dimensional
spaces, its Gram determinant remains nonzero after scalar extension, so nondegeneracy is an exact
local-global property. The unrestricted descent theorem remains available for arbitrary modules.
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

/-- Nondegeneracy of a finite-dimensional bilinear form is preserved by field scalar extension. -/
theorem bilinForm_nondegenerate_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (B : LinearMap.BilinForm K M) (h : B.Nondegenerate) :
    (B.baseChange L).Nondegenerate := by
  let b := Module.finBasis K M
  have hmatrix : LinearMap.BilinForm.toMatrix (b.baseChange L) (B.baseChange L) =
      (algebraMap K L).mapMatrix (LinearMap.BilinForm.toMatrix b B) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Algebra.smul_def]
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero (B.baseChange L) (b.baseChange L)
  rw [hmatrix, ← RingHom.map_det]
  simpa using (FaithfulSMul.algebraMap_injective K L).ne_iff.mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp h)

/-- Nondegeneracy of a finite-dimensional bilinear form is detected by field scalar extension. -/
theorem bilinForm_nondegenerate_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (B : LinearMap.BilinForm K M) :
    B.Nondegenerate ↔ (B.baseChange L).Nondegenerate := by
  constructor
  · exact bilinForm_nondegenerate_baseChange B
  · exact bilinForm_nondegenerate_of_baseChange B

/-- Nondegeneracy over a number field follows when every completed base change is nondegenerate.
-/
theorem numberField_bilinForm_nondegenerate_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B : LinearMap.BilinForm K M)
    (h : ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).Nondegenerate) :
    B.Nondegenerate := by
  exact bilinForm_nondegenerate_of_baseChange (L := completion K (witnessPlace K)) B
    (h (witnessPlace K))

/-- Nondegeneracy of a finite-dimensional bilinear form over a number field is detected at every
completed place. -/
theorem numberField_bilinForm_nondegenerate_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (B : LinearMap.BilinForm K M) :
    B.Nondegenerate ↔ ∀ p : NumberFieldPlace K, (B.baseChange (completion K p)).Nondegenerate := by
  constructor
  · intro h p
    exact (bilinForm_nondegenerate_iff_baseChange (L := completion K p) B).mp h
  · intro h
    exact (bilinForm_nondegenerate_iff_baseChange
      (L := completion K (witnessPlace K)) B).mpr (h (witnessPlace K))

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

/-- Nondegeneracy of a finite-dimensional bilinear form over `F(t)` is detected at every finite
and infinite completed place. -/
theorem rationalFunction_bilinForm_nondegenerate_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [FiniteDimensional (RatFunc F) M] (B : LinearMap.BilinForm (RatFunc F) M) :
    B.Nondegenerate ↔ ∀ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).Nondegenerate := by
  constructor
  · intro h p
    exact (bilinForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F p) B).mp h
  · intro h
    exact (bilinForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) B).mpr (h .infinite)

/-- Nondegeneracy of a finite-dimensional number-field bilinear form can be certified at one
completion. -/
theorem numberField_bilinForm_nondegenerate_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (B : LinearMap.BilinForm K M) :
    B.Nondegenerate ↔ ∃ p : NumberFieldPlace K, (B.baseChange (completion K p)).Nondegenerate := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (bilinForm_nondegenerate_iff_baseChange
        (L := completion K (witnessPlace K)) B).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_nondegenerate_iff_baseChange (L := completion K p) B).mpr hp

/-- Nondegeneracy of a finite-dimensional `F(t)`-bilinear form can be certified at one
completion. -/
theorem rationalFunction_bilinForm_nondegenerate_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [FiniteDimensional (RatFunc F) M] (B : LinearMap.BilinForm (RatFunc F) M) :
    B.Nondegenerate ↔ ∃ p : RationalFunctionPlace F,
      (B.baseChange (rationalFunctionCompletion F p)).Nondegenerate := by
  constructor
  · intro h
    exact ⟨.infinite,
      (bilinForm_nondegenerate_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) B).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_nondegenerate_iff_baseChange
      (L := rationalFunctionCompletion F p) B).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
