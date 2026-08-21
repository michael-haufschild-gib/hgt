/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormEquality
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-!
# Hasse detection for quadratic forms over number fields

Because two is invertible in a number field, Mathlib's quadratic-form base change is available at
every completion.  Equality of fixed forms and nondegeneracy then descend through a completion.
This is not a local-global classification theorem for quadratic forms up to isometry.  The same
construction deliberately does not cover rational function fields of characteristic two.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The scalar extension of a quadratic form to a number-field completion. -/
noncomputable def numberFieldQuadraticFormBaseChange (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M) (p : NumberFieldPlace K) :
    QuadraticForm (completion K p) (completion K p ⊗[K] M) := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  exact Q.baseChange (completion K p)

/-- Field scalar extension reflects equality of quadratic forms when two is invertible. -/
theorem quadraticForm_eq_iff_baseChange_eq {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q₁ Q₂ : QuadraticForm K M) :
    Q₁ = Q₂ ↔ Q₁.baseChange L = Q₂.baseChange L := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext x
    apply FaithfulSMul.algebraMap_injective K L
    simpa [Algebra.smul_def] using congrArg (fun Q => Q (1 ⊗ₜ[K] x)) h

/-- Nondegeneracy of a quadratic form descends through field scalar extension when two is
invertible. -/
theorem quadraticForm_nondegenerate_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (h : (Q.baseChange L).Nondegenerate) : Q.Nondegenerate := by
  letI : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  apply QuadraticMap.nondegenerate_polar_iff.mp
  apply bilinForm_nondegenerate_of_baseChange (L := L) Q.polarBilin
  rw [← QuadraticForm.polarBilin_baseChange]
  exact QuadraticMap.nondegenerate_polar_iff.mpr h

/-- Equality of quadratic forms over a number field is detected at every completed place. -/
theorem numberField_quadraticForm_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    {M : Type w} [AddCommGroup M] [Module K M]
    (Q₁ Q₂ : QuadraticForm K M) :
    Q₁ = Q₂ ↔ ∀ p : NumberFieldPlace K,
      numberFieldQuadraticFormBaseChange K Q₁ p = numberFieldQuadraticFormBaseChange K Q₂ p := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  constructor
  · intro h p
    rw [h]
  · intro h
    apply (quadraticForm_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) Q₁ Q₂).mpr
    simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- Nondegeneracy of a quadratic form over a number field follows when every completed base
change is nondegenerate. -/
theorem numberField_quadraticForm_nondegenerate_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    (h : ∀ p : NumberFieldPlace K, (numberFieldQuadraticFormBaseChange K Q p).Nondegenerate) :
    Q.Nondegenerate := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  apply quadraticForm_nondegenerate_of_baseChange (L := completion K (witnessPlace K)) Q
  simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

/-- Anisotropy of a quadratic form descends through field scalar extension when two is
invertible. -/
theorem quadraticForm_anisotropic_of_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Invertible (2 : K)]
    (Q : QuadraticForm K M) (h : (Q.baseChange L).Anisotropic) : Q.Anisotropic := by
  intro x hx
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) M
  simp only [TensorProduct.mk_apply, TensorProduct.tmul_zero]
  apply h
  simp [QuadraticForm.baseChange_tmul, hx]

/-- A quadratic form over a number field is anisotropic when every completed base change is
anisotropic.  In fact the proof uses one selected completion. -/
theorem numberField_quadraticForm_anisotropic_of_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (Q : QuadraticForm K M)
    (h : ∀ p : NumberFieldPlace K, (numberFieldQuadraticFormBaseChange K Q p).Anisotropic) :
    Q.Anisotropic := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  apply quadraticForm_anisotropic_of_baseChange (L := completion K (witnessPlace K)) Q
  simpa only [numberFieldQuadraticFormBaseChange] using h (witnessPlace K)

end GaloisForLFunctions.HTGeometry.ABHN
