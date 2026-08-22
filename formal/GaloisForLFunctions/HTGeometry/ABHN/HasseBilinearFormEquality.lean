/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseBilinearFormNondegenerate
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-!
# Hasse detection of equality for bilinear forms

Scalar extension reflects equality of fixed bilinear forms.  Thus a pairing identity is global
exactly when it holds after every completion.  This concerns equality of specified forms, not
the substantially different local-global classification problem for forms up to isometry.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Field scalar extension reflects equality of bilinear forms. -/
theorem bilinForm_eq_iff_baseChange_eq {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M]
    (B C : LinearMap.BilinForm K M) : B = C ↔ B.baseChange L = C.baseChange L := by
  constructor
  · intro h
    rw [h]
  · intro h
    ext x y
    apply FaithfulSMul.algebraMap_injective K L
    simpa [Algebra.smul_def] using congrArg (fun D => D (1 ⊗ₜ[K] x) (1 ⊗ₜ[K] y)) h

/-- Equality of bilinear forms over a number field is detected at every completed place. -/
theorem numberField_bilinForm_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B C : LinearMap.BilinForm K M) :
    B = C ↔ ∀ p : NumberFieldPlace K, B.baseChange (completion K p) = C.baseChange (completion K p) := by
  constructor
  · intro h p
    exact (bilinForm_eq_iff_baseChange_eq (L := completion K p) B C).mp h
  · intro h
    exact (bilinForm_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) B C).mpr
      (h (witnessPlace K))

/-- Equality of bilinear forms over `F(t)` is detected at every finite and infinite completed
place. -/
theorem rationalFunction_bilinForm_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B C : LinearMap.BilinForm (RatFunc F) M) :
    B = C ↔ ∀ p : RationalFunctionPlace F,
      B.baseChange (rationalFunctionCompletion F p) =
        C.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h p
    exact (bilinForm_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) B C).mp h
  · intro h
    exact (bilinForm_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) B C).mpr
      (h RationalFunctionPlace.infinite)

/-- Equality of number-field bilinear forms can be certified at one completion. -/
theorem numberField_bilinForm_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M]
    (B C : LinearMap.BilinForm K M) :
    B = C ↔ ∃ p : NumberFieldPlace K, B.baseChange (completion K p) = C.baseChange (completion K p) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (bilinForm_eq_iff_baseChange_eq (L := completion K (witnessPlace K)) B C).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_eq_iff_baseChange_eq (L := completion K p) B C).mpr hp

/-- Equality of `F(t)`-bilinear forms can be certified at one completion. -/
theorem rationalFunction_bilinForm_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    (B C : LinearMap.BilinForm (RatFunc F) M) :
    B = C ↔ ∃ p : RationalFunctionPlace F,
      B.baseChange (rationalFunctionCompletion F p) = C.baseChange (rationalFunctionCompletion F p) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (bilinForm_eq_iff_baseChange_eq
        (L := rationalFunctionCompletion F .infinite) B C).mp h⟩
  · rintro ⟨p, hp⟩
    exact (bilinForm_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) B C).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
