/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseModuleRanks
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Hasse detection for linear endomorphism invariants

For a finite-dimensional vector space, characteristic polynomial, trace, and determinant commute
with field scalar extension.  Faithfulness of extension reflects equality with a specified global
polynomial or scalar, producing completion-wise tests for these endomorphism invariants.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Equality of a characteristic polynomial with a specified global polynomial is reflected by
field scalar extension. -/
theorem linearMap_charpoly_eq_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (p : Polynomial K) :
    f.charpoly = p ↔ (f.baseChange L).charpoly = p.map (algebraMap K L) := by
  rw [LinearMap.charpoly_baseChange]
  constructor
  · intro h
    rw [h]
  · intro h
    apply Polynomial.map_injective (algebraMap K L) (FaithfulSMul.algebraMap_injective K L)
    simpa using h

/-- Equality of trace with a specified global scalar is reflected by field scalar extension. -/
theorem linearMap_trace_eq_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.trace K M f = a ↔
      LinearMap.trace L (L ⊗[K] M) (f.baseChange L) = algebraMap K L a := by
  constructor
  · intro h
    rw [LinearMap.trace_baseChange, h]
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    rw [← LinearMap.trace_baseChange]
    exact h

/-- Equality of determinant with a specified global scalar is reflected by field scalar extension. -/
theorem linearMap_det_eq_iff_baseChange {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.det f = a ↔ LinearMap.det (f.baseChange L) = algebraMap K L a := by
  constructor
  · intro h
    rw [LinearMap.det_baseChange, h]
  · intro h
    apply FaithfulSMul.algebraMap_injective K L
    rw [← LinearMap.det_baseChange]
    exact h

/-- A number-field endomorphism has characteristic polynomial `p` exactly when each completed
scalar extension has the coefficientwise scalar extension of `p` as characteristic polynomial. -/
theorem numberField_linearMap_charpoly_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (p : Polynomial K) :
    f.charpoly = p ↔ ∀ v : NumberFieldPlace K,
      (f.baseChange (completion K v)).charpoly = p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h v
    exact (linearMap_charpoly_eq_iff_baseChange (L := completion K v) f p).mp h
  · intro h
    exact (linearMap_charpoly_eq_iff_baseChange
      (L := completion K (witnessPlace K)) f p).mpr (h (witnessPlace K))

/-- A number-field endomorphism has trace `a` exactly when every completed scalar extension has
trace equal to the image of `a`. -/
theorem numberField_linearMap_trace_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.trace K M f = a ↔ ∀ v : NumberFieldPlace K,
      LinearMap.trace (completion K v) (completion K v ⊗[K] M) (f.baseChange (completion K v)) =
        algebraMap K (completion K v) a := by
  constructor
  · intro h v
    exact (linearMap_trace_eq_iff_baseChange (L := completion K v) f a).mp h
  · intro h
    exact (linearMap_trace_eq_iff_baseChange
      (L := completion K (witnessPlace K)) f a).mpr (h (witnessPlace K))

/-- A number-field endomorphism has determinant `a` exactly when every completed scalar extension
has determinant equal to the image of `a`. -/
theorem numberField_linearMap_det_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.det f = a ↔ ∀ v : NumberFieldPlace K,
      LinearMap.det (f.baseChange (completion K v)) = algebraMap K (completion K v) a := by
  constructor
  · intro h v
    exact (linearMap_det_eq_iff_baseChange (L := completion K v) f a).mp h
  · intro h
    exact (linearMap_det_eq_iff_baseChange
      (L := completion K (witnessPlace K)) f a).mpr (h (witnessPlace K))

/-- An `F(t)`-endomorphism has characteristic polynomial `p` exactly when every finite and
infinite completed scalar extension has the coefficientwise scalar extension of `p`. -/
theorem rationalFunction_linearMap_charpoly_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (p : Polynomial (RatFunc F)) :
    f.charpoly = p ↔ ∀ v : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F v)).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h v
    exact (linearMap_charpoly_eq_iff_baseChange
      (L := rationalFunctionCompletion F v) f p).mp h
  · intro h
    exact (linearMap_charpoly_eq_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f p).mpr (h .infinite)

/-- An `F(t)`-endomorphism has trace `a` exactly when every finite and infinite completed scalar
extension has trace equal to the image of `a`. -/
theorem rationalFunction_linearMap_trace_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.trace (RatFunc F) M f = a ↔ ∀ v : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F v) (rationalFunctionCompletion F v ⊗[RatFunc F] M)
        (f.baseChange (rationalFunctionCompletion F v)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F v) a := by
  constructor
  · intro h v
    exact (linearMap_trace_eq_iff_baseChange
      (L := rationalFunctionCompletion F v) f a).mp h
  · intro h
    exact (linearMap_trace_eq_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f a).mpr (h .infinite)

/-- An `F(t)`-endomorphism has determinant `a` exactly when every finite and infinite completed
scalar extension has determinant equal to the image of `a`. -/
theorem rationalFunction_linearMap_det_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.det f = a ↔ ∀ v : RationalFunctionPlace F,
      LinearMap.det (f.baseChange (rationalFunctionCompletion F v)) =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) a := by
  constructor
  · intro h v
    exact (linearMap_det_eq_iff_baseChange
      (L := rationalFunctionCompletion F v) f a).mp h
  · intro h
    exact (linearMap_det_eq_iff_baseChange
      (L := rationalFunctionCompletion F .infinite) f a).mpr (h .infinite)

/-- A specified characteristic polynomial of a number-field endomorphism is certified at one
completed place. -/
theorem numberField_linearMap_charpoly_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (p : Polynomial K) :
    f.charpoly = p ↔ ∃ v : NumberFieldPlace K,
      (f.baseChange (completion K v)).charpoly = p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_charpoly_eq_iff_baseChange (L := completion K (witnessPlace K)) f p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_charpoly_eq_iff_baseChange (L := completion K v) f p).mpr hv

/-- A specified trace of a number-field endomorphism is certified at one completed place. -/
theorem numberField_linearMap_trace_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.trace K M f = a ↔ ∃ v : NumberFieldPlace K,
      LinearMap.trace (completion K v) (completion K v ⊗[K] M) (f.baseChange (completion K v)) =
        algebraMap K (completion K v) a := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_trace_eq_iff_baseChange (L := completion K (witnessPlace K)) f a).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_trace_eq_iff_baseChange (L := completion K v) f a).mpr hv

/-- A specified determinant of a number-field endomorphism is certified at one completed place. -/
theorem numberField_linearMap_det_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : M →ₗ[K] M) (a : K) :
    LinearMap.det f = a ↔ ∃ v : NumberFieldPlace K,
      LinearMap.det (f.baseChange (completion K v)) = algebraMap K (completion K v) a := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (linearMap_det_eq_iff_baseChange (L := completion K (witnessPlace K)) f a).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_det_eq_iff_baseChange (L := completion K v) f a).mpr hv

/-- A specified characteristic polynomial of an `F(t)`-endomorphism is certified at one
completed place. -/
theorem rationalFunction_linearMap_charpoly_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (p : Polynomial (RatFunc F)) :
    f.charpoly = p ↔ ∃ v : RationalFunctionPlace F,
      (f.baseChange (rationalFunctionCompletion F v)).charpoly =
        p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_charpoly_eq_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_charpoly_eq_iff_baseChange (L := rationalFunctionCompletion F v) f p).mpr hv

/-- A specified trace of an `F(t)`-endomorphism is certified at one completed place. -/
theorem rationalFunction_linearMap_trace_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.trace (RatFunc F) M f = a ↔ ∃ v : RationalFunctionPlace F,
      LinearMap.trace (rationalFunctionCompletion F v)
        (rationalFunctionCompletion F v ⊗[RatFunc F] M) (f.baseChange (rationalFunctionCompletion F v)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F v) a := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_trace_eq_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f a).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_trace_eq_iff_baseChange (L := rationalFunctionCompletion F v) f a).mpr hv

/-- A specified determinant of an `F(t)`-endomorphism is certified at one completed place. -/
theorem rationalFunction_linearMap_det_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M]
    [Module.Finite (RatFunc F) M] (f : M →ₗ[RatFunc F] M) (a : RatFunc F) :
    LinearMap.det f = a ↔ ∃ v : RationalFunctionPlace F,
      LinearMap.det (f.baseChange (rationalFunctionCompletion F v)) =
        algebraMap (RatFunc F) (rationalFunctionCompletion F v) a := by
  constructor
  · intro h
    exact ⟨.infinite,
      (linearMap_det_eq_iff_baseChange
        (L := rationalFunctionCompletion F .infinite) f a).mp h⟩
  · rintro ⟨v, hv⟩
    exact (linearMap_det_eq_iff_baseChange (L := rationalFunctionCompletion F v) f a).mpr hv

end GaloisForLFunctions.HTGeometry.ABHN
