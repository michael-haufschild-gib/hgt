/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapSolvability

/-!
# Hasse principle for one-sided division in central simple algebras

Membership of a fixed element in a principal left or right ideal is a linear equation.  Thus it
is reflected by scalar extension to a field, and over the supported global fields it is detected
at every completion.  Local witnesses need not agree; a global witness is recovered by descent.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Left multiplication after scalar extension is the base change of left multiplication. -/
theorem scalarExtensionMap_mulLeft_eq_linearMapBaseChange {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) =
      (LinearMap.mulLeft K a).baseChange L := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul l x =>
    rw [LinearMap.baseChange_tmul]
    simp [scalarExtensionMap, Algebra.TensorProduct.tmul_mul_tmul]

/-- Right multiplication after scalar extension is the base change of right multiplication. -/
theorem scalarExtensionMap_mulRight_eq_linearMapBaseChange {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.mulRight L (scalarExtensionMap (L := L) A a) =
      (LinearMap.mulRight K a).baseChange L := by
  apply LinearMap.ext
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul l x =>
    rw [LinearMap.baseChange_tmul]
    simp [scalarExtensionMap, Algebra.TensorProduct.tmul_mul_tmul]

/-- A left-division equation has a solution exactly when its scalar extension does. -/
theorem scalarExtensionMap_exists_mulLeft_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, a * x = b) ↔ ∃ z,
      scalarExtensionMap (L := L) A a * z = scalarExtensionMap (L := L) A b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨scalarExtensionMap (L := L) A x, by rw [← map_mul, hx]⟩
  · rintro ⟨z, hz⟩
    have hpreimage : ∃ z, (LinearMap.mulLeft K a).baseChange L z =
        (1 : L) ⊗ₜ[K] b := by
      refine ⟨z, ?_⟩
      rw [← scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
      simpa [scalarExtensionMap, LinearMap.mulLeft_apply] using hz
    simpa only [LinearMap.mulLeft_apply] using
      (linearMap_exists_preimage_iff_baseChange (L := L) (LinearMap.mulLeft K a) b).mpr hpreimage

/-- A right-division equation has a solution exactly when its scalar extension does. -/
theorem scalarExtensionMap_exists_mulRight_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x * a = b) ↔ ∃ z,
      z * scalarExtensionMap (L := L) A a = scalarExtensionMap (L := L) A b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨scalarExtensionMap (L := L) A x, by rw [← map_mul, hx]⟩
  · rintro ⟨z, hz⟩
    have hpreimage : ∃ z, (LinearMap.mulRight K a).baseChange L z =
        (1 : L) ⊗ₜ[K] b := by
      refine ⟨z, ?_⟩
      rw [← scalarExtensionMap_mulRight_eq_linearMapBaseChange]
      simpa [scalarExtensionMap, LinearMap.mulRight_apply] using hz
    simpa only [LinearMap.mulRight_apply] using
      (linearMap_exists_preimage_iff_baseChange (L := L) (LinearMap.mulRight K a) b).mpr hpreimage

/-- A left-division equation in a central simple algebra over a number field has a solution
exactly when it has one at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, a * x = b) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z =
        numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_mulLeft_eq_iff (L := completion K p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_mulLeft_eq_iff (L := completion K (witnessPlace K)) A a b).mpr
      (h (witnessPlace K))

/-- A right-division equation in a central simple algebra over a number field has a solution
exactly when it has one at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x * a = b) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      z * numberFieldLocalScalarExtensionMap K p A a =
        numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_mulRight_eq_iff (L := completion K p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_mulRight_eq_iff (L := completion K (witnessPlace K)) A a b).mpr
      (h (witnessPlace K))

/-- A left-division equation in a central simple algebra over `F(t)` has a solution exactly when
it has one at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, a * x = b) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_mulLeft_eq_iff (L := rationalFunctionCompletion F p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_mulLeft_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b).mpr (h .infinite)

/-- A right-division equation in a central simple algebra over `F(t)` has a solution exactly when
it has one at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, x * a = b) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p A a =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_mulRight_eq_iff
      (L := rationalFunctionCompletion F p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_mulRight_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b).mpr (h .infinite)

/-- A left-division equation in a number-field CSA is solvable exactly when it is solvable at one
completion. -/
theorem numberFieldLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, a * x = b) ↔ ∃ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z =
        numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_mulLeft_eq_iff
        (L := completion K (witnessPlace K)) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_mulLeft_eq_iff (L := completion K p) A a b).mpr hp

/-- A right-division equation in a number-field CSA is solvable exactly when it is solvable at
one completion. -/
theorem numberFieldLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x * a = b) ↔ ∃ p : NumberFieldPlace K, ∃ z,
      z * numberFieldLocalScalarExtensionMap K p A a =
        numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_mulRight_eq_iff
        (L := completion K (witnessPlace K)) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_mulRight_eq_iff (L := completion K p) A a b).mpr hp

/-- A left-division equation in a rational-function-field CSA is solvable exactly when it is
solvable at one finite or infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_mulLeft_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, a * x = b) ↔ ∃ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_mulLeft_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_mulLeft_eq_iff
      (L := rationalFunctionCompletion F p) A a b).mpr hp

/-- A right-division equation in a rational-function-field CSA is solvable exactly when it is
solvable at one finite or infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_mulRight_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, x * a = b) ↔ ∃ p : RationalFunctionPlace F, ∃ z,
      z * rationalFunctionLocalScalarExtensionMap F p A a =
        rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_mulRight_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_mulRight_eq_iff
      (L := rationalFunctionCompletion F p) A a b).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
