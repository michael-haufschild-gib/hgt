/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision

/-!
# Hasse principle for commutator equations in central simple algebras

For a fixed `a`, the map `x ↦ a*x - x*a` is linear.  Its scalar extension is the corresponding
commutator map in the scalar-extended algebra, so membership in its image is detected by every
completion of a number field or rational global function field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The commutator map after scalar extension is the base change of the original commutator map. -/
theorem scalarExtensionMap_commutator_eq_linearMapBaseChange {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A a) =
      (LinearMap.mulLeft K a - LinearMap.mulRight K a).baseChange L := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange,
    scalarExtensionMap_mulRight_eq_linearMapBaseChange]
  rw [← LinearMap.baseChange_sub]

/-- A commutator equation has a solution exactly when its scalar extension has a solution. -/
theorem scalarExtensionMap_exists_commutator_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, a * x - x * a = b) ↔ ∃ z,
      scalarExtensionMap (L := L) A a * z - z * scalarExtensionMap (L := L) A a =
        scalarExtensionMap (L := L) A b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨scalarExtensionMap (L := L) A x, by
      rw [← map_mul, ← map_mul, ← map_sub, hx]⟩
  · rintro ⟨z, hz⟩
    have hpreimage : ∃ z,
        (LinearMap.mulLeft K a - LinearMap.mulRight K a).baseChange L z =
          (1 : L) ⊗ₜ[K] b := by
      refine ⟨z, ?_⟩
      rw [← scalarExtensionMap_commutator_eq_linearMapBaseChange]
      simpa [scalarExtensionMap, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using hz
    simpa only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
      (linearMap_exists_preimage_iff_baseChange (L := L)
        (LinearMap.mulLeft K a - LinearMap.mulRight K a) b).mpr hpreimage

/-- A commutator equation in a central simple algebra over a number field has a solution exactly
when it has one at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, a * x - x * a = b) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z -
        z * numberFieldLocalScalarExtensionMap K p A a =
          numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_commutator_eq_iff (L := completion K p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_commutator_eq_iff
      (L := completion K (witnessPlace K)) A a b).mpr (h (witnessPlace K))

/-- A commutator equation in a central simple algebra over `F(t)` has a solution exactly when it
has one at every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_commutator_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, a * x - x * a = b) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z -
        z * rationalFunctionLocalScalarExtensionMap F p A a =
          rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_commutator_eq_iff
      (L := rationalFunctionCompletion F p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_commutator_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
