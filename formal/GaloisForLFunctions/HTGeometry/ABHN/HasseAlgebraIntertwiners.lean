/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision

/-!
# Hasse principle for intertwiners in central simple algebras

The Sylvester map `x ↦ a*x - x*b` is linear.  Its scalar extension is the corresponding local
Sylvester map.  Consequently both its inhomogeneous equations and existence of nonzero
intertwiners are detected by every completion of the supported global fields.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The Sylvester map after scalar extension is the base change of the original Sylvester map. -/
theorem scalarExtensionMap_intertwiner_eq_linearMapBaseChange {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A b) =
      (LinearMap.mulLeft K a - LinearMap.mulRight K b).baseChange L := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange,
    scalarExtensionMap_mulRight_eq_linearMapBaseChange]
  rw [← LinearMap.baseChange_sub]

/-- An inhomogeneous intertwining equation has a solution exactly when its scalar extension does. -/
theorem scalarExtensionMap_exists_intertwining_defect_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b c : A.carrier) :
    (∃ x, a * x - x * b = c) ↔ ∃ z,
      scalarExtensionMap (L := L) A a * z - z * scalarExtensionMap (L := L) A b =
        scalarExtensionMap (L := L) A c := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨scalarExtensionMap (L := L) A x, by
      rw [← map_mul, ← map_mul, ← map_sub, hx]⟩
  · rintro ⟨z, hz⟩
    have hpreimage : ∃ z,
        (LinearMap.mulLeft K a - LinearMap.mulRight K b).baseChange L z =
          (1 : L) ⊗ₜ[K] c := by
      refine ⟨z, ?_⟩
      rw [← scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
      simpa [scalarExtensionMap, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using hz
    simpa only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply] using
      (linearMap_exists_preimage_iff_baseChange (L := L)
        (LinearMap.mulLeft K a - LinearMap.mulRight K b) c).mpr hpreimage

/-- A nonzero intertwiner survives and is reflected by arbitrary field scalar extension. -/
theorem scalarExtensionMap_exists_nonzero_intertwiner_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∃ z, z ≠ 0 ∧
      scalarExtensionMap (L := L) A a * z = z * scalarExtensionMap (L := L) A b := by
  let f : A.carrier →ₗ[K] A.carrier := LinearMap.mulLeft K a - LinearMap.mulRight K b
  let fL : L ⊗[K] A.carrier →ₗ[L] L ⊗[K] A.carrier :=
    LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
      LinearMap.mulRight L (scalarExtensionMap (L := L) A b)
  have hfL : fL = f.baseChange L := scalarExtensionMap_intertwiner_eq_linearMapBaseChange A a b
  constructor
  · rintro ⟨x, hx0, hx⟩
    refine ⟨scalarExtensionMap (L := L) A x, ?_, ?_⟩
    · intro hzero
      apply hx0
      apply scalarExtensionMap_injective (L := L) A
      simpa using hzero
    · rw [← map_mul, ← map_mul, hx]
  · rintro ⟨z, hz0, hz⟩
    have hz' : fL z = 0 := by
      simpa only [fL, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        sub_eq_zero] using hz
    have hnotInjL : ¬ Function.Injective (f.baseChange L) := by
      intro hinj
      apply hz0
      apply hinj
      rw [← hfL, hz']
      exact (map_zero fL).symm
    have hnotInj : ¬ Function.Injective f := fun hinj => hnotInjL
      ((linearMap_injective_iff_baseChange_injective (L := L) f).mp hinj)
    have hker : ∃ x, x ≠ 0 ∧ f x = 0 := by
      by_contra h
      apply hnotInj
      rw [← LinearMap.ker_eq_bot]
      rw [Submodule.eq_bot_iff]
      intro x hx
      by_contra hx0
      apply h
      refine ⟨x, hx0, ?_⟩
      exact hx
    rcases hker with ⟨x, hx0, hx⟩
    exact ⟨x, hx0, by
      simpa only [f, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        sub_eq_zero] using hx⟩

/-- An inhomogeneous intertwining equation over a number field has a solution exactly when it has
one at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b c : A.carrier) :
    (∃ x, a * x - x * b = c) ↔ ∀ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z -
        z * numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := completion K p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := completion K (witnessPlace K)) A a b c).mpr (h (witnessPlace K))

/-- A nonzero intertwiner over a number field exists exactly when one exists at every completed
place. -/
theorem numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∀ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p A a * z =
        z * numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff (L := completion K p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff
      (L := completion K (witnessPlace K)) A a b).mpr (h (witnessPlace K))

/-- An inhomogeneous intertwining equation over `F(t)` has a solution exactly when it has one at
every finite and infinite completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b c : A.carrier) :
    (∃ x, a * x - x * b = c) ↔ ∀ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z -
        z * rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b c).mpr (h .infinite)

/-- A nonzero intertwiner over `F(t)` exists exactly when one exists at every finite and infinite
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∀ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p A a * z =
        z * rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h p
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff
      (L := rationalFunctionCompletion F p) A a b).mp h
  · intro h
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff
      (L := rationalFunctionCompletion F .infinite) A a b).mpr (h .infinite)

/-- A fixed inhomogeneous intertwining equation over a number field is solvable exactly when it
is solvable at one completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b c : A.carrier) :
    (∃ x, a * x - x * b = c) ↔ ∃ p : NumberFieldPlace K, ∃ z,
      numberFieldLocalScalarExtensionMap K p A a * z -
        z * numberFieldLocalScalarExtensionMap K p A b =
          numberFieldLocalScalarExtensionMap K p A c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_intertwining_defect_eq_iff
        (L := completion K (witnessPlace K)) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := completion K p) A a b c).mpr hp

/-- A fixed homogeneous intertwining equation over a number field has a nonzero solution exactly
when it does at one completed place. -/
theorem numberFieldLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∃ p : NumberFieldPlace K, ∃ z, z ≠ 0 ∧
      numberFieldLocalScalarExtensionMap K p A a * z =
        z * numberFieldLocalScalarExtensionMap K p A b := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_exists_nonzero_intertwiner_iff
        (L := completion K (witnessPlace K)) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff
      (L := completion K p) A a b).mpr hp

/-- A fixed inhomogeneous intertwining equation over `F(t)` is solvable exactly when it is
solvable at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_intertwining_defect_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b c : A.carrier) :
    (∃ x, a * x - x * b = c) ↔ ∃ p : RationalFunctionPlace F, ∃ z,
      rationalFunctionLocalScalarExtensionMap F p A a * z -
        z * rationalFunctionLocalScalarExtensionMap F p A b =
          rationalFunctionLocalScalarExtensionMap F p A c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_intertwining_defect_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_intertwining_defect_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mpr hp

/-- A fixed homogeneous intertwining equation over `F(t)` has a nonzero solution exactly when it
does at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_exists_nonzero_intertwiner_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier) :
    (∃ x, x ≠ 0 ∧ a * x = x * b) ↔ ∃ p : RationalFunctionPlace F, ∃ z, z ≠ 0 ∧
      rationalFunctionLocalScalarExtensionMap F p A a * z =
        z * rationalFunctionLocalScalarExtensionMap F p A b := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_exists_nonzero_intertwiner_iff
        (L := rationalFunctionCompletion F .infinite) A a b).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_exists_nonzero_intertwiner_iff
      (L := rationalFunctionCompletion F p) A a b).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
