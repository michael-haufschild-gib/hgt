/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariantValues
import GaloisForLFunctions.HTGeometry.ABHN.HassePolynomialSeparable

/-!
# Hasse detection of separable regular characteristic polynomials

The regular characteristic polynomial of a central-simple-algebra element commutes with scalar
extension, and separability is reflected by every field extension.  Thus regular semisimplicity
at the level of characteristic polynomials is a completionwise property of a fixed element.

This does not say that local eigenvectors or local conjugacy data descend globally.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Separability of the regular characteristic polynomial is reflected by arbitrary field scalar
extension of a central simple algebra. -/
theorem scalarExtensionMap_regularCharpoly_separable_iff
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (a : A.carrier) :
    (LinearMap.mulLeft K a).charpoly.Separable ↔
      (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)).charpoly.Separable := by
  have hchar :
      (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)).charpoly =
        (LinearMap.mulLeft K a).charpoly.map (algebraMap K L) :=
    (scalarExtensionMap_regularCharpoly_eq_iff (L := L) A a
      (LinearMap.mulLeft K a).charpoly).mp rfl
  constructor
  · intro h
    rw [hchar]
    exact (polynomial_separable_iff_map (L := L) (LinearMap.mulLeft K a).charpoly).mp h
  · intro h
    apply (polynomial_separable_iff_map (L := L) (LinearMap.mulLeft K a).charpoly).mpr
    rw [← hchar]
    exact h

/-- A number-field CSA element has separable regular characteristic polynomial exactly when its
image does at every completed place. -/
theorem numberField_regularCharpoly_separable_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (LinearMap.mulLeft K a).charpoly.Separable ↔ ∀ p : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)).charpoly.Separable := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularCharpoly_separable_iff
      (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_regularCharpoly_separable_iff
      (L := completion K (witnessPlace K)) A a).mpr (h (witnessPlace K))

/-- A global-function-field CSA element has separable regular characteristic polynomial exactly
when its image does at every completed place. -/
theorem rationalFunction_regularCharpoly_separable_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (LinearMap.mulLeft (RatFunc F) a).charpoly.Separable ↔ ∀ p : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a)).charpoly.Separable := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularCharpoly_separable_iff
      (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_regularCharpoly_separable_iff
      (L := rationalFunctionCompletion F .infinite) A a).mpr (h .infinite)

/-- Separability of a number-field CSA regular characteristic polynomial is certified at one
completion. -/
theorem numberField_regularCharpoly_separable_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) :
    (LinearMap.mulLeft K a).charpoly.Separable ↔ ∃ p : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)).charpoly.Separable := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_regularCharpoly_separable_iff
        (L := completion K (witnessPlace K)) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularCharpoly_separable_iff (L := completion K p) A a).mpr hp

/-- Separability of a global-function-field CSA regular characteristic polynomial is certified
at one completion. -/
theorem rationalFunction_regularCharpoly_separable_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    (LinearMap.mulLeft (RatFunc F) a).charpoly.Separable ↔ ∃ p : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a)).charpoly.Separable := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_regularCharpoly_separable_iff
        (L := rationalFunctionCompletion F .infinite) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularCharpoly_separable_iff
      (L := rationalFunctionCompletion F p) A a).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
