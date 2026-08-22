/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraNilpotence
import Mathlib.Algebra.Ring.Idempotent

/-!
# Hasse detection of idempotents in central simple algebras

The injective scalar-extension map preserves and reflects the equation `a * a = a`. Therefore,
fixed idempotents and the decompositions they induce are detectable at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Idempotence of an element of a central simple algebra is reflected by arbitrary field scalar
extension. -/
theorem scalarExtensionMap_isIdempotent_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    IsIdempotentElem a ↔ IsIdempotentElem (scalarExtensionMap (L := L) A a) := by
  constructor
  · intro h
    rw [IsIdempotentElem] at h ⊢
    rw [← map_mul, h]
  · intro h
    rw [IsIdempotentElem] at h ⊢
    apply scalarExtensionMap_injective (L := L) A
    rw [map_mul, h]

/-- An element of a central simple algebra over a number field is idempotent exactly when it is
idempotent after scalar extension at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_isIdempotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) (a : A.carrier) :
    IsIdempotentElem a ↔ ∀ p : NumberFieldPlace K,
      IsIdempotentElem (numberFieldLocalScalarExtensionMap K p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isIdempotent_iff (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isIdempotent_iff
      (L := completion K (witnessPlace K)) A a).mpr (h (witnessPlace K))

/-- An element of a central simple algebra over `F(t)` is idempotent exactly when it is
idempotent after scalar extension at every finite and infinite completed place. -/
theorem rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    IsIdempotentElem a ↔ ∀ p : RationalFunctionPlace F,
      IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isIdempotent_iff
      (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isIdempotent_iff
      (L := rationalFunctionCompletion F .infinite) A a).mpr (h .infinite)

/-- Idempotence of a number-field CSA element is detected at one completion. -/
theorem numberFieldLocalScalarExtensionMap_isIdempotent_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) (a : A.carrier) :
    IsIdempotentElem a ↔ ∃ p : NumberFieldPlace K,
      IsIdempotentElem (numberFieldLocalScalarExtensionMap K p A a) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_isIdempotent_iff
        (L := completion K (witnessPlace K)) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_isIdempotent_iff (L := completion K p) A a).mpr hp

/-- Idempotence of a rational-function-field CSA element is detected at one finite or infinite
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_isIdempotent_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    IsIdempotentElem a ↔ ∃ p : RationalFunctionPlace F,
      IsIdempotentElem (rationalFunctionLocalScalarExtensionMap F p A a) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_isIdempotent_iff
        (L := rationalFunctionCompletion F .infinite) A a).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_isIdempotent_iff
      (L := rationalFunctionCompletion F p) A a).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
