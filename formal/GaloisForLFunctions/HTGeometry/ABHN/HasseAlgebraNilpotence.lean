/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalScalarExtension

/-!
# Hasse detection for nilpotent elements of central simple algebras

The scalar-extension map of a central simple algebra is injective and preserves powers.  Hence an
element is nilpotent precisely when all of its completed scalar extensions are nilpotent.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

/-- Nilpotence of an element of a central simple algebra is reflected by arbitrary field scalar
extension. -/
theorem scalarExtensionMap_isNilpotent_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    IsNilpotent a ↔ IsNilpotent (scalarExtensionMap (L := L) A a) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [← map_pow, hn, map_zero]
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply scalarExtensionMap_injective (L := L) A
    rw [map_pow, hn, map_zero]

/-- An element of a central simple algebra over a number field is nilpotent exactly when it is
nilpotent after scalar extension at every completed place. -/
theorem numberFieldLocalScalarExtensionMap_isNilpotent_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, v} K) (a : A.carrier) :
    IsNilpotent a ↔ ∀ p : NumberFieldPlace K,
      IsNilpotent (numberFieldLocalScalarExtensionMap K p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isNilpotent_iff (L := completion K p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isNilpotent_iff (L := completion K (witnessPlace K)) A a).mpr
      (h (witnessPlace K))

/-- An element of a central simple algebra over `F(t)` is nilpotent exactly when it is nilpotent
after scalar extension at every finite and infinite completed place. -/
theorem rationalFunctionLocalScalarExtensionMap_isNilpotent_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, v} (RatFunc F)) (a : A.carrier) :
    IsNilpotent a ↔ ∀ p : RationalFunctionPlace F,
      IsNilpotent (rationalFunctionLocalScalarExtensionMap F p A a) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_isNilpotent_iff
      (L := rationalFunctionCompletion F p) A a).mp h
  · intro h
    exact (scalarExtensionMap_isNilpotent_iff
      (L := rationalFunctionCompletion F .infinite) A a).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
