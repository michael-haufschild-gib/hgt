/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenDimensions

/-!
# Hasse comparison of generalized Sylvester kernels

For fixed elements `a`, `b` and scalar `c` of a central simple algebra, scalar extension
preserves the dimension of every generalized eigenspace of the Sylvester map
`z ↦ a * z - z * b`. Consequently these higher commutator multiplicities can be checked at all
completions or at one completion. The elements and scalar remain globally fixed throughout.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Field scalar extension preserves every generalized Sylvester-kernel dimension of a central
simple algebra. -/
theorem scalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_baseChange
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (a b : A.carrier) (c : K) (n : ℕ) :
    Module.finrank L (LinearMap.ker
      ((LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A b) -
        (algebraMap K L c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker
        ((LinearMap.mulLeft K a - LinearMap.mulRight K b - c • LinearMap.id) ^ n)) := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_generalizedEigenKernel_finrank_baseChange
    (LinearMap.mulLeft K a - LinearMap.mulRight K b) c n

/-- A generalized Sylvester kernel over a number-field CSA has the same dimension at every
completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K)
    (n : ℕ) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker
      ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
        LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b) -
        (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker
        ((LinearMap.mulLeft K a - LinearMap.mulRight K b - c • LinearMap.id) ^ n)) :=
  scalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_baseChange
    (L := completion K p) A a b c n

/-- A generalized Sylvester kernel over a global-function-field CSA has the same dimension at
every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) (n : ℕ) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
      ((LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a) -
        LinearMap.mulRight (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A b) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) =
      Module.finrank (RatFunc F) (LinearMap.ker
        ((LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b -
          c • LinearMap.id) ^ n)) :=
  scalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_baseChange
    (L := rationalFunctionCompletion F p) A a b c n

/-- A prescribed generalized Sylvester-kernel dimension in a number-field CSA is detected at
every completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K)
    (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K a - LinearMap.mulRight K b - c • LinearMap.id) ^ n)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      K A a b c n p, h]
  · intro h
    rw [← numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      K A a b c n (witnessPlace K)]
    exact h (witnessPlace K)

/-- A prescribed generalized Sylvester-kernel dimension in a global-function-field CSA is
detected at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b -
        c • LinearMap.id) ^ n)) = d ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      F A a b c n p, h]
  · intro h
    rw [← rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      F A a b c n .infinite]
    exact h .infinite

/-- A prescribed generalized Sylvester-kernel dimension in a number-field CSA is certified at
one completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K)
    (n d : ℕ) :
    Module.finrank K (LinearMap.ker
      ((LinearMap.mulLeft K a - LinearMap.mulRight K b - c • LinearMap.id) ^ n)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
        K A a b c n (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      K A a b c n p).symm.trans hp

/-- A prescribed generalized Sylvester-kernel dimension in a global-function-field CSA is
certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker
      ((LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b -
        c • LinearMap.id) ^ n)) = d ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
        F A a b c n .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionLocalScalarExtensionMap_intertwiner_generalizedEigenKernel_finrank_completion
      F A a b c n p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
