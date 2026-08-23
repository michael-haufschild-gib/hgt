/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraEigenvectors
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenDimensions

/-!
# Hasse comparison of generalized regular eigenspaces

For a fixed scalar and element of a central simple algebra, scalar extension preserves the
dimension of every generalized eigenspace of left regular multiplication.  Consequently these
Jordan-theoretic multiplicities can be checked at all completions or at one completion.  The
scalar remains globally fixed throughout.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Field scalar extension preserves the dimension of every generalized left-regular eigenspace
of a central simple algebra. -/
theorem scalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_baseChange
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (x : A.carrier) (c : K) (n : ℕ) :
    Module.finrank L (LinearMap.ker
      ((LinearMap.mulLeft L (scalarExtensionMap (L := L) A x) -
        (algebraMap K L c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact linearMap_generalizedEigenKernel_finrank_baseChange (LinearMap.mulLeft K x) c n

/-- A generalized left-regular eigenspace over a number-field CSA has the same dimension at every
completion. -/
theorem numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier) (c : K)
    (n : ℕ) (p : NumberFieldPlace K) :
    Module.finrank (completion K p) (LinearMap.ker
      ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A x) -
        (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) =
      Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) :=
  scalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_baseChange
    (L := completion K p) A x c n

/-- A generalized left-regular eigenspace over a global-function-field CSA has the same dimension
at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) (n : ℕ) (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
      ((LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A x) -
        (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) =
      Module.finrank (RatFunc F) (LinearMap.ker
        ((LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ^ n)) :=
  scalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_baseChange
    (L := rationalFunctionCompletion F p) A x c n

/-- A prescribed generalized left-regular eigenspace dimension in a number-field CSA is detected
at every completion. -/
theorem numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier) (c : K)
    (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      K A x c n p, h]
  · intro h
    rw [← numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      K A x c n (witnessPlace K)]
    exact h (witnessPlace K)

/-- A prescribed generalized left-regular eigenspace dimension in a global-function-field CSA is
detected at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker ((LinearMap.mulLeft (RatFunc F) x -
      c • LinearMap.id) ^ n)) = d ↔ ∀ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h p
    rw [rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      F A x c n p, h]
  · intro h
    rw [← rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      F A x c n .infinite]
    exact h .infinite

/-- A prescribed generalized left-regular eigenspace dimension in a number-field CSA is certified
at one completion. -/
theorem numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier) (c : K)
    (n d : ℕ) :
    Module.finrank K (LinearMap.ker ((LinearMap.mulLeft K x - c • LinearMap.id) ^ n)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p) (LinearMap.ker
          ((LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A x) -
            (algebraMap K (completion K p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
        K A x c n (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      K A x c n p).symm.trans hp

/-- A prescribed generalized left-regular eigenspace dimension in a global-function-field CSA is
certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) (n d : ℕ) :
    Module.finrank (RatFunc F) (LinearMap.ker ((LinearMap.mulLeft (RatFunc F) x -
      c • LinearMap.id) ^ n)) = d ↔ ∃ p : RationalFunctionPlace F,
      Module.finrank (rationalFunctionCompletion F p) (LinearMap.ker
        ((LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ^ n)) = d := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
        F A x c n .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionLocalScalarExtensionMap_mulLeft_generalizedEigenKernel_finrank_completion
      F A x c n p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
