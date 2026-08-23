/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEigenvectors

/-!
# Hasse detection of regular eigenvalues in central simple algebras

For a fixed scalar and a fixed element of a central simple algebra, a nontrivial eigenspace of
left regular multiplication is reflected by field scalar extension.  Hence this spectral property
is detected at all completions and, in this faithfully-flat setting, at any one completion.  The
scalar is fixed globally; no descent of separately chosen local eigenvectors is asserted.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- A fixed scalar is an eigenvalue of left regular multiplication exactly when it remains one
after arbitrary field scalar extension. -/
theorem scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, w} K) (x : A.carrier) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) ≠ ⊥ ↔
      LinearMap.ker (LinearMap.mulLeft L (scalarExtensionMap (L := L) A x) -
        (algebraMap K L c) • LinearMap.id) ≠ ⊥ := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact linearMap_eigenKernel_ne_bot_iff_baseChange (LinearMap.mulLeft K x) c

/-- A fixed scalar is an eigenvalue of left regular multiplication in a number-field CSA exactly
when it is one at every completion. -/
theorem numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) ≠ ⊥ ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A x) -
          (algebraMap K (completion K p) c) • LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h p
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := completion K p) A x c).mp h
  · intro h
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := completion K (witnessPlace K)) A x c).mpr (h (witnessPlace K))

/-- A fixed scalar is an eigenvalue of left regular multiplication in a global-function-field CSA
exactly when it is one at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ≠ ⊥ ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h p
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := rationalFunctionCompletion F p) A x c).mp h
  · intro h
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := rationalFunctionCompletion F RationalFunctionPlace.infinite) A x c).mpr
        (h RationalFunctionPlace.infinite)

/-- A fixed scalar is an eigenvalue of left regular multiplication in a number-field CSA exactly
when it is one at some completion. -/
theorem numberFieldLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (x : A.carrier) (c : K) :
    LinearMap.ker (LinearMap.mulLeft K x - c • LinearMap.id) ≠ ⊥ ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.ker (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A x) -
          (algebraMap K (completion K p) c) • LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h
    exact ⟨witnessPlace K, (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := completion K (witnessPlace K)) A x c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff (L := completion K p) A x c).mpr hp

/-- A fixed scalar is an eigenvalue of left regular multiplication in a global-function-field CSA
exactly when it is one at some completion. -/
theorem rationalFunctionLocalScalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (x : A.carrier)
    (c : RatFunc F) :
    LinearMap.ker (LinearMap.mulLeft (RatFunc F) x - c • LinearMap.id) ≠ ⊥ ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A x) -
          (algebraMap (RatFunc F) (rationalFunctionCompletion F p) c) • LinearMap.id) ≠ ⊥ := by
  constructor
  · intro h
    exact ⟨.infinite, (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := rationalFunctionCompletion F .infinite) A x c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_mulLeft_eigenKernel_ne_bot_iff
      (L := rationalFunctionCompletion F p) A x c).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
