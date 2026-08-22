/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraCommutator
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions

/-!
# Hasse detection of centralizer dimensions in central simple algebras

The centralizer of an element is the kernel of its commutator map. Since that linear map commutes
with scalar extension, centralizer dimension is unchanged at every completion. This is useful for
the regular-element and conjugacy stratifications of a central simple algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The dimension of the kernel of the commutator map is unchanged by field scalar extension. -/
theorem scalarExtensionMap_commutator_ker_finrank {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    Module.finrank L (LinearMap.ker (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
      LinearMap.mulRight L (scalarExtensionMap (L := L) A a))) =
      Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K a)) := by
  rw [scalarExtensionMap_commutator_eq_linearMapBaseChange]
  exact linearMap_ker_finrank_baseChange (L := L)
    (LinearMap.mulLeft K a - LinearMap.mulRight K a)

/-- The commutator-kernel dimension of an element is unchanged at every completed place of a
number field. -/
theorem numberFieldLocalScalarExtensionMap_commutator_ker_finrank_completion
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier)
    (p : NumberFieldPlace K) :
    Module.finrank (completion K p)
      (LinearMap.ker (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
          (numberFieldLocalScalarExtensionMap K p A a))) =
        Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K a)) :=
  scalarExtensionMap_commutator_ker_finrank (L := completion K p) A a

/-- The commutator-kernel dimension of an element equals `d` exactly when this holds at every
completed place of a number field. -/
theorem numberFieldLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K a)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A a))) = d := by
  constructor
  · intro h p
    rw [numberFieldLocalScalarExtensionMap_commutator_ker_finrank_completion K A a p, h]
  · intro h
    rw [← numberFieldLocalScalarExtensionMap_commutator_ker_finrank_completion K A a
      (witnessPlace K)]
    exact h (witnessPlace K)

/-- The commutator-kernel dimension of an element is unchanged at every finite and infinite
completed place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_completion
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier)
    (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a))) =
        Module.finrank (RatFunc F)
          (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) a)) :=
  scalarExtensionMap_commutator_ker_finrank (L := rationalFunctionCompletion F p) A a

/-- The commutator-kernel dimension of an element equals `d` exactly when this holds at every
finite and infinite completed place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) a)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A a))) = d := by
  constructor
  · intro h p
    rw [rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_completion F A a p, h]
  · intro h
    rw [← rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_completion F A a
      .infinite]
    exact h .infinite

/-- A prescribed centralizer dimension over a number field can be certified at one completion. -/
theorem numberFieldLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a : A.carrier) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K a)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A a))) = d := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_commutator_ker_finrank_completion K A a
        (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldLocalScalarExtensionMap_commutator_ker_finrank_completion K A a p).symm.trans hp

/-- A prescribed centralizer dimension over `F(t)` can be certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) a)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A a))) = d := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_completion F A a
        .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionLocalScalarExtensionMap_commutator_ker_finrank_completion F A a p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
