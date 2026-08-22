/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapDimensions

/-!
# Hasse detection of intertwiner dimensions in central simple algebras

The intertwiners from `a` to `b` form the kernel of the Sylvester map `x ↦ a * x - x * b`.
Its dimension is unchanged by scalar extension, hence detectable at every completion. This
measures morphism spaces between the `K[t]`-module structures defined by `a` and `b`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- The dimension of the intertwiner space from `a` to `b` is unchanged by field scalar
extension. -/
theorem scalarExtensionMap_intertwiner_ker_finrank {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) :
    Module.finrank L (LinearMap.ker (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
      LinearMap.mulRight L (scalarExtensionMap (L := L) A b))) =
      Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K b)) := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_ker_finrank_baseChange (L := L)
    (LinearMap.mulLeft K a - LinearMap.mulRight K b)

/-- The dimension of the intertwiner space from `a` to `b` is unchanged at every completed place
of a number field. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_completion
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier)
    (p : NumberFieldPlace K) :
    Module.finrank (completion K p)
      (LinearMap.ker (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
          (numberFieldLocalScalarExtensionMap K p A b))) =
        Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K b)) :=
  scalarExtensionMap_intertwiner_ker_finrank (L := completion K p) A a b

/-- The dimension of the intertwiner space from `a` to `b` equals `d` exactly when this holds at
every completed place of a number field. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K b)) = d ↔
      ∀ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A b))) = d := by
  constructor
  · intro h p
    rw [numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_completion K A a b p, h]
  · intro h
    rw [← numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_completion K A a b
      (witnessPlace K)]
    exact h (witnessPlace K)

/-- The dimension of the intertwiner space from `a` to `b` is unchanged at every finite and
infinite completed place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_completion
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (p : RationalFunctionPlace F) :
    Module.finrank (rationalFunctionCompletion F p)
      (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b))) =
        Module.finrank (RatFunc F)
          (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) :=
  scalarExtensionMap_intertwiner_ker_finrank (L := rationalFunctionCompletion F p) A a b

/-- The dimension of the intertwiner space from `a` to `b` equals `d` exactly when this holds at
every finite and infinite completed place of `F(t)`. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) = d ↔
      ∀ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A b))) = d := by
  constructor
  · intro h p
    rw [rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_completion F A a b p, h]
  · intro h
    rw [← rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_completion F A a b
      .infinite]
    exact h .infinite

/-- A prescribed intertwiner-space dimension over a number field can be certified at one
completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (d : ℕ) :
    Module.finrank K (LinearMap.ker (LinearMap.mulLeft K a - LinearMap.mulRight K b)) = d ↔
      ∃ p : NumberFieldPlace K,
        Module.finrank (completion K p)
          (LinearMap.ker (LinearMap.mulLeft (completion K p)
            (numberFieldLocalScalarExtensionMap K p A a) - LinearMap.mulRight (completion K p)
              (numberFieldLocalScalarExtensionMap K p A b))) = d := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_completion K A a b
        (witnessPlace K)).trans h⟩
  · rintro ⟨p, hp⟩
    exact (numberFieldLocalScalarExtensionMap_intertwiner_ker_finrank_completion K A a b p).symm.trans hp

/-- A prescribed intertwiner-space dimension over `F(t)` can be certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a b : A.carrier) (d : ℕ) :
    Module.finrank (RatFunc F)
      (LinearMap.ker (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b)) = d ↔
      ∃ p : RationalFunctionPlace F,
        Module.finrank (rationalFunctionCompletion F p)
          (LinearMap.ker (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
              LinearMap.mulRight (rationalFunctionCompletion F p)
                (rationalFunctionLocalScalarExtensionMap F p A b))) = d := by
  constructor
  · intro h
    exact ⟨.infinite,
      (rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_completion F A a b
        .infinite).trans h⟩
  · rintro ⟨p, hp⟩
    exact (rationalFunctionLocalScalarExtensionMap_intertwiner_ker_finrank_completion F A a b p).symm.trans hp

end GaloisForLFunctions.HTGeometry.ABHN
