/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraDivision
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Hasse detection for regular trace and norm

For an algebra element, its regular trace and regular norm are respectively the trace and
determinant of left multiplication.  They commute with field scalar extension.  This gives
completion-wise tests for their vanishing over number fields and rational global function fields.
These are regular invariants, not reduced trace or reduced norm.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- The regular trace of an element commutes with field scalar extension. -/
theorem scalarExtensionMap_regularTrace {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.trace L (L ⊗[K] A.carrier)
        (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)) =
      algebraMap K L (LinearMap.trace K A.carrier (LinearMap.mulLeft K a)) := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact LinearMap.trace_baseChange (LinearMap.mulLeft K a) L

/-- The regular norm of an element commutes with field scalar extension. -/
theorem scalarExtensionMap_regularNorm {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.det (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)) =
      algebraMap K L (LinearMap.det (LinearMap.mulLeft K a)) := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact LinearMap.det_baseChange (LinearMap.mulLeft K a)

/-- The regular trace of a central-simple-algebra element over a number field vanishes exactly
when its regular trace vanishes after scalar extension at every completed place. -/
theorem numberField_regularTrace_eq_zero_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) = 0 ↔ ∀ p : NumberFieldPlace K,
      LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a)) = 0 := by
  constructor
  · intro h p
    simpa only [numberFieldLocalScalarExtensionMap, h, map_zero] using
      (scalarExtensionMap_regularTrace (L := completion K p) A a)
  · intro h
    apply FaithfulSMul.algebraMap_injective K (completion K (witnessPlace K))
    calc
      algebraMap K (completion K (witnessPlace K))
          (LinearMap.trace K A.carrier (LinearMap.mulLeft K a)) =
          LinearMap.trace (completion K (witnessPlace K))
            (completion K (witnessPlace K) ⊗[K] A.carrier)
              (LinearMap.mulLeft (completion K (witnessPlace K))
                (numberFieldLocalScalarExtensionMap K (witnessPlace K) A a)) := by
        simpa only [numberFieldLocalScalarExtensionMap] using
          (scalarExtensionMap_regularTrace (L := completion K (witnessPlace K)) A a).symm
      _ = 0 := h (witnessPlace K)

/-- The regular norm of a central-simple-algebra element over a number field vanishes exactly
when its regular norm vanishes after scalar extension at every completed place. -/
theorem numberField_regularNorm_eq_zero_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) :
    LinearMap.det (LinearMap.mulLeft K a) = 0 ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)) = 0 := by
  constructor
  · intro h p
    simpa only [numberFieldLocalScalarExtensionMap, h, map_zero] using
      (scalarExtensionMap_regularNorm (L := completion K p) A a)
  · intro h
    apply FaithfulSMul.algebraMap_injective K (completion K (witnessPlace K))
    calc
      algebraMap K (completion K (witnessPlace K)) (LinearMap.det (LinearMap.mulLeft K a)) =
          LinearMap.det (LinearMap.mulLeft (completion K (witnessPlace K))
            (numberFieldLocalScalarExtensionMap K (witnessPlace K) A a)) := by
        simpa only [numberFieldLocalScalarExtensionMap] using
          (scalarExtensionMap_regularNorm (L := completion K (witnessPlace K)) A a).symm
      _ = 0 := h (witnessPlace K)

/-- The regular trace of a central-simple-algebra element over `F(t)` vanishes exactly when its
regular trace vanishes after scalar extension at every finite and infinite completion. -/
theorem rationalFunction_regularTrace_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a) = 0 ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a)) = 0 := by
  constructor
  · intro h p
    simpa only [rationalFunctionLocalScalarExtensionMap, h, map_zero] using
      (scalarExtensionMap_regularTrace (L := rationalFunctionCompletion F p) A a)
  · intro h
    apply FaithfulSMul.algebraMap_injective (RatFunc F)
      (rationalFunctionCompletion F .infinite)
    calc
      algebraMap (RatFunc F) (rationalFunctionCompletion F .infinite)
          (LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a)) =
          LinearMap.trace (rationalFunctionCompletion F .infinite)
            (rationalFunctionCompletion F .infinite ⊗[RatFunc F] A.carrier)
              (LinearMap.mulLeft (rationalFunctionCompletion F .infinite)
                (rationalFunctionLocalScalarExtensionMap F .infinite A a)) := by
        simpa only [rationalFunctionLocalScalarExtensionMap] using
          (scalarExtensionMap_regularTrace
            (L := rationalFunctionCompletion F .infinite) A a).symm
      _ = 0 := h .infinite

/-- The regular norm of a central-simple-algebra element over `F(t)` vanishes exactly when its
regular norm vanishes after scalar extension at every finite and infinite completion. -/
theorem rationalFunction_regularNorm_eq_zero_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a : A.carrier) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a) = 0 ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a)) = 0 := by
  constructor
  · intro h p
    simpa only [rationalFunctionLocalScalarExtensionMap, h, map_zero] using
      (scalarExtensionMap_regularNorm (L := rationalFunctionCompletion F p) A a)
  · intro h
    apply FaithfulSMul.algebraMap_injective (RatFunc F)
      (rationalFunctionCompletion F .infinite)
    calc
      algebraMap (RatFunc F) (rationalFunctionCompletion F .infinite)
          (LinearMap.det (LinearMap.mulLeft (RatFunc F) a)) =
          LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F .infinite)
            (rationalFunctionLocalScalarExtensionMap F .infinite A a)) := by
        simpa only [rationalFunctionLocalScalarExtensionMap] using
          (scalarExtensionMap_regularNorm
            (L := rationalFunctionCompletion F .infinite) A a).symm
      _ = 0 := h .infinite

end GaloisForLFunctions.HTGeometry.ABHN
