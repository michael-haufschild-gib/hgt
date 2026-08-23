/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraIntertwiners
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapInvariants

/-!
# Hasse detection for Sylvester spectral invariants

For fixed elements `a` and `b` of a central simple algebra, the characteristic polynomial, trace,
and determinant of the Sylvester map `z ↦ a * z - z * b` commute with scalar extension. Thus each
specified global invariant is detectable at all completions or at one completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Equality of a Sylvester characteristic polynomial with a specified polynomial is reflected by
field scalar extension. -/
theorem scalarExtensionMap_intertwinerCharpoly_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) (p : Polynomial K) :
    (LinearMap.mulLeft K a - LinearMap.mulRight K b).charpoly = p ↔
      (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A b)).charpoly =
          p.map (algebraMap K L) := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_charpoly_eq_iff_baseChange (LinearMap.mulLeft K a - LinearMap.mulRight K b) p

/-- Equality of a Sylvester trace with a specified scalar is reflected by field scalar extension. -/
theorem scalarExtensionMap_intertwinerTrace_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      LinearMap.trace L (L ⊗[K] A.carrier)
        (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
          LinearMap.mulRight L (scalarExtensionMap (L := L) A b)) = algebraMap K L c := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_trace_eq_iff_baseChange (LinearMap.mulLeft K a - LinearMap.mulRight K b) c

/-- Equality of a Sylvester determinant with a specified scalar is reflected by field scalar
extension. -/
theorem scalarExtensionMap_intertwinerDet_eq_iff {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      LinearMap.det (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a) -
        LinearMap.mulRight L (scalarExtensionMap (L := L) A b)) = algebraMap K L c := by
  rw [scalarExtensionMap_intertwiner_eq_linearMapBaseChange]
  exact linearMap_det_eq_iff_baseChange (LinearMap.mulLeft K a - LinearMap.mulRight K b) c

/-- The Sylvester characteristic polynomial over a number-field CSA is detected at every
completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier)
    (q : Polynomial K) :
    (LinearMap.mulLeft K a - LinearMap.mulRight K b).charpoly = q ↔
      ∀ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)).charpoly =
            q.map (algebraMap K (completion K p)) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff (L := completion K p) A a b q).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff
      (L := completion K (witnessPlace K)) A a b q).mpr (h (witnessPlace K))

/-- The Sylvester trace over a number-field CSA is detected at every completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
          (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) =
              algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerTrace_eq_iff (L := completion K p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerTrace_eq_iff
      (L := completion K (witnessPlace K)) A a b c).mpr (h (witnessPlace K))

/-- The Sylvester determinant over a number-field CSA is detected at every completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      ∀ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) =
            algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerDet_eq_iff (L := completion K p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerDet_eq_iff
      (L := completion K (witnessPlace K)) A a b c).mpr (h (witnessPlace K))

/-- The Sylvester characteristic polynomial over a global-function-field CSA is detected at every
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b).charpoly = q ↔
      ∀ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)).charpoly =
              q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff
      (L := rationalFunctionCompletion F p) A a b q).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b q).mpr (h .infinite)

/-- The Sylvester trace over a global-function-field CSA is detected at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier
      (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) = c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A b)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerTrace_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerTrace_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b c).mpr (h .infinite)

/-- The Sylvester determinant over a global-function-field CSA is detected at every completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) = c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)) =
              algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_intertwinerDet_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mp h
  · intro h
    exact (scalarExtensionMap_intertwinerDet_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a b c).mpr (h .infinite)

/-- A specified Sylvester characteristic polynomial over a number-field CSA is certified at one
completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier)
    (q : Polynomial K) :
    (LinearMap.mulLeft K a - LinearMap.mulRight K b).charpoly = q ↔
      ∃ p : NumberFieldPlace K,
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)).charpoly =
            q.map (algebraMap K (completion K p)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_intertwinerCharpoly_eq_iff
        (L := completion K (witnessPlace K)) A a b q).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff (L := completion K p) A a b q).mpr hp

/-- A specified Sylvester trace over a number-field CSA is certified at one completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
          (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a) -
            LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) =
              algebraMap K (completion K p) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_intertwinerTrace_eq_iff
        (L := completion K (witnessPlace K)) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerTrace_eq_iff (L := completion K p) A a b c).mpr hp

/-- A specified Sylvester determinant over a number-field CSA is certified at one completion. -/
theorem numberFieldLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place
    (K : Type u) [Field K] [NumberField K] (A : CSA.{u, w} K) (a b : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a - LinearMap.mulRight K b) = c ↔
      ∃ p : NumberFieldPlace K,
        LinearMap.det (LinearMap.mulLeft (completion K p)
          (numberFieldLocalScalarExtensionMap K p A a) -
          LinearMap.mulRight (completion K p) (numberFieldLocalScalarExtensionMap K p A b)) =
            algebraMap K (completion K p) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_intertwinerDet_eq_iff
        (L := completion K (witnessPlace K)) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerDet_eq_iff (L := completion K p) A a b c).mpr hp

/-- A specified Sylvester characteristic polynomial over a global-function-field CSA is certified
at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerCharpoly_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (q : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b).charpoly = q ↔
      ∃ p : RationalFunctionPlace F,
        (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)).charpoly =
              q.map (algebraMap (RatFunc F) (rationalFunctionCompletion F p)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_intertwinerCharpoly_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b q).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerCharpoly_eq_iff
      (L := rationalFunctionCompletion F p) A a b q).mpr hp

/-- A specified Sylvester trace over a global-function-field CSA is certified at one completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerTrace_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier
      (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) = c ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
          (LinearMap.mulLeft (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A a) -
            LinearMap.mulRight (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A b)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_intertwinerTrace_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerTrace_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mpr hp

/-- A specified Sylvester determinant over a global-function-field CSA is certified at one
completion. -/
theorem rationalFunctionLocalScalarExtensionMap_intertwinerDet_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F)) (a b : A.carrier)
    (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a - LinearMap.mulRight (RatFunc F) b) = c ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
          (rationalFunctionLocalScalarExtensionMap F p A a) -
          LinearMap.mulRight (rationalFunctionCompletion F p)
            (rationalFunctionLocalScalarExtensionMap F p A b)) =
              algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_intertwinerDet_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a b c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_intertwinerDet_eq_iff
      (L := rationalFunctionCompletion F p) A a b c).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
