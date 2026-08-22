/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseAlgebraRegularInvariants
import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapInvariants

/-!
# Hasse detection for specified regular trace and norm values

Regular trace and norm of a fixed central-simple-algebra element commute with scalar extension.
Consequently, equality with any specified global scalar is detectable at every completion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

/-- Equality of the regular characteristic polynomial with a specified polynomial is reflected by
arbitrary field scalar extension. -/
theorem scalarExtensionMap_regularCharpoly_eq_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) (p : Polynomial K) :
    (LinearMap.mulLeft K a).charpoly = p ↔
      (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)).charpoly =
        p.map (algebraMap K L) := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact linearMap_charpoly_eq_iff_baseChange (LinearMap.mulLeft K a) p

/-- Equality of regular trace with a specified scalar is reflected by arbitrary field scalar
extension. -/
theorem scalarExtensionMap_regularTrace_eq_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) = c ↔
      LinearMap.trace L (L ⊗[K] A.carrier)
        (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)) = algebraMap K L c := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact linearMap_trace_eq_iff_baseChange (LinearMap.mulLeft K a) c

/-- Equality of regular norm with a specified scalar is reflected by arbitrary field scalar
extension. -/
theorem scalarExtensionMap_regularNorm_eq_iff {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a) = c ↔
      LinearMap.det (LinearMap.mulLeft L (scalarExtensionMap (L := L) A a)) = algebraMap K L c := by
  rw [scalarExtensionMap_mulLeft_eq_linearMapBaseChange]
  exact linearMap_det_eq_iff_baseChange (LinearMap.mulLeft K a) c

/-- The regular characteristic polynomial of an element of a central simple algebra over a number
field equals `p` exactly when this holds after scalar extension at every completed place. -/
theorem numberField_regularCharpoly_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (p : Polynomial K) :
    (LinearMap.mulLeft K a).charpoly = p ↔ ∀ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v A a)).charpoly =
          p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h v
    exact (scalarExtensionMap_regularCharpoly_eq_iff (L := completion K v) A a p).mp h
  · intro h
    exact (scalarExtensionMap_regularCharpoly_eq_iff
      (L := completion K (witnessPlace K)) A a p).mpr (h (witnessPlace K))

/-- The regular trace of an element of a central simple algebra over a number field equals `c`
exactly when this holds after scalar extension at every completed place. -/
theorem numberField_regularTrace_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) = c ↔ ∀ p : NumberFieldPlace K,
      LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a)) =
          algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularTrace_eq_iff (L := completion K p) A a c).mp h
  · intro h
    exact (scalarExtensionMap_regularTrace_eq_iff
      (L := completion K (witnessPlace K)) A a c).mpr (h (witnessPlace K))

/-- The regular norm of an element of a central simple algebra over a number field equals `c`
exactly when this holds after scalar extension at every completed place. -/
theorem numberField_regularNorm_eq_iff_forall_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a) = c ↔ ∀ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)) = algebraMap K (completion K p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularNorm_eq_iff (L := completion K p) A a c).mp h
  · intro h
    exact (scalarExtensionMap_regularNorm_eq_iff
      (L := completion K (witnessPlace K)) A a c).mpr (h (witnessPlace K))

/-- The regular characteristic polynomial of an element of a central simple algebra over `F(t)`
equals `p` exactly when this holds after scalar extension at every finite and infinite completed
place. -/
theorem rationalFunction_regularCharpoly_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (p : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a).charpoly = p ↔ ∀ v : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F v)
        (rationalFunctionLocalScalarExtensionMap F v A a)).charpoly =
          p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h v
    exact (scalarExtensionMap_regularCharpoly_eq_iff
      (L := rationalFunctionCompletion F v) A a p).mp h
  · intro h
    exact (scalarExtensionMap_regularCharpoly_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a p).mpr (h .infinite)

/-- The regular trace of an element of a central simple algebra over `F(t)` equals `c` exactly
when this holds after scalar extension at every finite and infinite completed place. -/
theorem rationalFunction_regularTrace_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a) = c ↔
      ∀ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularTrace_eq_iff
      (L := rationalFunctionCompletion F p) A a c).mp h
  · intro h
    exact (scalarExtensionMap_regularTrace_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a c).mpr (h .infinite)

/-- The regular norm of an element of a central simple algebra over `F(t)` equals `c` exactly
when this holds after scalar extension at every finite and infinite completed place. -/
theorem rationalFunction_regularNorm_eq_iff_forall_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a) = c ↔ ∀ p : RationalFunctionPlace F,
      LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h p
    exact (scalarExtensionMap_regularNorm_eq_iff
      (L := rationalFunctionCompletion F p) A a c).mp h
  · intro h
    exact (scalarExtensionMap_regularNorm_eq_iff
      (L := rationalFunctionCompletion F .infinite) A a c).mpr (h .infinite)

/-- A prescribed regular characteristic polynomial over a number field can be certified at one
completion. -/
theorem numberField_regularCharpoly_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (p : Polynomial K) :
    (LinearMap.mulLeft K a).charpoly = p ↔ ∃ v : NumberFieldPlace K,
      (LinearMap.mulLeft (completion K v)
        (numberFieldLocalScalarExtensionMap K v A a)).charpoly =
          p.map (algebraMap K (completion K v)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_regularCharpoly_eq_iff
        (L := completion K (witnessPlace K)) A a p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (scalarExtensionMap_regularCharpoly_eq_iff (L := completion K v) A a p).mpr hv

/-- A prescribed regular trace over a number field can be certified at one completion. -/
theorem numberField_regularTrace_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.trace K A.carrier (LinearMap.mulLeft K a) = c ↔ ∃ p : NumberFieldPlace K,
      LinearMap.trace (completion K p) (completion K p ⊗[K] A.carrier)
        (LinearMap.mulLeft (completion K p) (numberFieldLocalScalarExtensionMap K p A a)) =
          algebraMap K (completion K p) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_regularTrace_eq_iff
        (L := completion K (witnessPlace K)) A a c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularTrace_eq_iff (L := completion K p) A a c).mpr hp

/-- A prescribed regular norm over a number field can be certified at one completion. -/
theorem numberField_regularNorm_eq_iff_exists_place (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, w} K) (a : A.carrier) (c : K) :
    LinearMap.det (LinearMap.mulLeft K a) = c ↔ ∃ p : NumberFieldPlace K,
      LinearMap.det (LinearMap.mulLeft (completion K p)
        (numberFieldLocalScalarExtensionMap K p A a)) = algebraMap K (completion K p) c := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (scalarExtensionMap_regularNorm_eq_iff
        (L := completion K (witnessPlace K)) A a c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularNorm_eq_iff (L := completion K p) A a c).mpr hp

/-- A prescribed regular characteristic polynomial over `F(t)` can be certified at one
completion. -/
theorem rationalFunction_regularCharpoly_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (p : Polynomial (RatFunc F)) :
    (LinearMap.mulLeft (RatFunc F) a).charpoly = p ↔ ∃ v : RationalFunctionPlace F,
      (LinearMap.mulLeft (rationalFunctionCompletion F v)
        (rationalFunctionLocalScalarExtensionMap F v A a)).charpoly =
          p.map (algebraMap (RatFunc F) (rationalFunctionCompletion F v)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_regularCharpoly_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a p).mp h⟩
  · rintro ⟨v, hv⟩
    exact (scalarExtensionMap_regularCharpoly_eq_iff
      (L := rationalFunctionCompletion F v) A a p).mpr hv

/-- A prescribed regular trace over `F(t)` can be certified at one completion. -/
theorem rationalFunction_regularTrace_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.trace (RatFunc F) A.carrier (LinearMap.mulLeft (RatFunc F) a) = c ↔
      ∃ p : RationalFunctionPlace F,
        LinearMap.trace (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] A.carrier)
            (LinearMap.mulLeft (rationalFunctionCompletion F p)
              (rationalFunctionLocalScalarExtensionMap F p A a)) =
                algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_regularTrace_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularTrace_eq_iff
      (L := rationalFunctionCompletion F p) A a c).mpr hp

/-- A prescribed regular norm over `F(t)` can be certified at one completion. -/
theorem rationalFunction_regularNorm_eq_iff_exists_place
    (F : Type u) [Field F] [Finite F] (A : CSA.{u, w} (RatFunc F))
    (a : A.carrier) (c : RatFunc F) :
    LinearMap.det (LinearMap.mulLeft (RatFunc F) a) = c ↔ ∃ p : RationalFunctionPlace F,
      LinearMap.det (LinearMap.mulLeft (rationalFunctionCompletion F p)
        (rationalFunctionLocalScalarExtensionMap F p A a)) =
          algebraMap (RatFunc F) (rationalFunctionCompletion F p) c := by
  constructor
  · intro h
    exact ⟨.infinite,
      (scalarExtensionMap_regularNorm_eq_iff
        (L := rationalFunctionCompletion F .infinite) A a c).mp h⟩
  · rintro ⟨p, hp⟩
    exact (scalarExtensionMap_regularNorm_eq_iff
      (L := rationalFunctionCompletion F p) A a c).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
