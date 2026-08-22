/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import Mathlib.RingTheory.Finiteness.Descent

/-!
# Hasse detection for finiteness properties

Faithfully flat scalar extension reflects finite modules and finite-type or finitely presented
commutative algebras.  Applied to a global-field completion, this gives local--global tests for
the finiteness hypotheses used by finite-dimensional algebra and algebraic-geometry arguments.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Finite generation of a module over a field is reflected by every field scalar extension. -/
theorem module_finite_iff_tensorProduct_finite {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module K M] :
    Module.Finite K M ↔ Module.Finite L (L ⊗[K] M) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

/-- Finite type of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_finiteType_iff_tensorProduct_finiteType {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] :
    Algebra.FiniteType K A ↔ Algebra.FiniteType L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    exact Algebra.FiniteType.baseChange L
  · intro h
    letI := h
    exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat L

/-- Finite presentation of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_finitePresentation_iff_tensorProduct_finitePresentation
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] :
    Algebra.FinitePresentation K A ↔ Algebra.FinitePresentation L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    exact Algebra.FinitePresentation.baseChange L
  · intro h
    letI := h
    exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat L

/-- A module over a number field is finite dimensional exactly when every completed scalar
extension is finite dimensional. -/
theorem numberField_module_finite_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    Module.Finite K M ↔ ∀ p : NumberFieldPlace K,
      Module.Finite (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h p
    exact (module_finite_iff_tensorProduct_finite (L := completion K p)).mp h
  · intro h
    exact (module_finite_iff_tensorProduct_finite
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A module over `F(t)` is finite dimensional exactly when every finite and infinite completed
scalar extension is finite dimensional. -/
theorem rationalFunction_module_finite_iff_forall_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    Module.Finite (RatFunc F) M ↔ ∀ p : RationalFunctionPlace F,
      Module.Finite (rationalFunctionCompletion F p) (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h p
    exact (module_finite_iff_tensorProduct_finite (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (module_finite_iff_tensorProduct_finite
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A commutative algebra over a number field is finite type exactly when all completed scalar
extensions are finite type. -/
theorem numberField_algebra_finiteType_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FiniteType K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.FiniteType (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_finiteType_iff_tensorProduct_finiteType (L := completion K p)).mp h
  · intro h
    exact (algebra_finiteType_iff_tensorProduct_finiteType
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is finite type exactly when all finite and infinite
completed scalar extensions are finite type. -/
theorem rationalFunction_algebra_finiteType_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FiniteType (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.FiniteType (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_finiteType_iff_tensorProduct_finiteType
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_finiteType_iff_tensorProduct_finiteType
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A commutative algebra over a number field is finitely presented exactly when all completed
scalar extensions are finitely presented. -/
theorem numberField_algebra_finitePresentation_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FinitePresentation K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.FinitePresentation (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := completion K p)).mp h
  · intro h
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is finitely presented exactly when all finite and infinite
completed scalar extensions are finitely presented. -/
theorem rationalFunction_algebra_finitePresentation_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FinitePresentation (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.FinitePresentation (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- Finite generation of a number-field module can be certified at one completion. -/
theorem numberField_module_finite_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {M : Type w} [AddCommGroup M] [Module K M] :
    Module.Finite K M ↔ ∃ p : NumberFieldPlace K,
      Module.Finite (completion K p) (completion K p ⊗[K] M) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (module_finite_iff_tensorProduct_finite (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_finite_iff_tensorProduct_finite (L := completion K p)).mpr hp

/-- Finite generation of an `F(t)`-module can be certified at one completion. -/
theorem rationalFunction_module_finite_iff_exists_place (F : Type u)
    [Field F] [Finite F] {M : Type w} [AddCommGroup M] [Module (RatFunc F) M] :
    Module.Finite (RatFunc F) M ↔ ∃ p : RationalFunctionPlace F,
      Module.Finite (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] M) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (module_finite_iff_tensorProduct_finite
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (module_finite_iff_tensorProduct_finite
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Finite type of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_finiteType_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FiniteType K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.FiniteType (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_finiteType_iff_tensorProduct_finiteType
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_finiteType_iff_tensorProduct_finiteType (L := completion K p)).mpr hp

/-- Finite type of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_finiteType_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FiniteType (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.FiniteType (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_finiteType_iff_tensorProduct_finiteType
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_finiteType_iff_tensorProduct_finiteType
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Finite presentation of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_finitePresentation_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FinitePresentation K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.FinitePresentation (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_finitePresentation_iff_tensorProduct_finitePresentation
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := completion K p)).mpr hp

/-- Finite presentation of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_finitePresentation_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FinitePresentation (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.FinitePresentation (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_finitePresentation_iff_tensorProduct_finitePresentation
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_finitePresentation_iff_tensorProduct_finitePresentation
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
