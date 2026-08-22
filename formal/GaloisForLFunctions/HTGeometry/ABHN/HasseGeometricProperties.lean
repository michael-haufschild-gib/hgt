/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import GaloisForLFunctions.HTGeometry.ABHN.FiniteEtale
import Mathlib.RingTheory.Etale.Descent

/-!
# Hasse detection for geometric algebra properties

Smoothness, unramifiedness, and étaleness descend along faithfully flat scalar extensions.  Thus
they are detected by the completed scalar extensions of a commutative algebra over either global
field model in this development.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Smoothness of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_smooth_iff_tensorProduct_smooth {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] :
    Algebra.Smooth K A ↔ Algebra.Smooth L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat L

/-- Unramifiedness of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_unramified_iff_tensorProduct_unramified {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] :
    Algebra.Unramified K A ↔ Algebra.Unramified L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Algebra.Unramified.of_unramified_tensorProduct_of_faithfullyFlat L

/-- Étaleness of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_etale_iff_tensorProduct_etale {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] :
    Algebra.Etale K A ↔ Algebra.Etale L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L

/-- A commutative algebra over a number field is smooth exactly when all completed scalar
extensions are smooth. -/
theorem numberField_algebra_smooth_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Smooth K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.Smooth (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_smooth_iff_tensorProduct_smooth (L := completion K p)).mp h
  · intro h
    exact (algebra_smooth_iff_tensorProduct_smooth
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is smooth exactly when all finite and infinite completed
scalar extensions are smooth. -/
theorem rationalFunction_algebra_smooth_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Smooth (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.Smooth (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_smooth_iff_tensorProduct_smooth (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_smooth_iff_tensorProduct_smooth
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A commutative algebra over a number field is unramified exactly when all completed scalar
extensions are unramified. -/
theorem numberField_algebra_unramified_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Unramified K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.Unramified (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_unramified_iff_tensorProduct_unramified (L := completion K p)).mp h
  · intro h
    exact (algebra_unramified_iff_tensorProduct_unramified
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is unramified exactly when all finite and infinite
completed scalar extensions are unramified. -/
theorem rationalFunction_algebra_unramified_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Unramified (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.Unramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_unramified_iff_tensorProduct_unramified
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_unramified_iff_tensorProduct_unramified
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A commutative algebra over a number field is étale exactly when all completed scalar
extensions are étale. -/
theorem numberField_algebra_etale_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Etale K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.Etale (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_etale_iff_tensorProduct_etale (L := completion K p)).mp h
  · intro h
    exact (algebra_etale_iff_tensorProduct_etale
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is étale exactly when all finite and infinite completed
scalar extensions are étale. -/
theorem rationalFunction_algebra_etale_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Etale (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.Etale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_etale_iff_tensorProduct_etale
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_etale_iff_tensorProduct_etale
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- A commutative algebra over a number field is finite étale exactly when all completed scalar
extensions are finite étale. -/
theorem numberField_algebra_finiteEtale_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FiniteEtale K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.FiniteEtale (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (Algebra.finiteEtale_iff_tensorProduct (L := completion K p)).mp h
  · intro h
    exact (Algebra.finiteEtale_iff_tensorProduct
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is finite étale exactly when all finite and infinite
completed scalar extensions are finite étale. -/
theorem rationalFunction_algebra_finiteEtale_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FiniteEtale (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.FiniteEtale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (Algebra.finiteEtale_iff_tensorProduct
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (Algebra.finiteEtale_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- Smoothness of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_smooth_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Smooth K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.Smooth (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_smooth_iff_tensorProduct_smooth
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_smooth_iff_tensorProduct_smooth (L := completion K p)).mpr hp

/-- Smoothness of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_smooth_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Smooth (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.Smooth (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_smooth_iff_tensorProduct_smooth
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_smooth_iff_tensorProduct_smooth
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Unramifiedness of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_unramified_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Unramified K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.Unramified (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_unramified_iff_tensorProduct_unramified
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_unramified_iff_tensorProduct_unramified (L := completion K p)).mpr hp

/-- Unramifiedness of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_unramified_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Unramified (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.Unramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_unramified_iff_tensorProduct_unramified
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_unramified_iff_tensorProduct_unramified
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Étaleness of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_etale_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.Etale K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.Etale (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_etale_iff_tensorProduct_etale
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_etale_iff_tensorProduct_etale (L := completion K p)).mpr hp

/-- Étaleness of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_etale_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.Etale (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.Etale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_etale_iff_tensorProduct_etale
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_etale_iff_tensorProduct_etale
      (L := rationalFunctionCompletion F p)).mpr hp

/-- Finite étaleness of a number-field algebra can be certified at one completion. -/
theorem numberField_algebra_finiteEtale_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FiniteEtale K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.FiniteEtale (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (Algebra.finiteEtale_iff_tensorProduct
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (Algebra.finiteEtale_iff_tensorProduct (L := completion K p)).mpr hp

/-- Finite étaleness of an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_algebra_finiteEtale_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FiniteEtale (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.FiniteEtale (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (Algebra.finiteEtale_iff_tensorProduct
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (Algebra.finiteEtale_iff_tensorProduct
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
