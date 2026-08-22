/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseGeometricProperties

/-!
# Hasse detection for formally unramified algebras

Formal unramifiedness descends along faithfully flat scalar extension.  Therefore it is detected
by the completed scalar extensions of a commutative algebra over either global field model.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

/-- Formal unramifiedness of a commutative algebra is reflected by every field scalar extension. -/
theorem algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
    {K : Type u} {L : Type v} {A : Type w} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] :
    Algebra.FormallyUnramified K A ↔ Algebra.FormallyUnramified L (L ⊗[K] A) := by
  constructor
  · intro h
    letI := h
    infer_instance
  · intro h
    letI := h
    exact Algebra.FormallyUnramified.of_formallyUnramified_tensorProduct_of_faithfullyFlat L

/-- A commutative algebra over a number field is formally unramified exactly when all completed
scalar extensions are formally unramified. -/
theorem numberField_algebra_formallyUnramified_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FormallyUnramified K A ↔ ∀ p : NumberFieldPlace K,
      Algebra.FormallyUnramified (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h p
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := completion K p)).mp h
  · intro h
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := completion K (witnessPlace K))).mpr (h (witnessPlace K))

/-- A commutative algebra over `F(t)` is formally unramified exactly when all finite and infinite
completed scalar extensions are formally unramified. -/
theorem rationalFunction_algebra_formallyUnramified_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FormallyUnramified (RatFunc F) A ↔ ∀ p : RationalFunctionPlace F,
      Algebra.FormallyUnramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h p
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := rationalFunctionCompletion F p)).mp h
  · intro h
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := rationalFunctionCompletion F .infinite)).mpr (h .infinite)

/-- Formal unramifiedness of a fixed number-field algebra is certified at one completion. -/
theorem numberField_algebra_formallyUnramified_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] :
    Algebra.FormallyUnramified K A ↔ ∃ p : NumberFieldPlace K,
      Algebra.FormallyUnramified (completion K p) (completion K p ⊗[K] A) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
        (L := completion K (witnessPlace K))).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := completion K p)).mpr hp

/-- Formal unramifiedness of a fixed `F(t)`-algebra is certified at one completion. -/
theorem rationalFunction_algebra_formallyUnramified_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] :
    Algebra.FormallyUnramified (RatFunc F) A ↔ ∃ p : RationalFunctionPlace F,
      Algebra.FormallyUnramified (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] A) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
        (L := rationalFunctionCompletion F .infinite)).mp h⟩
  · rintro ⟨p, hp⟩
    exact (algebra_formallyUnramified_iff_tensorProduct_formallyUnramified
      (L := rationalFunctionCompletion F p)).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
