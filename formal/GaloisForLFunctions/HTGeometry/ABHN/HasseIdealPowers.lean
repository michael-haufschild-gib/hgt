/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HasseIdealCoprime

/-!
# Hasse detection for ideal powers

Extension along a field commutes with ideal powers, while faithful flatness reflects equality.
Thus fixed ideal-power relations, idempotence, and nilpotence can be checked at every completion.
This detects prescribed infinitesimal thickenings; it does not assert that radicality ascends under
arbitrary scalar extension.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u v w

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A fixed ideal-power equality is reflected by tensoring a commutative algebra along a field
extension. -/
theorem ideal_pow_eq_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]
    (I J : Ideal A) (n : ℕ) :
    I ^ n = J ↔ I.map (algebraMap A (L ⊗[K] A)) ^ n = J.map (algebraMap A (L ⊗[K] A)) := by
  rw [← Ideal.map_pow]
  exact (ideal_map_eq_iff_tensorProduct (L := L) (I ^ n) J).symm

/-- Idempotence of an ideal is reflected by tensoring a commutative algebra along a field
extension. -/
theorem ideal_isIdempotentElem_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A) :
    IsIdempotentElem I ↔ IsIdempotentElem (I.map (algebraMap A (L ⊗[K] A))) := by
  change I * I = I ↔ I.map (algebraMap A (L ⊗[K] A)) *
    I.map (algebraMap A (L ⊗[K] A)) = I.map (algebraMap A (L ⊗[K] A))
  simpa only [pow_two] using ideal_pow_eq_iff_tensorProduct (L := L) I I 2

/-- Nilpotence of an ideal is reflected by tensoring a commutative algebra along a field
extension. -/
theorem ideal_isNilpotent_iff_tensorProduct {K : Type u} {L : Type v} {A : Type w}
    [Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A] (I : Ideal A) :
    IsNilpotent I ↔ IsNilpotent (I.map (algebraMap A (L ⊗[K] A)) : Ideal (L ⊗[K] A)) := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using (ideal_pow_eq_iff_tensorProduct (L := L) I (⊥ : Ideal A) n).mp hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    exact (ideal_pow_eq_iff_tensorProduct (L := L) I (⊥ : Ideal A) n).mpr (by simpa using hn)

/-- An ideal-power equality in a commutative number-field algebra holds exactly when it holds at
every completed place. -/
theorem numberField_ideal_pow_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (I J : Ideal A) (n : ℕ) :
    I ^ n = J ↔ ∀ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ^ n =
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h p
    exact (ideal_pow_eq_iff_tensorProduct (L := completion K p) I J n).mp h
  · intro h
    exact (ideal_pow_eq_iff_tensorProduct (L := completion K (witnessPlace K)) I J n).mpr
      (h (witnessPlace K))

/-- An ideal-power equality in a commutative `F(t)`-algebra holds exactly when it holds at every
finite and infinite completed place. -/
theorem rationalFunction_ideal_pow_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (I J : Ideal A) (n : ℕ) :
    I ^ n = J ↔ ∀ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ^ n =
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h p
    exact (ideal_pow_eq_iff_tensorProduct (L := rationalFunctionCompletion F p) I J n).mp h
  · intro h
    exact (ideal_pow_eq_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I J n).mpr (h .infinite)

/-- An ideal in a commutative number-field algebra is idempotent exactly when its extension is
idempotent at every completed place. -/
theorem numberField_ideal_isIdempotentElem_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    IsIdempotentElem I ↔ ∀ p : NumberFieldPlace K,
      IsIdempotentElem (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  constructor
  · intro h p
    exact (ideal_isIdempotentElem_iff_tensorProduct (L := completion K p) I).mp h
  · intro h
    exact (ideal_isIdempotentElem_iff_tensorProduct (L := completion K (witnessPlace K)) I).mpr
      (h (witnessPlace K))

/-- An ideal in a commutative `F(t)`-algebra is idempotent exactly when its extension is
idempotent at every finite and infinite completed place. -/
theorem rationalFunction_ideal_isIdempotentElem_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    IsIdempotentElem I ↔ ∀ p : RationalFunctionPlace F,
      IsIdempotentElem (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  constructor
  · intro h p
    exact (ideal_isIdempotentElem_iff_tensorProduct (L := rationalFunctionCompletion F p) I).mp h
  · intro h
    exact (ideal_isIdempotentElem_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I).mpr (h .infinite)

/-- An ideal in a commutative number-field algebra is nilpotent exactly when its extension is
nilpotent at every completed place. -/
theorem numberField_ideal_isNilpotent_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    IsNilpotent I ↔ ∀ p : NumberFieldPlace K,
      IsNilpotent (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  constructor
  · intro h p
    exact (ideal_isNilpotent_iff_tensorProduct (L := completion K p) I).mp h
  · intro h
    exact (ideal_isNilpotent_iff_tensorProduct (L := completion K (witnessPlace K)) I).mpr
      (h (witnessPlace K))

/-- An ideal in a commutative `F(t)`-algebra is nilpotent exactly when its extension is nilpotent
at every finite and infinite completed place. -/
theorem rationalFunction_ideal_isNilpotent_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    IsNilpotent I ↔ ∀ p : RationalFunctionPlace F,
      IsNilpotent (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  constructor
  · intro h p
    exact (ideal_isNilpotent_iff_tensorProduct (L := rationalFunctionCompletion F p) I).mp h
  · intro h
    exact (ideal_isNilpotent_iff_tensorProduct
      (L := rationalFunctionCompletion F .infinite) I).mpr (h .infinite)

/-- A fixed ideal-power relation in a number-field algebra can be certified at one completion. -/
theorem numberField_ideal_pow_eq_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A]
    (I J : Ideal A) (n : ℕ) :
    I ^ n = J ↔ ∃ p : NumberFieldPlace K,
      I.map (algebraMap A (completion K p ⊗[K] A)) ^ n =
        J.map (algebraMap A (completion K p ⊗[K] A)) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (ideal_pow_eq_iff_tensorProduct (L := completion K (witnessPlace K)) I J n).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_pow_eq_iff_tensorProduct (L := completion K p) I J n).mpr hp

/-- A fixed ideal-power relation in an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_ideal_pow_eq_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A]
    (I J : Ideal A) (n : ℕ) :
    I ^ n = J ↔ ∃ p : RationalFunctionPlace F,
      I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) ^ n =
        J.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A)) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (ideal_pow_eq_iff_tensorProduct
        (L := rationalFunctionCompletion F .infinite) I J n).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_pow_eq_iff_tensorProduct (L := rationalFunctionCompletion F p) I J n).mpr hp

/-- Idempotence of an ideal in a number-field algebra can be certified at one completion. -/
theorem numberField_ideal_isIdempotentElem_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    IsIdempotentElem I ↔ ∃ p : NumberFieldPlace K,
      IsIdempotentElem (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (ideal_isIdempotentElem_iff_tensorProduct
        (L := completion K (witnessPlace K)) I).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_isIdempotentElem_iff_tensorProduct (L := completion K p) I).mpr hp

/-- Idempotence of an ideal in an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_ideal_isIdempotentElem_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    IsIdempotentElem I ↔ ∃ p : RationalFunctionPlace F,
      IsIdempotentElem (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (ideal_isIdempotentElem_iff_tensorProduct
        (L := rationalFunctionCompletion F .infinite) I).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_isIdempotentElem_iff_tensorProduct
      (L := rationalFunctionCompletion F p) I).mpr hp

/-- Nilpotence of an ideal in a number-field algebra can be certified at one completion. -/
theorem numberField_ideal_isNilpotent_iff_exists_place (K : Type u)
    [Field K] [NumberField K] {A : Type w} [CommRing A] [Algebra K A] (I : Ideal A) :
    IsNilpotent I ↔ ∃ p : NumberFieldPlace K,
      IsNilpotent (I.map (algebraMap A (completion K p ⊗[K] A))) := by
  constructor
  · intro h
    exact ⟨witnessPlace K,
      (ideal_isNilpotent_iff_tensorProduct (L := completion K (witnessPlace K)) I).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_isNilpotent_iff_tensorProduct (L := completion K p) I).mpr hp

/-- Nilpotence of an ideal in an `F(t)`-algebra can be certified at one completion. -/
theorem rationalFunction_ideal_isNilpotent_iff_exists_place (F : Type u)
    [Field F] [Finite F] {A : Type w} [CommRing A] [Algebra (RatFunc F) A] (I : Ideal A) :
    IsNilpotent I ↔ ∃ p : RationalFunctionPlace F,
      IsNilpotent (I.map (algebraMap A (rationalFunctionCompletion F p ⊗[RatFunc F] A))) := by
  constructor
  · intro h
    exact ⟨.infinite,
      (ideal_isNilpotent_iff_tensorProduct
        (L := rationalFunctionCompletion F .infinite) I).mp h⟩
  · rintro ⟨p, hp⟩
    exact (ideal_isNilpotent_iff_tensorProduct
      (L := rationalFunctionCompletion F p) I).mpr hp

end GaloisForLFunctions.HTGeometry.ABHN
