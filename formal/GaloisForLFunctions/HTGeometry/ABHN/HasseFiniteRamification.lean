/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.Places
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Finite ramification in Dedekind and number-field extensions

For a finite separable extension of Dedekind domains, ramified height-one primes are exactly the
prime divisors of its relative different ideal, hence form a finite set. The finite places of every
finite separable number-field extension are an immediate instance. The special case `ℚ ⊂ K` is
also exposed directly.

This is the geometric finiteness mechanism needed by the finite-ramification component of the
Albert--Brauer--Hasse--Noether sequence. It concerns number-field extensions themselves; the
remaining Brauer-theoretic bridge is to produce an Azumaya order for a central simple algebra away
from finitely many places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped NumberField

universe u v

noncomputable section

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
  [Algebra A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [Module.Finite A B]

local instance : Algebra (FractionRing A) (FractionRing B) :=
  FractionRing.liftAlgebra A (FractionRing B)

/-- In a finite separable extension of Dedekind domains, ramified height-one primes are exactly
the prime divisors of the relative different. -/
theorem ramifiedHeightOneSpectrum_eq_differentFactors_of_separable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    {P : IsDedekindDomain.HeightOneSpectrum B |
      ¬ Algebra.IsUnramifiedAt A P.asIdeal} =
      {P : IsDedekindDomain.HeightOneSpectrum B | P.asIdeal ∣ differentIdeal A B} := by
  ext P
  exact dvd_differentIdeal_iff.symm

/-- A finite separable extension of Dedekind domains ramifies at only finitely many height-one
primes. -/
theorem finite_ramifiedHeightOneSpectrum_of_separable
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)] :
    {P : IsDedekindDomain.HeightOneSpectrum B |
      ¬ Algebra.IsUnramifiedAt A P.asIdeal}.Finite := by
  have h : {P : IsDedekindDomain.HeightOneSpectrum B |
      P.asIdeal ∣ differentIdeal A B}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  rw [ramifiedHeightOneSpectrum_eq_differentFactors_of_separable]
  exact h

end

/-- At a finite place of a separable number-field extension, ramification is exactly divisibility
by the relative different. -/
theorem numberFieldExtension_ramifiedFinitePlaces_eq_differentFactors
    {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    {w : NumberField.FinitePlace L |
      ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal} =
    (NumberField.FinitePlace.maximalIdeal ⁻¹'
      {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
        P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}) := by
  ext w
  exact Set.ext_iff.mp
    (ramifiedHeightOneSpectrum_eq_differentFactors_of_separable (A := 𝓞 K) (B := 𝓞 L)) _

/-- Only finitely many primes of a finite separable number-field extension ramify. -/
theorem numberFieldExtension_finite_ramifiedPrimes
    {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      ¬ Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal}.Finite := by
  exact finite_ramifiedHeightOneSpectrum_of_separable (A := 𝓞 K) (B := 𝓞 L)

/-- Only finitely many finite places of a finite separable number-field extension ramify. -/
theorem numberFieldExtension_finite_ramifiedFinitePlaces
    {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    {w : NumberField.FinitePlace L |
      ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal}.Finite := by
  have h : {P : IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
      P.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  have h_inj : Set.InjOn NumberField.FinitePlace.maximalIdeal
      {w : NumberField.FinitePlace L |
        ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal} :=
    Function.Injective.injOn NumberField.FinitePlace.maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_differentIdeal_iff, Set.image_subset_iff, Set.preimage_setOf_eq, subset_refl]

/-- Ramified finite places of a separable number-field extension form a finite subset of the
full ABHN place type. -/
theorem numberFieldExtension_finite_ramifiedPlaces
    {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    {p : NumberFieldPlace L | match p with
      | .finite w => ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal
      | .infinite _ => False}.Finite := by
  let s : Set (NumberField.FinitePlace L) :=
    {w | ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal}
  have hs : s.Finite := numberFieldExtension_finite_ramifiedFinitePlaces
  have heq : {p : NumberFieldPlace L | match p with
      | .finite w => ¬ Algebra.IsUnramifiedAt (𝓞 K) w.maximalIdeal.asIdeal
      | .infinite _ => False} = NumberFieldPlace.finite '' s := by
    ext p
    cases p <;> simp [s]
  rw [heq]
  exact hs.image NumberFieldPlace.finite

/-- At a finite place of a number field, ramification is exactly divisibility by the different. -/
theorem numberField_ramifiedFinitePlaces_eq_differentFactors (K : Type u) [Field K]
    [NumberField K] :
    {w : NumberField.FinitePlace K |
      ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal} =
    (NumberField.FinitePlace.maximalIdeal ⁻¹'
      {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
        v.asIdeal ∣ differentIdeal ℤ (𝓞 K)}) := by
  ext w
  exact dvd_differentIdeal_iff.symm

/-- Only finitely many finite places of a number field ramify over `ℤ`. -/
theorem numberField_finite_ramifiedFinitePlaces (K : Type u) [Field K] [NumberField K] :
    {w : NumberField.FinitePlace K |
      ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal}.Finite := by
  have h : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      v.asIdeal ∣ differentIdeal ℤ (𝓞 K)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  have h_inj : Set.InjOn NumberField.FinitePlace.maximalIdeal
      {w : NumberField.FinitePlace K | ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal} :=
    Function.Injective.injOn NumberField.FinitePlace.maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_differentIdeal_iff, Set.image_subset_iff, Set.preimage_setOf_eq, subset_refl]

/-- The ramified finite places form a finite subset of the full ABHN place type; its infinite
places are empty by definition. -/
theorem numberField_finite_ramifiedPlaces (K : Type u) [Field K] [NumberField K] :
    {p : NumberFieldPlace K | match p with
      | .finite w => ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal
      | .infinite _ => False}.Finite := by
  let s : Set (NumberField.FinitePlace K) :=
    {w | ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal}
  have hs : s.Finite := numberField_finite_ramifiedFinitePlaces K
  have heq : {p : NumberFieldPlace K | match p with
      | .finite w => ¬ Algebra.IsUnramifiedAt ℤ w.maximalIdeal.asIdeal
      | .infinite _ => False} = NumberFieldPlace.finite '' s := by
    ext p
    cases p <;> simp [s]
  rw [heq]
  exact hs.image NumberFieldPlace.finite

end

end GaloisForLFunctions.HTGeometry.ABHN
