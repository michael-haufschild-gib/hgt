/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaScalarExtension
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Azumaya models at primes outside a principal divisor

An Azumaya algebra over a principal open subset base-changes to an Azumaya algebra at every
prime outside its defining divisor.  This is the local-ring form of the finite-ramification
bridge, independent of the later comparison with completed local Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- An Azumaya algebra over `R[1/d]` remains Azumaya after base change to the local ring at any
prime ideal not containing `d`. -/
theorem isAzumaya_scalarExtension_atPrime_of_not_mem
    (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime] (d : R) (hd : d ∉ P)
    (B : Type v) [Ring B] [Algebra (Localization (Submonoid.powers d)) B]
    [IsAzumaya (Localization (Submonoid.powers d)) B] :
    let T := Localization (Submonoid.powers d)
    let Q := Localization.AtPrime P
    let f : T →+* Q := IsLocalization.Away.lift d
      (IsLocalization.map_units Q ⟨d, show d ∈ P.primeCompl from hd⟩)
    letI : Algebra T Q := f.toAlgebra
    IsAzumaya Q (Q ⊗[T] B) := by
  let T := Localization (Submonoid.powers d)
  let Q := Localization.AtPrime P
  have hunit : IsUnit (algebraMap R Q d) :=
    IsLocalization.map_units Q ⟨d, show d ∈ P.primeCompl from hd⟩
  let f : T →+* Q := IsLocalization.Away.lift d hunit
  letI : Algebra T Q := f.toAlgebra
  exact AzumayaScalarExtension.isAzumaya_scalarExtension (R := T) (S := Q) (A := B)

/-- At a height-one prime outside both principal divisors of a two-stage model, the associated
single-principal Azumaya algebra remains Azumaya after base change to the local ring. -/
theorem isAzumaya_scalarExtension_atHeightOne_of_not_twoPrincipalDivisors
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (r a : R)
    (hP : ¬ (P.asIdeal ∣ Ideal.span ({r} : Set R) ∨
      P.asIdeal ∣ Ideal.span ({a} : Set R)))
    (B : Type v) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B] :
    let T := Localization (Submonoid.powers (r * a))
    let Q := Localization.AtPrime P.asIdeal
    let f : T →+* Q := IsLocalization.Away.lift (r * a)
      (IsLocalization.map_units Q ⟨r * a, show r * a ∈ P.asIdeal.primeCompl from by
        intro hra
        apply hP
        rcases P.isPrime.mem_or_mem hra with hr | ha
        · exact Or.inl (Ideal.dvd_span_singleton.mpr hr)
        · exact Or.inr (Ideal.dvd_span_singleton.mpr ha)⟩)
    letI : Algebra T Q := f.toAlgebra
    IsAzumaya Q (Q ⊗[T] B) := by
  have hd : r * a ∉ P.asIdeal := by
    intro hra
    apply hP
    rcases P.isPrime.mem_or_mem hra with hr | ha
    · exact Or.inl (Ideal.dvd_span_singleton.mpr hr)
    · exact Or.inr (Ideal.dvd_span_singleton.mpr ha)
  exact isAzumaya_scalarExtension_atPrime_of_not_mem R P.asIdeal (r * a) hd B

end GaloisForLFunctions.HTGeometry.ABHN
