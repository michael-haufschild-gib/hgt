/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.PrincipalOpenAzumayaAtPrime
import GaloisForLFunctions.HTGeometry.DedekindResidueFieldAtPlace

/-!
# Azumaya models over height-one valuation subrings

The local ring at a height-one prime of a Dedekind domain is identified with the corresponding
valuation subring of the fraction field.  This module transports principal-open Azumaya models
across that identification, reaching the DVR layer used by finite-residue arguments.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open IsDedekindDomain

universe u v

/-- Outside the two principal divisors of a global Azumaya witness, its local-ring model
base-changes to an Azumaya algebra over the corresponding height-one valuation subring. -/
theorem isAzumaya_scalarExtension_toValuationSubringAtHeightOne_of_not_twoPrincipalDivisors
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (r a : R)
    (hP : ¬ (P.asIdeal ∣ Ideal.span ({r} : Set R) ∨
      P.asIdeal ∣ Ideal.span ({a} : Set R)))
    (B : Type v) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B] :
    let T := Localization (Submonoid.powers (r * a))
    let Q := Localization.AtPrime P.asIdeal
    let W := ((P.valuation K).valuationSubring)
    let f : T →+* Q := IsLocalization.Away.lift (r * a)
      (IsLocalization.map_units Q ⟨r * a, show r * a ∈ P.asIdeal.primeCompl from by
        intro hra
        apply hP
        rcases P.isPrime.mem_or_mem hra with hr | ha
        · exact Or.inl (Ideal.dvd_span_singleton.mpr hr)
        · exact Or.inr (Ideal.dvd_span_singleton.mpr ha)⟩)
    letI : Algebra T Q := f.toAlgebra
    letI : Semiring (Q ⊗[T] B) := inferInstance
    letI : Algebra Q (Q ⊗[T] B) := inferInstance
    letI : IsAzumaya Q (Q ⊗[T] B) :=
      isAzumaya_scalarExtension_atHeightOne_of_not_twoPrincipalDivisors R P r a hP B
    let e : Q ≃+* W :=
      (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P).toRingEquiv.trans
        (GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P)
    letI : Algebra Q W := e.toRingHom.toAlgebra
    IsAzumaya W (W ⊗[Q] (Q ⊗[T] B)) := by
  let T := Localization (Submonoid.powers (r * a))
  let Q := Localization.AtPrime P.asIdeal
  let W := ((P.valuation K).valuationSubring)
  have hd : r * a ∉ P.asIdeal := by
    intro hra
    apply hP
    rcases P.isPrime.mem_or_mem hra with hr | ha
    · exact Or.inl (Ideal.dvd_span_singleton.mpr hr)
    · exact Or.inr (Ideal.dvd_span_singleton.mpr ha)
  have hunit : IsUnit (algebraMap R Q (r * a)) :=
    IsLocalization.map_units Q ⟨r * a, show r * a ∈ P.asIdeal.primeCompl from hd⟩
  let f : T →+* Q := IsLocalization.Away.lift (r * a) hunit
  letI : Algebra T Q := f.toAlgebra
  letI : Semiring (Q ⊗[T] B) := inferInstance
  letI : Algebra Q (Q ⊗[T] B) := inferInstance
  letI : IsAzumaya Q (Q ⊗[T] B) :=
    isAzumaya_scalarExtension_atHeightOne_of_not_twoPrincipalDivisors R P r a hP B
  let e : Q ≃+* W :=
    (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P).toRingEquiv.trans
      (GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P)
  letI : Algebra Q W := e.toRingHom.toAlgebra
  exact AzumayaScalarExtension.isAzumaya_scalarExtension
    (R := Q) (S := W) (A := Q ⊗[T] B)

end GaloisForLFunctions.HTGeometry.ABHN
