/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaHeightOneValuationSubring
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaFiniteResidueFiber

/-!
# Split residue fibers of height-one Azumaya models

Outside the two principal divisors of a global Azumaya witness, its model reaches the height-one
valuation subring.  If that valuation subring has finite residue field, the resulting residue
Brauer class is split.  This is not a comparison with the completed generic fiber.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open IsDedekindDomain

universe u

/-- At a height-one valuation subring with finite residue field, the residue fiber of the
principal-open Azumaya model is split outside its two exceptional divisors. -/
theorem azumayaResidueBrauerClass_toValuationSubringAtHeightOne_eq_split
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (r a : R)
    (hP : ¬ (P.asIdeal ∣ Ideal.span ({r} : Set R) ∨
      P.asIdeal ∣ Ideal.span ({a} : Set R)))
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B]
    [Finite (IsLocalRing.ResidueField ((P.valuation K).valuationSubring))] :
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
    letI : Semiring (W ⊗[Q] (Q ⊗[T] B)) := inferInstance
    letI : Algebra W (W ⊗[Q] (Q ⊗[T] B)) := inferInstance
    letI : IsAzumaya W (W ⊗[Q] (Q ⊗[T] B)) :=
      isAzumaya_scalarExtension_toValuationSubringAtHeightOne_of_not_twoPrincipalDivisors
        R K P r a hP B
    azumayaScalarExtensionBrauerClass W (IsLocalRing.ResidueField W)
      (W ⊗[Q] (Q ⊗[T] B)) = brauerSplitClass (IsLocalRing.ResidueField W) := by
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
  letI : Semiring (W ⊗[Q] (Q ⊗[T] B)) := inferInstance
  letI : Algebra W (W ⊗[Q] (Q ⊗[T] B)) := inferInstance
  letI : IsAzumaya W (W ⊗[Q] (Q ⊗[T] B) ) :=
    isAzumaya_scalarExtension_toValuationSubringAtHeightOne_of_not_twoPrincipalDivisors
      R K P r a hP B
  exact azumayaResidueBrauerClass_eq_split W (W ⊗[Q] (Q ⊗[T] B))

end GaloisForLFunctions.HTGeometry.ABHN
