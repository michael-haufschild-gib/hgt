/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaHeightOneValuationResidue
import GaloisForLFunctions.HTGeometry.ABHN.PrincipalOpenFinitePlaces

/-!
# Finite exceptional support for Azumaya residue fibers

An Azumaya algebra over the two-principal localization `R[1 / (r * a)]` has a split residue
Brauer fiber at every height-one valuation subring outside the divisors of `r` and `a`.  This
packages that pointwise statement with its finite exceptional set.  It is the finite-ramification
residue-fiber layer of ABHN; it does not identify these residue classes with the Brauer classes of
the completed fraction fields.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped NumberField Polynomial TensorProduct

universe u

/-- The two height-one divisor sets which can obstruct the residue-fiber construction for a
two-principal Azumaya model. -/
def twoPrincipalOpenAzumayaResidueBadHeightOnePrimes
    (R : Type u) [CommRing R] (r a : R) : Set (HeightOneSpectrum R) :=
  {P | P.asIdeal ∣ Ideal.span ({r} : Set R) ∨ P.asIdeal ∣ Ideal.span ({a} : Set R)}

/-- The exceptional height-one support of a two-principal Azumaya model is finite. -/
theorem finite_twoPrincipalOpenAzumayaResidueBadHeightOnePrimes
    (R : Type u) [CommRing R] [IsDedekindDomain R] (r a : R)
    (hr : r ≠ 0) (ha : a ≠ 0) :
    (twoPrincipalOpenAzumayaResidueBadHeightOnePrimes R r a).Finite := by
  have hrfin : {P : HeightOneSpectrum R | P.asIdeal ∣ Ideal.span ({r} : Set R)}.Finite :=
    finite_heightOneSpectrum_divisors_span_singleton R r hr
  have hafin : {P : HeightOneSpectrum R | P.asIdeal ∣ Ideal.span ({a} : Set R)}.Finite :=
    finite_heightOneSpectrum_divisors_span_singleton R a ha
  have heq : twoPrincipalOpenAzumayaResidueBadHeightOnePrimes R r a =
      {P : HeightOneSpectrum R | P.asIdeal ∣ Ideal.span ({r} : Set R)} ∪
        {P : HeightOneSpectrum R | P.asIdeal ∣ Ideal.span ({a} : Set R)} := by
    ext P
    simp [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes]
  rw [heq]
  exact hrfin.union hafin

/-- The residue Brauer class attached to a two-principal Azumaya model at a good height-one
valuation subring. -/
noncomputable def twoPrincipalOpenAzumayaHeightOneResidueBrauerClass
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (r a : R)
    (hP : ¬ (P.asIdeal ∣ Ideal.span ({r} : Set R) ∨
      P.asIdeal ∣ Ideal.span ({a} : Set R)))
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B] :
    BrauerGroup (IsLocalRing.ResidueField ((P.valuation K).valuationSubring)) := by
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
  letI : IsAzumaya W (W ⊗[Q] (Q ⊗[T] B)) :=
    isAzumaya_scalarExtension_toValuationSubringAtHeightOne_of_not_twoPrincipalDivisors
      R K P r a hP B
  exact azumayaScalarExtensionBrauerClass W (IsLocalRing.ResidueField W)
    (W ⊗[Q] (Q ⊗[T] B))

/-- At every good height-one prime with finite residue field, the residue Brauer class of a
two-principal Azumaya model is split. -/
theorem twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (r a : R)
    (hP : ¬ (P.asIdeal ∣ Ideal.span ({r} : Set R) ∨
      P.asIdeal ∣ Ideal.span ({a} : Set R)))
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B]
    [Finite (IsLocalRing.ResidueField ((P.valuation K).valuationSubring))] :
    twoPrincipalOpenAzumayaHeightOneResidueBrauerClass R K P r a hP B =
      brauerSplitClass (IsLocalRing.ResidueField ((P.valuation K).valuationSubring)) := by
  exact azumayaResidueBrauerClass_toValuationSubringAtHeightOne_eq_split R K P r a hP B

/-- Outside the finite two-divisor exceptional support, every height-one residue fiber of a
two-principal Azumaya model is split. -/
theorem twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (r a : R)
    (hP : P ∉ twoPrincipalOpenAzumayaResidueBadHeightOnePrimes R r a)
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B]
    [Finite (IsLocalRing.ResidueField ((P.valuation K).valuationSubring))] :
    twoPrincipalOpenAzumayaHeightOneResidueBrauerClass R K P r a
        (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B =
      brauerSplitClass (IsLocalRing.ResidueField ((P.valuation K).valuationSubring)) := by
  exact twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split R K P r a
    (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B

/-- The finite-residue Hasse support statement for a two-principal Azumaya model over the ring
of integers of a number field. -/
theorem numberField_twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    (K : Type u) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (r a : 𝓞 K)
    (hP : P ∉ twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (𝓞 K) r a)
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B] :
    twoPrincipalOpenAzumayaHeightOneResidueBrauerClass (𝓞 K) K P r a
        (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B =
      brauerSplitClass (IsLocalRing.ResidueField ((P.valuation K).valuationSubring)) := by
  exact twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    (𝓞 K) K P r a hP B

/-- The finite-residue Hasse support statement for a two-principal Azumaya model over `F[X]`.
It covers every finite place of the global function field `F(t)` outside its finite divisor set. -/
theorem rationalFunction_twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    (F : Type u) [Field F] [Finite F]
    (P : HeightOneSpectrum F[X]) (r a : F[X])
    (hP : P ∉ twoPrincipalOpenAzumayaResidueBadHeightOnePrimes F[X] r a)
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers (r * a))) B]
    [IsAzumaya (Localization (Submonoid.powers (r * a))) B] :
    twoPrincipalOpenAzumayaHeightOneResidueBrauerClass F[X] (RatFunc F) P r a
        (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B =
      brauerSplitClass (IsLocalRing.ResidueField ((P.valuation (RatFunc F)).valuationSubring)) := by
  exact twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    F[X] (RatFunc F) P r a hP B

end GaloisForLFunctions.HTGeometry.ABHN
