import GaloisForLFunctions.HTGeometry.DifferentialObservableGaugeInvariance
import GaloisForLFunctions.HTGeometry.UniversalPrimeKreinHamming

/-!
# Dephasing energy faithfully enriches the prime-chamber observable field

All finite prime-residue chambers of the universal source have the same finite field of
observables because they differ by rational base gauges.  This blindness has a nontrivial positive
residue: the independent-dephasing master energy on the same chambers recovers their complete
Hamming geometry.

Thus the energy-enriched observable object is faithful even though its field component is
constant.  The construction is static and constraint-based; no temporal evolution is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- Every finite prime-residue chamber has the same observable field as the universal source at
every resolution vector. -/
theorem universalFacetOrbitPrimeOrientedSource_familyObservableField_eq
    (J : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitPrimeOrientedSource J) N =
      differentialFamilyObservableField (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge) N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let base := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
    universalFacetOrbitGauge
  let correction : UniversalFacetOrbitIndex → upperEndMeroField := fun q =>
    algebraMap (RatFunc ℂ) upperEndMeroField
      (universalPrimeOrientedPaletteGauge J q)
  have h := differentialFamilyObservableField_addOfJetsInBase_eq base correction
    (fun q n => upperEndRatfunc_allJets_closed
      (universalPrimeOrientedPaletteGauge J q) n) N
  simpa [base, correction, universalFacetOrbitPrimeOrientedSource,
    universalFacetOrbitRationalGaugeSource] using h

/-- Any two finite prime-residue chambers have exactly the same observable field at every
resolution. -/
theorem universalPrimeChambers_familyObservableField_eq
    (J L : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitPrimeOrientedSource J) N =
      differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitPrimeOrientedSource L) N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact (universalFacetOrbitPrimeOrientedSource_familyObservableField_eq J N).trans
    (universalFacetOrbitPrimeOrientedSource_familyObservableField_eq L N).symm

/-- **Positive residue of observable blindness.**  The field component is constant, but the
dephasing master energy is exactly the Hamming distance and vanishes exactly on equal chambers. -/
theorem universalPrimeChamber_energyEnrichedObservableGeometry
    (J L : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource J) N =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource L) N ∧
      primeChamberDephasingMasterEnergy J L =
        (primeChamberHammingDistance J L : ℝ) ∧
      (primeChamberDephasingMasterEnergy J L = 0 ↔ J = L) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact ⟨universalPrimeChambers_familyObservableField_eq J L N,
    primeChamberDephasingMasterEnergy_eq_hamming J L,
    primeChamberDephasingMasterEnergy_eq_zero_iff J L⟩

/-- Equality of energy-enriched observable data is faithful on the complete finite chamber
family: the common field together with zero relative energy identifies the chamber exactly. -/
theorem universalPrimeChamber_energyEnrichedObservable_eq_iff
    (J L : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    (differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource J) N =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource L) N ∧
      primeChamberDephasingMasterEnergy J L = 0) ↔ J = L := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  constructor
  · exact fun h => (primeChamberDephasingMasterEnergy_eq_zero_iff J L).mp h.2
  · intro hJL
    subst L
    exact ⟨rfl, (primeChamberDephasingMasterEnergy_eq_zero_iff J J).mpr rfl⟩

/-- Against the all-positive chamber, the same dephasing energy that faithfully enriches the
observable field also discharges the global Herglotz condition. -/
theorem universalPrimeChamber_sameObservableField_while_Herglotz_iff_energy_zero
    (J : Finset Nat.Primes) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource J) N =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitPrimeOrientedSource ∅) N ∧
      ((∀ z : ℂ, 0 < z.im → 0 ≤ (universalPrimeOrientedHerglotz J z).im) ↔
        primeChamberDephasingMasterEnergy J ∅ = 0) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact ⟨universalPrimeChambers_familyObservableField_eq J ∅ N,
    universalPrimeOrientedHerglotz_nonneg_iff_dephasingMasterEnergy_eq_zero J⟩

end

end GaloisForLFunctions.HTGeometry
