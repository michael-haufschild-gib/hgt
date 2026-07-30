import GaloisForLFunctions.HTGeometry.DifferentialObservableGaugeInvariance
import GaloisForLFunctions.HTGeometry.UniversalOrientedConstraintProduct

/-!
# Universal oriented HT observables are rational-gauge blind

Every finite orientation chamber of the universal prime-log source is obtained by adding a
coordinatewise rational gauge.  Since all jets of the rational correction remain in the
coefficient field, every finite clock-observable field is identical across all chambers.

The analytic orientation is not identical: Herglotz positivity holds exactly in the chamber of
orientation index zero.  Thus the bare field-valued observable net cannot recover the positive
orientation.  A source-sensitive refinement must retain ordered, positive-cone, or state data in
addition to the observable field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

/-- Arbitrary coordinatewise rational gauges preserve every finite observable field of the
universal facet source. -/
theorem universalFacetOrbitRationalGaugeSource_familyObservableField_eq
    (r : UniversalFacetOrbitIndex → RatFunc ℂ)
    (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitRationalGaugeSource r) N =
      differentialFamilyObservableField (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge) N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let base := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
    universalFacetOrbitGauge
  let correction : UniversalFacetOrbitIndex → upperEndMeroField := fun q =>
    algebraMap (RatFunc ℂ) upperEndMeroField (r q)
  have h := differentialFamilyObservableField_addOfJetsInBase_eq base correction
    (fun q n => upperEndRatfunc_allJets_closed (r q) n) N
  simpa [base, correction, universalFacetOrbitRationalGaugeSource] using! h

/-- Every finite orientation chamber has the same field of observables at every resolution as the
underlying universal source. -/
theorem universalFacetOrbitOrientedSource_familyObservableField_eq
    (S J : Finset ℕ) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitOrientedSource S J) N =
      differentialFamilyObservableField (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge) N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  simpa [universalFacetOrbitOrientedSource] using!
    universalFacetOrbitRationalGaugeSource_familyObservableField_eq
      (universalOrientedPaletteGauge S J) N

/-- Any two finite orientation chambers have exactly the same observable field at every
resolution vector. -/
theorem universalFacetOrbitOrientedSource_familyObservableField_eq_chamber
    (S J S' J' : Finset ℕ) (N : UniversalFacetOrbitIndex → ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitOrientedSource S J) N =
      differentialFamilyObservableField (RatFunc ℂ)
        (universalFacetOrbitOrientedSource S' J') N := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact (universalFacetOrbitOrientedSource_familyObservableField_eq S J N).trans
    (universalFacetOrbitOrientedSource_familyObservableField_eq S' J' N).symm

/-- **Finite-observable orientation blindness.**  The chamber of orientation index `k` has the
same observable field as the positive chamber at every resolution, while Herglotz positivity
holds exactly when `k = 0` and the negative residue index is exactly `k`. -/
theorem universalOrientationIndex_sameObservableField_while_Herglotz_iff_zero
    (k : ℕ) (N : UniversalFacetOrbitIndex → ℕ) :
    let S := universalOrientationSupport k
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitOrientedSource S S) N =
        differentialFamilyObservableField (RatFunc ℂ)
          (universalFacetOrbitOrientedSource ∅ ∅) N ∧
      ((∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S S z).im) ↔ k = 0) ∧
      orientedNegativeIndex S S = k := by
  dsimp only
  refine ⟨universalFacetOrbitOrientedSource_familyObservableField_eq_chamber
      (universalOrientationSupport k) (universalOrientationSupport k) ∅ ∅ N, ?_, ?_⟩
  · have h := universalOrientedHerglotz_nonneg_iff_empty_of_subset
      (S := universalOrientationSupport k) (J := universalOrientationSupport k)
      (fun _ hmem => hmem)
    exact h.trans (universalOrientationSupport_eq_empty_iff k)
  · exact (orientedNegativeIndex_eq_card_of_subset
      (S := universalOrientationSupport k) (J := universalOrientationSupport k)
      (fun _ hmem => hmem)).trans (universalOrientationSupport_card k)

end

end GaloisForLFunctions.HTGeometry
