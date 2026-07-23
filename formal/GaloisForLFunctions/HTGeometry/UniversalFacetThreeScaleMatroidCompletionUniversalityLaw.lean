import GaloisForLFunctions.HTGeometry.UniversalFacetSourceCountablePointFiniteConstraintUniversalityLaw
import GaloisForLFunctions.HTGeometry.UniversalFacetSourceStanleyReisnerMatroidLaw
import GaloisForLFunctions.HTGeometry.UniversalFacetTwoScaleBlindnessUniversalityLaw

/-!
# Universal facet three-scale matroid/completion law

Three terminal universal-facet theorems describe different resolutions of the same source phase.
This file closes them into one law: exact countable point-finite quotient independence, the complete
finite localized Laurent matroid, and the compact-open completed orientation ring are all fixed
throughout the universal source phase.  The completed invariant is additionally blind to arbitrary
finite or infinite prime orientation.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- **Universal facet three-scale matroid/completion universality law.**  Any universal facet source
realizes the exact structural matroid at both countable point-finite and finite localized Laurent
resolution, while any two sources and any two prime orientations have the same completed ring. -/
theorem UniversalFacetSource.countable_finiteLocalized_completed_threeScale
    (u v : UniversalFacetSource) (ε δ : Nat.Primes → Bool)
    {αc ιc : Type*} [Countable αc] [DecidableEq αc]
    [Fintype ιc] [DecidableEq ιc]
    (facetsC : Set (Finset αc)) (hneC : facetsC.Nonempty)
    (hfacetsC : PointFiniteFacetFamily facetsC)
    (P : ιc → MvPolynomial αc (Polynomial ℂ))
    {αf ιf : Type} [Fintype αf] [Fintype ιf]
    [DecidableEq αf] [DecidableEq ιf]
    (d : translationSubmonoid (Polynomial ℂ) αf)
    (facetsF : Finset (Finset αf))
    (N : ιf → MvPolynomial αf (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facetsF) :
    (let Q := fun i => pointFiniteFacetRow facetsC hfacetsC (P i)
     let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facetsC)
     letI := isDomain_upperEndAnalyticSubring
     letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
     letI := upperEndMeroFieldDifferential
     let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
       boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
     DifferentialIndependent ℂ
         (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
       LinearIndependent (Polynomial ℂ)
         (fun i => Ideal.Quotient.mk
           (setStanleyReisnerIdeal (Polynomial ℂ) facetsC) (P i))) ∧
    (let e := finiteVertexNatEmbedding αf
     let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facetsF N) →
         upperEndMeroField := fun q =>
       boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
         u.1 (finiteFacetOrbitUniversalIndex e facetsF q.1)
     differentialFamilyMatroid (F := ℂ)
         (differentialOperatorRowApply
           (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facetsF N)) source) =
       stanleyReisnerLaurentMatroid d facetsF N) ∧
    UniversalFacetSource.completedOrientationRing u ε =
      UniversalFacetSource.completedOrientationRing v δ := by
  refine ⟨UniversalFacetSource.countablePointFiniteConstraintDifferentialMatroid
      u facetsC hneC hfacetsC P,
    UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq
      u d facetsF N,
    UniversalFacetSource.completedOrientationRing_eq u v ε δ⟩

end

end GaloisForLFunctions.HTGeometry
