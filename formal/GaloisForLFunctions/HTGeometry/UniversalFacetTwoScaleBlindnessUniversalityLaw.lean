import GaloisForLFunctions.HTGeometry.CountablePointFiniteConstraintCarrier
import GaloisForLFunctions.HTGeometry.UniversalFacetSourcePhase

/-!
# Universal facet two-scale blindness

The countable point-finite differential matroid and the compact-open completed rational Cauchy
ring forget different parts of the universal facet presentation.  The first forgets the chosen
source inside the residual phase.  The second forgets both that source and an arbitrary finite or
infinite prime orientation.  Together they give a source-independent local/global invariant pair.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- **Universal facet two-scale blindness law.**  Any two universal facet sources have identical
countable point-finite differential dependence packets, while their completed orientation rings
agree for every pair of finite or infinite prime orientations. -/
theorem UniversalFacetSource.countableConstraint_and_completion_sourceInvariant
    (u v : UniversalFacetSource) (ε δ : Nat.Primes → Bool)
    {α ι : Type*} [Countable α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α))
    (hfacets : PointFiniteFacetFamily facets)
    (P : ι → MvPolynomial α (Polynomial ℂ)) :
    let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
    let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let sourceU : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
    let sourceV : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift v.1 (e q.1)
    (DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) sourceU) ↔
      DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) sourceV)) ∧
      UniversalFacetSource.completedOrientationRing u ε =
        UniversalFacetSource.completedOrientationRing v δ := by
  classical
  let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
  let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let sourceU : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
    boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
  let sourceV : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
    boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift v.1 (e q.1)
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  have hsourceRatU : DifferentialIndependent (RatFunc ℂ) sourceU := by
    have hcomp := (UniversalFacetSource.differentialIndependent u).comp
      (fun q : FinsuppOperatorRowIndex Q => e q.1)
      (e.injective.comp Subtype.val_injective)
    simpa [sourceU, Function.comp_def] using hcomp
  have hsourceRatV : DifferentialIndependent (RatFunc ℂ) sourceV := by
    have hcomp := (UniversalFacetSource.differentialIndependent v).comp
      (fun q : FinsuppOperatorRowIndex Q => e q.1)
      (e.injective.comp Subtype.val_injective)
    simpa [sourceV, Function.comp_def] using hcomp
  have hsourceU : DifferentialIndependent ℂ sourceU :=
    differentialIndependent_upperEnd_restrictComplex sourceU hsourceRatU
  have hsourceV : DifferentialIndependent ℂ sourceV :=
    differentialIndependent_upperEnd_restrictComplex sourceV hsourceRatV
  have hu := differentialIndependent_finsuppOperatorRows_iff
    upperEndMero_deriv_complexConstant Q sourceU hsourceU
  have hv := differentialIndependent_finsuppOperatorRows_iff
    upperEndMero_deriv_complexConstant Q sourceV hsourceV
  exact ⟨hu.trans hv.symm, UniversalFacetSource.completedOrientationRing_eq u v ε δ⟩

end

end GaloisForLFunctions.HTGeometry
