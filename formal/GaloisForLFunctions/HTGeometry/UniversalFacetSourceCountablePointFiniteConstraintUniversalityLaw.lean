import GaloisForLFunctions.HTGeometry.CountablePointFiniteConstraintCarrier
import GaloisForLFunctions.HTGeometry.UniversalFacetSourcePhase

/-!
# Every universal facet source carries countable point-finite constraints

The countable point-finite theorem uses one fixed universal gauge, while the finite
Stanley--Reisner matroid theorem allows every point of the universal facet-source phase.  Their
common source-independence argument extends the countable theorem to the whole phase: arbitrary
universal facet sources realize exactly the same finite structural relation packets on every
countable point-finite facet geometry.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- Every universal facet source realizes the exact row matroid of a finite family of finitely
supported polynomial operators on a countable coordinate set. -/
theorem UniversalFacetSource.finsuppDifferentialMatroid
    (u : UniversalFacetSource)
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ UniversalFacetOrbitIndex)
    (Q : ι → κ →₀ Polynomial ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
      LinearIndependent (Polynomial ℂ) Q := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1
  let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
    fullSource (e q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := (UniversalFacetSource.differentialIndependent u).comp
      (fun q : FinsuppOperatorRowIndex Q => e q.1)
      (e.injective.comp Subtype.val_injective)
    simpa [source, fullSource, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
    LinearIndependent (Polynomial ℂ) Q
  exact differentialIndependent_finsuppOperatorRows_iff
    upperEndMero_deriv_complexConstant Q source hsource

/-- **Universal-source countable point-finite constraint law.**  Every point of the universal
facet-source phase realizes the exact nonlinear differential relation packet of every finite
structural family in every nonempty countable point-finite Stanley--Reisner geometry. -/
theorem UniversalFacetSource.countablePointFiniteConstraintDifferentialMatroid
    (u : UniversalFacetSource)
    {α ι : Type*} [Countable α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α)) (hne : facets.Nonempty)
    (hfacets : PointFiniteFacetFamily facets)
    (P : ι → MvPolynomial α (Polynomial ℂ)) :
    let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
    let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
      LinearIndependent (Polynomial ℂ)
        (fun i => Ideal.Quotient.mk
          (setStanleyReisnerIdeal (Polynomial ℂ) facets) (P i)) := by
  classical
  let Q := fun i => pointFiniteFacetRow facets hfacets (P i)
  let e := countableUniversalFacetOrbitEmbedding (PointFiniteFacetIndex facets)
  have hanalytic := UniversalFacetSource.finsuppDifferentialMatroid u e Q
  have halgebra := linearIndependent_pointFiniteFacetRow_iff
    facets hne hfacets P
  exact hanalytic.trans halgebra

end

end GaloisForLFunctions.HTGeometry
