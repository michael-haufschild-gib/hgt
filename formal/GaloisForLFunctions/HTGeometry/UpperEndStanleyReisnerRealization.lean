import GaloisForLFunctions.HTGeometry.UpperEndConstantField

/-!
# Upper-end realization of localized Stanley--Reisner differential matroids

For every finite facet complex, one bounded prime-log Herglotz source is chosen whose complete
collision-free facet--integral-orbit translation family is differentially independent over `C`.
The same source then realizes, simultaneously for every finite Laurent structural family, exactly
the localized Stanley--Reisner nonlinear differential matroid.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- One bounded prime-log source has a complete facet--Laurent orbit that is differentially
independent over `C(z)`.  This is the conventional hypertranscendence-strength realization. -/
theorem exists_upperEndFacetOrbit_differentialIndependent_ratfunc
    {α : Type*} [Fintype α]
    (facets : Finset (Finset α)) :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent (RatFunc ℂ)
        (boundedGaugeTranslatedPrimeLogUpperEnd
          (facetOrbitShift facets (rationalIndependentWeights α)) u) := by
  classical
  let omega := rationalIndependentWeights α
  let shiftValue := facetOrbitShift facets omega
  exact exists_upperEndShift_differentialIndependent shiftValue
    (facetOrbitShift_injective facets omega
      (rationalIndependentWeights_linearIndependent α))

/-- One bounded prime-log source has a differentially independent complete facet--Laurent orbit. -/
theorem exists_upperEndFacetOrbit_differentialIndependent
    {α : Type*} [Fintype α]
    (facets : Finset (Finset α)) :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent ℂ
        (boundedGaugeTranslatedPrimeLogUpperEnd
          (facetOrbitShift facets (rationalIndependentWeights α)) u) := by
  classical
  let omega := rationalIndependentWeights α
  let shiftValue := facetOrbitShift facets omega
  have hshiftValue : Function.Injective shiftValue :=
    facetOrbitShift_injective facets omega
      (rationalIndependentWeights_linearIndependent α)
  obtain ⟨u, hu⟩ := exists_upperEndShift_differentialIndependent
    shiftValue hshiftValue
  refine ⟨u, ?_⟩
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  change DifferentialIndependent ℂ
    (boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u)
  exact differentialIndependent_upperEnd_restrictComplex _ hu

/-- **Universal fixed-source realization law.**  Once the complete facet orbit of a source is
differentially independent, every finite common-denominator Laurent structural family has outputs
whose full nonlinear differential matroid is exactly its Stanley--Reisner numerator matroid. -/
theorem upperEnd_stanleyReisnerLaurentDifferentialMatroid
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (u : PrimeLogBoundedGauge)
    (facets : Finset (Finset α))
    (hu :
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      DifferentialIndependent ℂ
        (boundedGaugeTranslatedPrimeLogUpperEnd
          (facetOrbitShift facets (rationalIndependentWeights α)) u))
    (d : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd
        (facetOrbitShift facets (rationalIndependentWeights α)) u q.1
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd
    (facetOrbitShift facets (rationalIndependentWeights α)) u
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q => fullSource q.1
  have hsource : DifferentialIndependent ℂ source := by
    exact hu.comp
      (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) => q.1)
      Subtype.val_injective
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

/-- Every finite localized structural family admits the concrete upper-end realization; this is a
finite-family corollary of the fixed-source theorem. -/
theorem exists_upperEnd_stanleyReisnerLaurentDifferentialMatroid
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ u : PrimeLogBoundedGauge,
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      let omega := rationalIndependentWeights α
      let shiftValue := facetOrbitShift facets omega
      let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
          upperEndMeroField := fun q =>
        boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u q.1
      DifferentialIndependent ℂ
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
        LinearIndependent (Polynomial ℂ) N := by
  classical
  let omega := rationalIndependentWeights α
  let shiftValue := facetOrbitShift facets omega
  have hshiftValue : Function.Injective shiftValue :=
    facetOrbitShift_injective facets omega
      (rationalIndependentWeights_linearIndependent α)
  obtain ⟨u, hu⟩ := exists_upperEndShift_differentialIndependent
    shiftValue hshiftValue
  refine ⟨u, ?_⟩
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    boundedGaugeTranslatedPrimeLogUpperEnd shiftValue u q.1
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := hu.comp
      (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) => q.1)
      Subtype.val_injective
    simpa [source, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

end

end GaloisForLFunctions.HTGeometry
