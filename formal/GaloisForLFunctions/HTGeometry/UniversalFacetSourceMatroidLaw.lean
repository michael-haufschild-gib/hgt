import GaloisForLFunctions.HTGeometry.UniversalFacetSourcePhase
import GaloisForLFunctions.HTGeometry.LocalizedStanleyReisnerMatroidRank

/-!
# A universal facet source represents the complete localized Stanley–Reisner matroid

Membership in the universal source phase gives differential independence of the whole facet-orbit
palette.  Composing with the finite facet-orbit index map, whose injectivity preserves
independence, and restricting the constants from `RatFunc ℂ` to `ℂ` produces exactly the
independent source packet required by the localized Stanley--Reisner matroid law.  The conclusion
is therefore not merely independence of the whole output family but equality of the entire
represented matroid: every subset independence, every circuit, and every rank is the
Stanley--Reisner quotient datum.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- **Complete matroid law for a universal facet source.**  The differential matroid represented
by the localized Stanley--Reisner outputs of a universal facet source is the Stanley--Reisner
quotient-class matroid itself. -/
theorem UniversalFacetSource.stanleyReisnerLaurentMatroid_eq
    (u : UniversalFacetSource)
    {α ι : Type}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
    differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) =
      stanleyReisnerLaurentMatroid d facets N := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let e := finiteVertexNatEmbedding α
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    fullSource (finiteFacetOrbitUniversalIndex e facets q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := (UniversalFacetSource.differentialIndependent u).comp
      (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) =>
        finiteFacetOrbitUniversalIndex e facets q.1)
      ((finiteFacetOrbitUniversalIndex_injective e facets).comp Subtype.val_injective)
    simpa [source, fullSource, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  exact differentialFamilyMatroid_stanleyReisnerLaurentRows_eq
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

end

end GaloisForLFunctions.HTGeometry
