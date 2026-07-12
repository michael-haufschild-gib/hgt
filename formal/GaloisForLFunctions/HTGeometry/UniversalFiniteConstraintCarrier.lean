import GaloisForLFunctions.HTGeometry.UniversalFacetPalette
import GaloisForLFunctions.HTGeometry.UpperEndStanleyReisnerRealization

/-!
# One fixed Herglotz source for every finite Stanley--Reisner differential matroid

The universal facet palette already carries one fixed bounded prime-log source whose complete
countable orbit is differentially independent.  This module embeds the facet orbit of an arbitrary
finite complex into that one palette and applies the exact localized Stanley--Reisner operator
theorem.  The chosen gauge is global: it does not depend on the vertex type, facets, denominator,
or structural family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- Canonical embedding of any finite vertex type into the universal natural vertex set. -/
def finiteVertexNatEmbedding (α : Type*) [Fintype α] : α ↪ ℕ :=
  (Fintype.equivFin α).toEmbedding.trans Fin.valEmbedding

/-- Embed one finite facet--integral-orbit palette into the universal countable palette. -/
def finiteFacetOrbitUniversalIndex
    {α : Type*} [Fintype α]
    (e : α ↪ ℕ) (facets : Finset (Finset α)) :
    (facets × (α → ℤ)) → UniversalFacetOrbitIndex := fun q =>
  (q.1.val.image e,
    (Finsupp.equivFunOnFinite.symm q.2).embDomain e)

theorem finiteFacetOrbitUniversalIndex_injective
    {α : Type*} [Fintype α]
    (e : α ↪ ℕ) (facets : Finset (Finset α)) :
    Function.Injective (finiteFacetOrbitUniversalIndex e facets) := by
  rintro ⟨F, n⟩ ⟨G, m⟩ h
  have hfacetImage := congrArg Prod.fst h
  have hexponent := congrArg Prod.snd h
  have hfacetVal : F.val = G.val :=
    (Finset.image_injective e.injective) hfacetImage
  have hfacet : F = G := Subtype.ext hfacetVal
  subst G
  have hfinsupp : Finsupp.equivFunOnFinite.symm n =
      Finsupp.equivFunOnFinite.symm m :=
    (Finsupp.embDomain_injective e) hexponent
  have hfun : n = m := Finsupp.equivFunOnFinite.symm.injective hfinsupp
  subst m
  rfl

/-- The single globally chosen positive prime-log gauge used for every finite constraint
geometry. -/
def universalFacetOrbitGauge : PrimeLogBoundedGauge :=
  Classical.choose exists_universalFacetOrbit_upperEnd_differentialIndependent

/-- The complete universal orbit of the fixed source is genuinely differentially independent over
`C(z)`. -/
theorem universalFacetOrbitGauge_differentialIndependent :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        universalFacetOrbitGauge) :=
  Classical.choose_spec exists_universalFacetOrbit_upperEnd_differentialIndependent

/-- **Single-source finite constraint-completeness law.** The one fixed universal gauge realizes,
for every finite simplicial facet family and every finite localized structural family, exactly the
Stanley--Reisner nonlinear differential matroid.  No analytic source parameter in this theorem
depends on `α`, `facets`, `d`, `ι`, or `N`. -/
theorem universalFacetOrbit_stanleyReisnerLaurentDifferentialMatroid
    {α ι : Type*}
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
        universalFacetOrbitGauge (finiteFacetOrbitUniversalIndex e facets q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  classical
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let e := finiteVertexNatEmbedding α
  let fullSource := boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
    universalFacetOrbitGauge
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    fullSource (finiteFacetOrbitUniversalIndex e facets q.1)
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := universalFacetOrbitGauge_differentialIndependent.comp
      (fun q : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) =>
        finiteFacetOrbitUniversalIndex e facets q.1)
      ((finiteFacetOrbitUniversalIndex_injective e facets).comp Subtype.val_injective)
    simpa [source, fullSource, Function.comp_def] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

/-- Every prime logarithm remains an exact simple pole of the single universal source, with the
same explicit positive-weight residue data in every finite realization. -/
theorem universalFacetOrbitGauge_hasSimplePoleAt (p : Nat.Primes) :
    HasSimplePoleAt
      (primeLogHerglotz (fun q => universalFacetOrbitGauge q))
      (primeLogSupport p : ℂ)
      (-(primeDyadicWeight (fun q => universalFacetOrbitGauge q) p : ℂ)) :=
  hasSimplePoleAt_primeLogHerglotz (fun q => universalFacetOrbitGauge q)
    ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q)) p

end

end GaloisForLFunctions.HTGeometry
