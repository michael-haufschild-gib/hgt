import GaloisForLFunctions.HTGeometry.LocalizedStanleyReisnerMatroidRank
import GaloisForLFunctions.HTGeometry.UniversalFacetSourcePhase

/-!
# Universal facet sources represent the complete Stanley--Reisner matroid

The source-phase theorem previously exposed only independence of the entire localized output
family.  Restricting the universal orbit palette to the exact finite coordinate packet supplies the
independent source required by the general localized-row theorem, which identifies the whole
differential matroid and therefore every dependent subfamily, circuit, and rank.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial Set
open scoped Differential

noncomputable section

local instance universalFacetSourceMatroidUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance universalFacetSourceMatroidComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance universalFacetSourceMatroidCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance universalFacetSourceMatroidComplexDifferential : Differential ℂ := ⟨0⟩

local instance universalFacetSourceMatroidUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance universalFacetSourceMatroidDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField where
  deriv_algebraMap c := by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]

/-- **Universal facet-source Stanley--Reisner matroid law.**  Every point of the canonical source
phase represents the complete localized Stanley--Reisner quotient-class matroid.  Thus source and
orientation choices cannot change any subfamily dependence relation or rank. -/
theorem UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq
    (u : UniversalFacetSource)
    {α ι : Type}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
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
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
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
  change differentialFamilyMatroid (F := ℂ)
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) =
    stanleyReisnerLaurentMatroid d facets N
  exact differentialFamilyMatroid_stanleyReisnerLaurentRows_eq
    upperEndMero_deriv_complexConstant d facets N source hsource

/-- Every selected output packet consequently has the same extended rank as its localized
Stanley--Reisner quotient-class packet. -/
theorem UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eRk
    (u : UniversalFacetSource)
    {α ι : Type}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets)
    (I : Set ι) :
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source)).eRk I =
      (stanleyReisnerLaurentMatroid d facets N).eRk I := by
  classical
  let e := finiteVertexNatEmbedding α
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
      u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
  have hmat :=
    UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq
      u d facets N
  exact congrArg (fun M : Matroid ι => M.eRk I) hmat

/-- Every minimal dependence is the Stanley--Reisner one: a subset is a circuit of the
source-represented matroid exactly when it is a circuit of the quotient-class matroid. -/
theorem UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_isCircuit_iff
    (u : UniversalFacetSource)
    {α ι : Type}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets)
    (I : Set ι) :
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source)).IsCircuit I ↔
      (stanleyReisnerLaurentMatroid d facets N).IsCircuit I := by
  classical
  have hmat :=
    UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq
      u d facets N
  exact iff_of_eq (congrArg (fun M : Matroid ι => M.IsCircuit I) hmat)

/-- Independence of every selected subfamily is exactly linear independence of the corresponding
Stanley--Reisner quotient classes, so no source or orientation choice can change a single
dependence relation. -/
theorem UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_indep_iff
    (u : UniversalFacetSource)
    {α ι : Type}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets)
    (I : Set ι) :
    let e := finiteVertexNatEmbedding α
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
        u.1 (finiteFacetOrbitUniversalIndex e facets q.1)
    (differentialFamilyMatroid (F := ℂ)
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source)).Indep I ↔
      LinearIndependent (Polynomial ℂ) (fun i : I => N i) := by
  classical
  have hmat :=
    UniversalFacetSource.stanleyReisnerLaurentDifferentialFamilyMatroid_eq
      u d facets N
  exact (iff_of_eq (congrArg (fun M : Matroid ι => M.Indep I) hmat)).trans
    (stanleyReisnerLaurentMatroid_indep_iff d facets N I)

end

end GaloisForLFunctions.HTGeometry
