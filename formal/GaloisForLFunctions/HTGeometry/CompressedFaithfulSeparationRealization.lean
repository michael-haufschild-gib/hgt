import GaloisForLFunctions.HTGeometry.FacetSliceLaurentSupport
import GaloisForLFunctions.HTGeometry.FaithfulSeparationOrbitShift
import GaloisForLFunctions.HTGeometry.UpperEndStanleyReisnerRealization
import GaloisForLFunctions.HTGeometry.FacetSewnHerglotzStanleyReisner
import GaloisForLFunctions.HTGeometry.ComplexTranscendental

/-!
# Compressed realization from arbitrary faithful facet-separation data

The universal Stanley--Reisner realization uses one analytic coordinate per facet, and separates
the complete facet orbit by rationally independent vertex weights carried by *all* vertices.  A
faithful facet separation compresses that system: the translate of a facet summand by a vertex
outside that facet is trivial, so the shift palette collapses onto the facet slice.

That collapse is exactly compatible with the Laurent operator rows, whose finite index set lies in
the facet slice.  Hence arbitrary faithful separation data, in any dimension, already realizes the
complete localized Stanley--Reisner nonlinear differential matroid: the compressed source has a
differentially independent structural orbit, and every finite Laurent structural family has
differential matroid equal to its Stanley--Reisner numerator matroid.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- Index type of the compressed structural orbit: facet slices of the translation lattice. -/
abbrev FacetSliceIndex (α : Type*) (facets : Finset (Finset α)) : Type _ :=
  {q : facets × (α → ℤ) // q ∈ FacetSeparationValues.FacetSlice α facets}

/-- The compressed shift palette is injective on the facet slice. -/
theorem facetSliceShift_injective {α : Type*} [Fintype α]
    {facets : Finset (Finset α)} (S : FacetSeparationValues α facets)
    {t : ℂ} (ht : t ∉ S.collisionSet) :
    Function.Injective
      (fun q : FacetSliceIndex α facets => S.orbitShift t q.1) := by
  intro q₁ q₂ h
  exact Subtype.ext (S.orbitShift_injOn ht q₁.2 q₂.2 h)

/-- Every finite Laurent operator row index is a facet slice index. -/
def rowIndexToFacetSlice {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
    (d : translationSubmonoid (Polynomial ℂ) α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      FacetSliceIndex α facets :=
  fun q => ⟨q.1, fun _v hv => finiteFinsuppRowIndex_slice d facets N q hv⟩

theorem rowIndexToFacetSlice_injective {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι]
    (d : translationSubmonoid (Polynomial ℂ) α) (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    Function.Injective (rowIndexToFacetSlice d facets N) := by
  intro a b h
  have h1 : (rowIndexToFacetSlice d facets N a).1 =
      (rowIndexToFacetSlice d facets N b).1 := congrArg Subtype.val h
  exact Subtype.ext h1

/-- **Compressed faithful-separation realization law.**  Every faithful facet separation, in any
dimension, supplies a separation parameter and one bounded prime-log Herglotz source whose
compressed structural orbit realizes exactly the localized Stanley--Reisner nonlinear differential
matroid of every finite Laurent structural family. -/
theorem exists_compressedSeparation_stanleyReisnerLaurentDifferentialMatroid
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (facets : Finset (Finset α)) (S : FacetSeparationValues α facets)
    (d : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ (t : ℂ) (u : PrimeLogBoundedGauge),
      t ∉ S.collisionSet ∧
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
          upperEndMeroField := fun q =>
        boundedGaugeTranslatedPrimeLogUpperEnd (S.orbitShift t) u q.1
      DifferentialIndependent ℂ
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
        LinearIndependent (Polynomial ℂ) N := by
  classical
  obtain ⟨t, ht⟩ := S.exists_separation_parameter
  obtain ⟨u, hu⟩ := exists_upperEndShift_differentialIndependent
    (fun q : FacetSliceIndex α facets => S.orbitShift t q.1)
    (facetSliceShift_injective S ht)
  refine ⟨t, u, ht, ?_⟩
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
      upperEndMeroField := fun q =>
    boundedGaugeTranslatedPrimeLogUpperEnd (S.orbitShift t) u q.1
  have hsourceRat : DifferentialIndependent (RatFunc ℂ) source := by
    have hcomp := hu.comp (rowIndexToFacetSlice d facets N)
      (rowIndexToFacetSlice_injective d facets N)
    simpa [source, rowIndexToFacetSlice, Function.comp_def,
      boundedGaugeTranslatedPrimeLogUpperEnd] using hcomp
  have hsource : DifferentialIndependent ℂ source :=
    differentialIndependent_upperEnd_restrictComplex source hsourceRat
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := upperEndMeroField)
    upperEndMero_deriv_complexConstant d facets N source hsource

/-- **Unconditional compressed realization.**  Every finite facet family carries faithful
separation values, hence a compressed realization of its localized Stanley--Reisner nonlinear
differential matroid. -/
theorem exists_compressed_stanleyReisnerLaurentDifferentialMatroid
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (facets : Finset (Finset α))
    (d : translationSubmonoid (Polynomial ℂ) α)
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ (S : FacetSeparationValues α facets) (t : ℂ) (u : PrimeLogBoundedGauge),
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
          upperEndMeroField := fun q =>
        boundedGaugeTranslatedPrimeLogUpperEnd (S.orbitShift t) u q.1
      DifferentialIndependent ℂ
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
        LinearIndependent (Polynomial ℂ) N := by
  classical
  obtain ⟨τ, hτ⟩ := exists_transcendental_complex
  refine ⟨FacetSeparationValues.ofTranscendental facets hτ, ?_⟩
  obtain ⟨t, u, -, hmatroid⟩ :=
    exists_compressedSeparation_stanleyReisnerLaurentDifferentialMatroid facets
      (FacetSeparationValues.ofTranscendental facets hτ) d N
  exact ⟨t, u, hmatroid⟩

/-- **Compressed exact annihilator.**  A single structural Laurent output of the compressed
realization is differentially independent exactly when its Stanley--Reisner class is nonzero; the
differential annihilator of the compressed source is therefore exactly the Stanley--Reisner
ideal. -/
theorem exists_compressedSeparation_annihilator
    {α : Type*} [Fintype α] [DecidableEq α]
    (facets : Finset (Finset α)) (S : FacetSeparationValues α facets)
    (d : translationSubmonoid (Polynomial ℂ) α)
    (P : MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    ∃ (t : ℂ) (u : PrimeLogBoundedGauge),
      letI := isDomain_upperEndAnalyticSubring
      letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
      letI := upperEndMeroFieldDifferential
      let source : FiniteFinsuppRowIndex
          (stanleyReisnerLaurentRows d facets (fun _ : Unit => P)) →
          upperEndMeroField := fun q =>
        boundedGaugeTranslatedPrimeLogUpperEnd (S.orbitShift t) u q.1
      DifferentialIndependent ℂ
          (differentialOperatorRowApply
            (finiteFinsuppOperatorRows
              (stanleyReisnerLaurentRows d facets (fun _ : Unit => P))) source) ↔
        P ≠ 0 := by
  classical
  obtain ⟨t, u, -, hmatroid⟩ :=
    exists_compressedSeparation_stanleyReisnerLaurentDifferentialMatroid facets S d
      (fun _ : Unit => P)
  exact ⟨t, u, hmatroid.trans (linearIndependent_unit_stanleyReisner_iff facets P)⟩

end

end GaloisForLFunctions.HTGeometry
