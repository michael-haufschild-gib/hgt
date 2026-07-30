import GaloisForLFunctions.HTGeometry.UniversalOrientedHerglotz

/-!
# Universal oriented HT constraint product

The finite residue cube is attached to the same universal prime-log source used for all finite
Stanley--Reisner constraint geometries.  Every chamber is a rational gauge of the same embedded
differential field; the full nonlinear differential matroid is chamber-independent, while Herglotz
positivity selects exactly the all-positive chamber.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- The translated rational correction attached to a finite orientation chamber. -/
def orientedAtomGaugeRatFunc (S J : Finset ℕ) (h : ℂ) : RatFunc ℂ :=
  ∑ n ∈ S, RatFunc.C (orientedAtomCoefficient J n : ℂ) *
    (RatFunc.C (orientationPole n : ℂ) - (RatFunc.X + RatFunc.C h))⁻¹

/-- The rational gauge on the complete universal palette induced by one finite orientation
chamber of the underlying source. -/
def universalOrientedPaletteGauge (S J : Finset ℕ) :
    UniversalFacetOrbitIndex → RatFunc ℂ := fun q =>
  orientedAtomGaugeRatFunc S J (universalFacetOrbitShift q)

/-- The complete universal palette in a chosen orientation chamber. -/
def universalFacetOrbitOrientedSource
    (S J : Finset ℕ) (q : UniversalFacetOrbitIndex) : upperEndMeroField :=
  universalFacetOrbitRationalGaugeSource (universalOrientedPaletteGauge S J) q

/-- Every finite orientation chamber retains differential independence of the complete universal
palette. -/
theorem universalFacetOrbitOrientedSource_differentialIndependent (S J : Finset ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ) (universalFacetOrbitOrientedSource S J) := by
  simpa [universalFacetOrbitOrientedSource] using!
    universalFacetOrbitRationalGaugeSource_differentialIndependent
      (universalOrientedPaletteGauge S J)

/-- Every orientation chamber generates exactly the same embedded differential field. -/
theorem universalFacetOrbitOrientedSource_differentialAdjoin_eq (S J : Finset ℕ) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialAdjoin (RatFunc ℂ) (Set.range (universalFacetOrbitOrientedSource S J)) =
      differentialAdjoin (RatFunc ℂ)
        (Set.range (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
          universalFacetOrbitGauge)) := by
  simpa [universalFacetOrbitOrientedSource] using!
    universalFacetOrbitRationalGaugeSource_differentialAdjoin_eq
      (universalOrientedPaletteGauge S J)

set_option synthInstance.maxHeartbeats 200000 in
/-- Every finite localized Stanley--Reisner differential matroid persists in every orientation
chamber. -/
theorem universalFacetOrbitOriented_stanleyReisnerLaurentDifferentialMatroid
    (S J : Finset ℕ)
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
      universalFacetOrbitOrientedSource S J
        (finiteFacetOrbitUniversalIndex e facets q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  simpa [universalFacetOrbitOrientedSource] using
    universalFacetOrbitRationalGauge_stanleyReisnerLaurentDifferentialMatroid
      (universalOrientedPaletteGauge S J) d facets N

/-- **Universal oriented constraint product.**  In every finite cube `J ⊆ S`, the representative
generates the same embedded differential field and realizes every finite localized nonlinear
constraint geometry.  The analytic source is Herglotz exactly at the all-positive vertex, and its
negative residue index is the cubical distance `|J|` from that vertex. -/
theorem universal_oriented_constraint_product
    (S J : Finset ℕ) (hJS : J ⊆ S)
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialAdjoin (RatFunc ℂ) (Set.range (universalFacetOrbitOrientedSource S J)) =
        differentialAdjoin (RatFunc ℂ)
          (Set.range (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
            universalFacetOrbitGauge)) ∧
      ((∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S J z).im) ↔ J = ∅) ∧
      orientedNegativeIndex S J = J.card ∧
      (let e := finiteVertexNatEmbedding α
       let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
           upperEndMeroField := fun q =>
         universalFacetOrbitOrientedSource S J
           (finiteFacetOrbitUniversalIndex e facets q.1)
       DifferentialIndependent ℂ
           (differentialOperatorRowApply
             (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
         LinearIndependent (Polynomial ℂ) N) := by
  refine ⟨universalFacetOrbitOrientedSource_differentialAdjoin_eq S J,
    universalOrientedHerglotz_nonneg_iff_empty_of_subset hJS,
    orientedNegativeIndex_eq_card_of_subset hJS, ?_⟩
  exact universalFacetOrbitOriented_stanleyReisnerLaurentDifferentialMatroid
    S J d facets N

/-- Canonical chamber support with prescribed orientation index. -/
def universalOrientationSupport (k : ℕ) : Finset ℕ := Finset.range k

@[simp]
theorem universalOrientationSupport_card (k : ℕ) :
    (universalOrientationSupport k).card = k := by
  simp [universalOrientationSupport]

@[simp]
theorem universalOrientationSupport_eq_empty_iff (k : ℕ) :
    universalOrientationSupport k = ∅ ↔ k = 0 := by
  simp [universalOrientationSupport]

/-- **Index form of the universal oriented constraint theorem.**  For every `k`, one explicit
representative has orientation index exactly `k`, is Herglotz exactly when `k=0`, generates the
same embedded differential field, and realizes every finite localized Stanley--Reisner nonlinear
differential matroid. -/
theorem universal_oriented_constraint_index_product
    (k : ℕ)
    {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    let S := universalOrientationSupport k
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    differentialAdjoin (RatFunc ℂ) (Set.range (universalFacetOrbitOrientedSource S S)) =
        differentialAdjoin (RatFunc ℂ)
          (Set.range (boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift
            universalFacetOrbitGauge)) ∧
      ((∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S S z).im) ↔ k = 0) ∧
      orientedNegativeIndex S S = k ∧
      (let e := finiteVertexNatEmbedding α
       let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
           upperEndMeroField := fun q =>
         universalFacetOrbitOrientedSource S S
           (finiteFacetOrbitUniversalIndex e facets q.1)
       DifferentialIndependent ℂ
           (differentialOperatorRowApply
             (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
         LinearIndependent (Polynomial ℂ) N) := by
  dsimp only
  have h := universal_oriented_constraint_product
    (universalOrientationSupport k) (universalOrientationSupport k) (fun _ hmem => hmem)
    d facets N
  refine ⟨h.1, ?_, ?_, h.2.2.2⟩
  · simpa using h.2.1.trans (universalOrientationSupport_eq_empty_iff k)
  · simpa using h.2.2.1.trans (universalOrientationSupport_card k)

end

end GaloisForLFunctions.HTGeometry
