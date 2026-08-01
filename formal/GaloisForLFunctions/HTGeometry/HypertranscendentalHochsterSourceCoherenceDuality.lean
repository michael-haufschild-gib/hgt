import GaloisForLFunctions.HTGeometry.HochsterMultidegreeExhaustion
import GaloisForLFunctions.HTGeometry.UniversalOrientedConstraintProduct

/-!
# Hypertranscendental Hochster source-coherence duality

Every finite Stanley--Reisner constraint geometry is realized by the universal prime-log
hypertranscendental source.  The same source admits every finite residue-orientation index without
changing its embedded differential field or nonlinear structural matroid.  Independently, the
multidegree strands of that exact Stanley--Reisner quotient are the reduced simplicial cochain
complexes of the induced constraint subcomplexes in every Koszul degree.

This file composes those two already-unconditional constructions on the same facet complex.  The
capstone is the exact topology--orientation product law: arbitrary finite derived constraint
topology and arbitrary finite residue orientation coexist over one fixed hypertranscendental
differential field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

/-- **Exact Hochster source-coherence profile.**  In every multidegree and every Koszul degree,
cycles are exactly reduced simplicial cocycles and boundaries are exactly reduced simplicial
coboundaries under the exhaustive strand correspondence. -/
def HochsterSourceCoherenceExact
    {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α]
    (facets : Finset (Finset α)) : Prop :=
  ∀ (σ : Finset α) (p : ℕ)
    (b : (Fin (p + 1) → α) → stanleyReisnerRing ℂ facets),
    IsAltTensor b → IsMultidegreeStrand ℂ facets σ b →
      (koszulD (srVertexX ℂ facets) b = 0 ↔
          ∀ v : Fin p → α, (∀ t, v t ∈ σ) → Function.Injective v →
            IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
              simplicialCoboundary ℂ (strandCochain ℂ facets σ b)
                (σ \ Finset.image v Finset.univ) = 0) ∧
        (b ∈ koszulBoundaries (p := p) (srVertexX ℂ facets) ↔
          ∃ h : Finset α → ℂ, ∀ v : Fin (p + 1) → α,
            (∀ t, v t ∈ σ) → Function.Injective v →
              IsFaceOf (↑facets : Set (Finset α)) (σ \ Finset.image v Finset.univ) →
                simplicialCoboundary ℂ h (σ \ Finset.image v Finset.univ) =
                  strandCochain ℂ facets σ b (σ \ Finset.image v Finset.univ))

/-- Every finite facet complex has the complete all-degree Hochster source-coherence profile. -/
theorem hochsterSourceCoherenceExact
    {α : Type*} [DecidableEq α] [LinearOrder α] [Fintype α]
    (facets : Finset (Finset α)) :
    HochsterSourceCoherenceExact facets := by
  intro σ p b hb hstr
  exact hochster_multidegree_strand_correspondence facets σ hb hstr

/-- **Hypertranscendental Hochster topology--orientation product law.**  For every finite facet
complex and every prescribed finite residue index `k`, one representative:

* generates the same embedded differential field as the positive universal source;
* is Herglotz exactly at `k = 0` and has negative residue index exactly `k`;
* realizes the exact localized Stanley--Reisner nonlinear differential matroid for every finite
  structural family `N`; and
* carries, in every multidegree and every Koszul degree, exactly the reduced simplicial
  cycle/boundary data of the induced constraint subcomplex.

Thus the complete derived constraint topology is invariant under arbitrary finite residue
orientation surgery and cannot select the positive chamber. -/
theorem hypertranscendentalHochsterSourceCoherence_orientationProduct
    (k : ℕ)
    {α ι : Type*}
    [Fintype α] [LinearOrder α] [Fintype ι] [DecidableEq ι]
    (d : translationSubmonoid (Polynomial ℂ) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    (let S := universalOrientationSupport k
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
           LinearIndependent (Polynomial ℂ) N)) ∧
      HochsterSourceCoherenceExact facets := by
  constructor
  · exact universal_oriented_constraint_index_product k d facets N
  · exact hochsterSourceCoherenceExact facets

end

end GaloisForLFunctions.HTGeometry
