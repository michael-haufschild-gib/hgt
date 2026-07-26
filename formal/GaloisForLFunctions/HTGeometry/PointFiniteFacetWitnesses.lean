import GaloisForLFunctions.HTGeometry.UniversalFacetSourceCountablePointFiniteConstraintUniversalityLaw

/-!
# Realizations of the point-finite facet interface

Point-finiteness of a facet family is the exact boundary at which complete facet observation stays
finite.  This module supplies the realizations of that interface: it is inherited by subfamilies,
automatic for finite families and over a finite vertex set, and automatic for any pairwise disjoint
family — which produces infinite examples.  The disjoint edge family on the natural numbers is one,
so the countable point-finite Stanley--Reisner constraint law holds unconditionally on an infinite
geometry, and over a finite vertex set the premise disappears from the law altogether.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

/-! ## General realizations -/

/-- Every finite facet family is point-finite. -/
theorem PointFiniteFacetFamily.of_finite {α : Type*} {facets : Set (Finset α)}
    (h : facets.Finite) : PointFiniteFacetFamily facets :=
  fun _ => h.subset fun _ hF => hF.1

/-- Over a finite vertex set every facet family is point-finite, since there are only finitely
many facets available. -/
theorem pointFiniteFacetFamily_of_finite_vertices {α : Type*} [Finite α]
    (facets : Set (Finset α)) : PointFiniteFacetFamily facets :=
  fun _ => Set.toFinite _

/-- Point-finiteness passes to subfamilies. -/
theorem PointFiniteFacetFamily.mono {α : Type*} {facets facets' : Set (Finset α)}
    (hsub : facets' ⊆ facets) (h : PointFiniteFacetFamily facets) :
    PointFiniteFacetFamily facets' :=
  fun v => (h v).subset fun _ hF => ⟨hsub hF.1, hF.2⟩

/-- The union of two point-finite families is point-finite. -/
theorem PointFiniteFacetFamily.union {α : Type*} {facets facets' : Set (Finset α)}
    (h : PointFiniteFacetFamily facets) (h' : PointFiniteFacetFamily facets') :
    PointFiniteFacetFamily (facets ∪ facets') := by
  intro v
  apply ((h v).union (h' v)).subset
  intro F hF
  rcases hF.1 with hmem | hmem
  · exact Or.inl ⟨hmem, hF.2⟩
  · exact Or.inr ⟨hmem, hF.2⟩

/-- A pairwise disjoint facet family is point-finite: a vertex lies on at most one facet.  This is
the source of infinite point-finite families. -/
theorem pointFiniteFacetFamily_of_pairwise_disjoint {α : Type*}
    {facets : Set (Finset α)} (h : facets.Pairwise fun F G => Disjoint F G) :
    PointFiniteFacetFamily facets := by
  intro v
  apply Set.Subsingleton.finite
  intro F hF G hG
  by_contra hne
  exact Finset.disjoint_left.mp (h hF.1 hG.1 hne) hF.2 hG.2

/-! ## An infinite realization -/

/-- The disjoint edge family `{2k, 2k+1}` on the natural numbers. -/
def consecutivePairFacets : Set (Finset ℕ) :=
  Set.range fun k : ℕ => ({2 * k, 2 * k + 1} : Finset ℕ)

theorem consecutivePairFacets_pairwise_disjoint :
    consecutivePairFacets.Pairwise fun F G => Disjoint F G := by
  rintro F ⟨a, rfl⟩ G ⟨b, rfl⟩ hne
  have hab : a ≠ b := fun h => hne (by rw [h])
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  omega

theorem consecutivePairFacets_pointFinite :
    PointFiniteFacetFamily consecutivePairFacets :=
  pointFiniteFacetFamily_of_pairwise_disjoint consecutivePairFacets_pairwise_disjoint

theorem consecutivePairFacets_nonempty : consecutivePairFacets.Nonempty :=
  ⟨_, Set.mem_range_self 0⟩

theorem consecutivePairFacets_infinite : consecutivePairFacets.Infinite := by
  apply Set.infinite_range_of_injective
  intro a b hab
  have hab' : ({2 * a, 2 * a + 1} : Finset ℕ) = ({2 * b, 2 * b + 1} : Finset ℕ) := hab
  have hmem : (2 * a) ∈ ({2 * b, 2 * b + 1} : Finset ℕ) := by
    rw [← hab']
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/-! ## The interface disappears from the observation and constraint laws -/

/-- Over a finite vertex set complete nonconstant facet observation is finite for every family and
every polynomial, with no point-finiteness premise. -/
theorem polynomialVisibleFacets_finite_of_finite_vertices
    {R α : Type*} [CommSemiring R] [Finite α]
    (facets : Set (Finset α)) (P : MvPolynomial α R) :
    (polynomialVisibleFacets facets P).Finite :=
  polynomialVisibleFacets_finite_of_pointFinite facets
    (pointFiniteFacetFamily_of_finite_vertices facets) P

/-- The infinite disjoint edge family observes every polynomial finitely. -/
theorem polynomialVisibleFacets_consecutivePairFacets_finite
    {R : Type*} [CommSemiring R] (P : MvPolynomial ℕ R) :
    (polynomialVisibleFacets consecutivePairFacets P).Finite :=
  polynomialVisibleFacets_finite_of_pointFinite consecutivePairFacets
    consecutivePairFacets_pointFinite P

/-- The Stanley--Reisner row criterion over a finite vertex set, with the point-finiteness premise
discharged. -/
theorem linearIndependent_pointFiniteFacetRow_iff_of_finite_vertices
    {R α ι : Type*} [CommRing R] [Finite α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α)) (hne : facets.Nonempty) (P : ι → MvPolynomial α R) :
    LinearIndependent R
        (pointFiniteFacetRow facets
          (pointFiniteFacetFamily_of_finite_vertices facets) ∘ P) ↔
      LinearIndependent R
        (fun i => Ideal.Quotient.mk (setStanleyReisnerIdeal R facets) (P i)) :=
  linearIndependent_pointFiniteFacetRow_iff facets hne
    (pointFiniteFacetFamily_of_finite_vertices facets) P

/-- **Universal-source constraint law over a finite vertex set.**  On every nonempty facet family
over a finite vertex set the point-finiteness premise is automatic, so every universal facet source
realizes the exact Stanley--Reisner relation packet unconditionally. -/
theorem UniversalFacetSource.finiteVertexConstraintDifferentialMatroid
    (u : UniversalFacetSource)
    {α ι : Type*} [Finite α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α)) (hne : facets.Nonempty)
    (P : ι → MvPolynomial α (Polynomial ℂ)) :
    let Q := fun i =>
      pointFiniteFacetRow facets (pointFiniteFacetFamily_of_finite_vertices facets) (P i)
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
          (setStanleyReisnerIdeal (Polynomial ℂ) facets) (P i)) :=
  UniversalFacetSource.countablePointFiniteConstraintDifferentialMatroid u facets hne
    (pointFiniteFacetFamily_of_finite_vertices facets) P

/-- **Universal-source constraint law on an infinite geometry.**  The disjoint edge family on the
natural numbers is an unconditional infinite instance of the countable point-finite law. -/
theorem UniversalFacetSource.consecutivePairConstraintDifferentialMatroid
    (u : UniversalFacetSource) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → MvPolynomial ℕ (Polynomial ℂ)) :
    let Q := fun i =>
      pointFiniteFacetRow consecutivePairFacets consecutivePairFacets_pointFinite (P i)
    let e := countableUniversalFacetOrbitEmbedding
      (PointFiniteFacetIndex consecutivePairFacets)
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℂ upperEndMeroField := upperEndComplexToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let source : FinsuppOperatorRowIndex Q → upperEndMeroField := fun q =>
      boundedGaugeTranslatedPrimeLogUpperEnd universalFacetOrbitShift u.1 (e q.1)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply (finsuppOperatorRows Q) source) ↔
      LinearIndependent (Polynomial ℂ)
        (fun i => Ideal.Quotient.mk
          (setStanleyReisnerIdeal (Polynomial ℂ) consecutivePairFacets) (P i)) :=
  UniversalFacetSource.countablePointFiniteConstraintDifferentialMatroid u
    consecutivePairFacets consecutivePairFacets_nonempty
    consecutivePairFacets_pointFinite P

end GaloisForLFunctions.HTGeometry
