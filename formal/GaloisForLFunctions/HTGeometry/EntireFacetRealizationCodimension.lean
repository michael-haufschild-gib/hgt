import GaloisForLFunctions.HTGeometry.EllipticLiouvilleFacetCodimension

/-!
# Entire facet carriers: two omitted vertices are already impossible

At the level of the analytic datum `ScalarFacetRealization`, an **entire** facet carrier cannot have
two `ℚ`-independent periods at all:

* if the two steps are `ℝ`-dependent, the period group is not discrete and the carrier is constant
  (`no_scalarFacetRealization_of_two_omitted_realDependent`);
* if they are `ℝ`-independent they form a `PeriodPair`, and Liouville's theorem makes the carrier
  constant (`const_of_lattice_periodic_differentiable`).

So `no_scalarFacetRealization_of_two_omitted_entire` covers both cases at once, and
`facetComplementRankOne_of_facetRealization_entire` states the facet-codimension law directly for the
analytic datum, without going through a ring-level realization.  This is the form that vectorized
(channel) realizations reduce to.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **Two omitted vertices kill an entire facet carrier.**  Whether or not the two omitted steps are
`ℝ`-dependent, the carrier ends up constant — by non-discreteness of the period group in the first
case and by Liouville's theorem in the second. -/
theorem no_scalarFacetRealization_of_two_omitted_entire {V : Finset α}
    {facets : Set (Finset α)} (R : ScalarFacetRealization V facets)
    (hentire : ∀ F ∈ facets, Differentiable ℂ (R.carrier F))
    {F : Finset α} (hF : F ∈ facets) {a b : α}
    (ha : a ∈ V \ F) (hb : b ∈ V \ F) (hab : a ≠ b) : False := by
  by_cases hdep : LinearIndependent ℝ (R.ω ∘ ![a, b])
  · have hindep' : LinearIndependent ℝ ![R.ω a, R.ω b] := by
      rwa [comp_cons_two] at hdep
    set L : PeriodPair := ⟨R.ω a, R.ω b, hindep'⟩ with hL
    have hspan : ∀ p ∈ Submodule.span ℤ (Set.range ![R.ω a, R.ω b]),
        Function.Periodic (R.carrier F) p := by
      refine periodic_of_mem_span_range ![R.ω a, R.ω b] (fun i => ?_)
      fin_cases i
      · exact R.carrier_periodic F hF a ha
      · exact R.carrier_periodic F hF b hb
    have hlat : ∀ p ∈ L.lattice, Function.Periodic (R.carrier F) p := by
      intro p hp
      refine hspan p ?_
      rw [range_cons_two]
      exact hp
    exact not_hypertranscendental_of_lattice_periodic_differentiable L (hentire F hF) hlat
      (R.carrier_hypertranscendental F hF)
  · exact no_scalarFacetRealization_of_two_omitted_realDependent R hF ha hb hab hdep

/-- **The facet-codimension law for an entire analytic datum.**  Every facet omits at most one
ambient vertex. -/
theorem facetComplementRankOne_of_facetRealization_entire {V : Finset α}
    {facets : Set (Finset α)} (R : ScalarFacetRealization V facets)
    (hentire : ∀ F ∈ facets, Differentiable ℂ (R.carrier F))
    (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  exact no_scalarFacetRealization_of_two_omitted_entire R hentire hF ha hb hab

end GaloisForLFunctions.HTGeometry
