import GaloisForLFunctions.HTGeometry.EllipticHypertranscendenceFreeProof
import GaloisForLFunctions.HTGeometry.ChannelSRRealization

/-!
# The facet-codimension law at the analytic datum, for meromorphic carriers

With `ellipticHypertranscendenceFree` proved, the lattice alternative in the period-rank analysis is
closed and the facet-codimension law holds for the analytic datum itself, with no entirety
hypothesis: two omitted vertices give the carrier two `ℚ`-independent periods, and both
configurations are excluded — the `ℝ`-dependent one by non-discreteness of the period group, the
`ℝ`-independent one because the carrier would be a hypertranscendental elliptic function.

* **`no_scalarFacetRealization_of_two_omitted`**;
* **`facetComplementRankOne_of_facetRealization`** — the law for a meromorphic analytic datum;
* **`channel_facetComplementRankOne`** — hence for an arbitrary family of meromorphic channels under
  componentwise translations, with no entirety hypothesis either.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **Two omitted vertices are impossible for a meromorphic facet datum.**  Whether or not the two
omitted steps are `ℝ`-dependent, the carrier cannot be hypertranscendental: in the first case its
period group is not discrete, in the second it is an elliptic function. -/
theorem no_scalarFacetRealization_of_two_omitted {V : Finset α} {facets : Set (Finset α)}
    (R : ScalarFacetRealization V facets) {F : Finset α} (hF : F ∈ facets) {a b : α}
    (ha : a ∈ V \ F) (hb : b ∈ V \ F) (hab : a ≠ b) : False := by
  by_cases hdep : LinearIndependent ℝ (R.ω ∘ ![a, b])
  · have hindep' : LinearIndependent ℝ ![R.ω a, R.ω b] := by
      rwa [comp_cons_two] at hdep
    have hspan : ∀ p ∈ Submodule.span ℤ (Set.range ![R.ω a, R.ω b]),
        Function.Periodic (R.carrier F) p := by
      refine periodic_of_mem_span_range ![R.ω a, R.ω b] (fun i => ?_)
      fin_cases i
      · exact R.carrier_periodic F hF a ha
      · exact R.carrier_periodic F hF b hb
    have hlat : ∀ p ∈ (⟨R.ω a, R.ω b, hindep'⟩ : PeriodPair).lattice,
        Function.Periodic (R.carrier F) p := by
      intro p hp
      refine hspan p ?_
      rw [range_cons_two]
      exact hp
    exact ellipticHypertranscendenceFree ⟨R.ω a, R.ω b, hindep'⟩ (R.carrier F)
      (R.carrier_meromorphic F hF) hlat (R.carrier_hypertranscendental F hF)
  · exact no_scalarFacetRealization_of_two_omitted_realDependent R hF ha hb hab hdep

/-- **The facet-codimension law for a meromorphic analytic datum.**  Every facet omits at most one
ambient vertex. -/
theorem facetComplementRankOne_of_facetRealization {V : Finset α} {facets : Set (Finset α)}
    (R : ScalarFacetRealization V facets) (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  exact no_scalarFacetRealization_of_two_omitted R hF ha hb hab

/-- **Componentwise channels obey the law with no entirety hypothesis.**  Choosing one
hypertranscendental component per facet reduces an arbitrary family of meromorphic channels to the
scalar analytic datum. -/
theorem channel_facetComplementRankOne {ι : Type*} [Nonempty ι] {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ChannelSRRealization ι facets)
    {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) :=
  facetComplementRankOne_of_facetRealization (R.toScalarFacetRealization hanti V)
    (fun F hF => hsub F (Finset.mem_coe.mp hF))

end GaloisForLFunctions.HTGeometry
