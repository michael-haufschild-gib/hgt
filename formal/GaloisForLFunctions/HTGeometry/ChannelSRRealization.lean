import GaloisForLFunctions.HTGeometry.EntireFacetRealizationCodimension
import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetSeparator

/-!
# Vectorized (channel) realizations do not escape the codimension law

Componentwise-channel stability: replacing a single meromorphic carrier by an arbitrary family of
channels, all translated by the same steps, changes nothing.  A `ChannelSRRealization` carries a
family `ι` of components with the vertex coordinates acting componentwise as difference operators and
with **some** component hypertranscendental for each nonzero Stanley–Reisner class — the vector form
of the full-matroid faithfulness.

Choosing, for each facet, one hypertranscendental component of its separator class produces an
ordinary `ScalarFacetRealization` (`ChannelSRRealization.toScalarFacetRealization`), so every result
proved for the scalar analytic datum applies verbatim.  In particular
`channel_facetComplementRankOne_of_entire`: for entire channels every facet omits at most one ambient
vertex, unconditionally.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α] {ι : Type*}

/-- **A vectorized (channel) one-variable realization.**  A family of components, translated
componentwise by the same steps, with some component hypertranscendental on each nonzero class. -/
structure ChannelSRRealization (ι : Type*) (facets : Finset (Finset α)) where
  /-- The translation step attached to each vertex. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The channel family attached to a Stanley–Reisner class. -/
  carrier : stanleyReisnerRing ℂ facets → (ℂ → ι → ℂ)
  /-- The zero class has zero carrier. -/
  carrier_zero : carrier 0 = 0
  /-- The vertex coordinate `x_v` acts componentwise as the difference operator `T_v − 1`. -/
  carrier_vertex : ∀ (v : α) (q : stanleyReisnerRing ℂ facets),
    carrier (srVertexX ℂ facets v * q) = fun z => carrier q (z + ω v) - carrier q z
  /-- Every component is meromorphic in normal form. -/
  carrier_meromorphic : ∀ (q : stanleyReisnerRing ℂ facets) (i : ι),
    MeromorphicNFOn (fun z => carrier q z i) Set.univ
  /-- A nonzero class has a hypertranscendental component. -/
  carrier_ht : ∀ q : stanleyReisnerRing ℂ facets, q ≠ 0 →
    ∃ i : ι, Hypertranscendental (fun z => carrier q z i)

omit [DecidableEq α] in
/-- Annihilation becomes componentwise periodicity. -/
theorem channel_periodic_of_mul_eq_zero {facets : Finset (Finset α)}
    (R : ChannelSRRealization ι facets) {v : α} {q : stanleyReisnerRing ℂ facets}
    (h : srVertexX ℂ facets v * q = 0) (i : ι) :
    Function.Periodic (fun z => R.carrier q z i) (R.ω v) := by
  have hz : (fun z => R.carrier q (z + R.ω v) - R.carrier q z) = 0 := by
    rw [← R.carrier_vertex v q, h, R.carrier_zero]
  intro z
  have hzi := congrFun (congrFun hz z) i
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hzi
  exact hzi

open Classical in
/-- A hypertranscendental component chosen for each facet class. -/
noncomputable def channelComponent [Nonempty ι] {facets : Finset (Finset α)}
    (R : ChannelSRRealization ι facets) (F : Finset α) : ι :=
  if h : (∏ w ∈ F, srVertexX ℂ facets w) = 0 then Classical.arbitrary ι
  else (R.carrier_ht _ h).choose

omit [DecidableEq α] in
theorem channelComponent_spec [Nonempty ι] {facets : Finset (Finset α)}
    (R : ChannelSRRealization ι facets) {F : Finset α}
    (hF : (∏ w ∈ F, srVertexX ℂ facets w) ≠ 0) :
    Hypertranscendental
      (fun z => R.carrier (∏ w ∈ F, srVertexX ℂ facets w) z (channelComponent R F)) := by
  rw [channelComponent, dif_neg hF]
  exact (R.carrier_ht _ hF).choose_spec

/-- **A channel realization yields an ordinary analytic facet datum.**  Take, for each facet, one
hypertranscendental component of its separator class. -/
noncomputable def ChannelSRRealization.toScalarFacetRealization [Nonempty ι]
    {facets : Finset (Finset α)} (R : ChannelSRRealization ι facets)
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (V : Finset α) :
    ScalarFacetRealization V (↑facets : Set (Finset α)) where
  ω := R.ω
  indep := R.indep
  carrier := fun F z => R.carrier (∏ w ∈ F, srVertexX ℂ facets w) z (channelComponent R F)
  carrier_meromorphic := fun _ _ => R.carrier_meromorphic _ _
  carrier_periodic := fun _F hF _v hv =>
    channel_periodic_of_mul_eq_zero R
      (srVertexX_mul_srProd_facet_eq_zero facets hanti (Finset.mem_coe.mp hF)
        (Finset.mem_sdiff.mp hv).2) _
  carrier_hypertranscendental := fun _F hF =>
    channelComponent_spec R (srProd_facet_ne_zero facets (Finset.mem_coe.mp hF))

/-- **Channel realizations obey the same codimension law.**  If every chosen component is entire,
every facet omits at most one ambient vertex — vectorization supplies no extra analytic direction. -/
theorem channel_facetComplementRankOne_of_entire [Nonempty ι] {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ChannelSRRealization ι facets)
    {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V)
    (hentire : ∀ F ∈ facets, Differentiable ℂ
      (fun z => R.carrier (∏ w ∈ F, srVertexX ℂ facets w) z (channelComponent R F))) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) :=
  facetComplementRankOne_of_facetRealization_entire (R.toScalarFacetRealization hanti V)
    (fun F hF => hentire F (Finset.mem_coe.mp hF))
    (fun F hF => hsub F (Finset.mem_coe.mp hF))

end GaloisForLFunctions.HTGeometry
