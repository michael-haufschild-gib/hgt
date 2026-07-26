import GaloisForLFunctions.HTGeometry.StanleyReisnerFacetSeparator
import GaloisForLFunctions.HTGeometry.BoundaryWedgePeriodRankObstruction

/-!
# From a scalar Stanley–Reisner realization to facet period carriers

The two halves of the constraint-dimension argument were formalized separately: the algebra (every
facet carries a nonzero Stanley–Reisner class annihilated by exactly the coordinates it omits,
`exists_facetSeparator`) and the analysis (a carrier with three `ℚ`-independent periods is constant,
so it cannot be hypertranscendental, `no_scalarFacetRealization_of_three_omitted`).  This file builds
the bridge between them.

`ScalarSRRealization` is the realization datum in one complex variable: `ℚ`-independent translation
steps `ω v`, and a carrier map from Stanley–Reisner classes to meromorphic normal-form functions
such that

* multiplication by the vertex coordinate `x_v` acts as the **difference operator** `T_v − 1`
  (`carrier_vertex`) — this is the convention `t_v = 1 + x_v` recorded by
  `stanleyReisnerTranslationClass`;
* a **nonzero** class has a hypertranscendental carrier (`carrier_ht`) — the faithfulness supplied by
  the full nonlinear Stanley–Reisner differential matroid condition.

Neither field mentions periods or dimensions: they are the definition of an exact realization.  From
them, `periodic_carrier_of_mul_eq_zero` *derives* the period identities, and
`toScalarFacetRealization` assembles the facet carriers, turning the algebraic separator into the
analytic datum `ScalarFacetRealization`.  Composing with the period-rank obstruction gives
`boundaryWedge_no_scalarSRRealization`: the boundary wedge has no one-variable realization at all.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **A scalar (one-variable) Stanley–Reisner realization.**  Translation steps together with a
carrier map on Stanley–Reisner classes for which the vertex coordinates act as difference operators
and nonzero classes are hypertranscendental. -/
structure ScalarSRRealization (facets : Finset (Finset α)) where
  /-- The translation step attached to each vertex. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The carrier of a Stanley–Reisner class. -/
  carrier : stanleyReisnerRing ℂ facets → (ℂ → ℂ)
  /-- Carriers are meromorphic in normal form on the whole plane. -/
  carrier_meromorphic : ∀ q, MeromorphicNFOn (carrier q) Set.univ
  /-- The zero class has zero carrier. -/
  carrier_zero : carrier 0 = 0
  /-- The vertex coordinate `x_v` acts as the difference operator `T_v − 1`. -/
  carrier_vertex : ∀ (v : α) (q : stanleyReisnerRing ℂ facets),
    carrier (srVertexX ℂ facets v * q) = fun z => carrier q (z + ω v) - carrier q z
  /-- A nonzero class has a hypertranscendental carrier. -/
  carrier_ht : ∀ q : stanleyReisnerRing ℂ facets, q ≠ 0 → Hypertranscendental (carrier q)

omit [DecidableEq α] in
/-- **Annihilation becomes periodicity.**  If the vertex coordinate `x_v` kills a class, the
difference operator `T_v − 1` kills its carrier, i.e. `ω v` is a period. -/
theorem periodic_carrier_of_mul_eq_zero {facets : Finset (Finset α)}
    (R : ScalarSRRealization facets) {v : α} {q : stanleyReisnerRing ℂ facets}
    (h : srVertexX ℂ facets v * q = 0) : Function.Periodic (R.carrier q) (R.ω v) := by
  have hz : (fun z => R.carrier q (z + R.ω v) - R.carrier q z) = 0 := by
    rw [← R.carrier_vertex v q, h, R.carrier_zero]
  intro z
  have := congrFun hz z
  simpa [sub_eq_zero] using this

/-- **The facet carriers of a scalar realization.**  Each facet's monomial is a nonzero class killed
by exactly the coordinates the facet omits, so its carrier is a hypertranscendental function with all
those steps as periods: the analytic datum required by the period-rank obstruction. -/
noncomputable def toScalarFacetRealization {facets : Finset (Finset α)}
    (R : ScalarSRRealization facets) (hanti : FacetAntichain (↑facets : Set (Finset α)))
    (V : Finset α) : ScalarFacetRealization V (↑facets : Set (Finset α)) where
  ω := R.ω
  indep := R.indep
  carrier := fun F => R.carrier (∏ w ∈ F, srVertexX ℂ facets w)
  carrier_meromorphic := fun _ _ => R.carrier_meromorphic _
  carrier_periodic := fun _F hF _v hv =>
    periodic_carrier_of_mul_eq_zero R
      (srVertexX_mul_srProd_facet_eq_zero facets hanti (Finset.mem_coe.mp hF)
        (Finset.mem_sdiff.mp hv).2)
  carrier_hypertranscendental := fun _F hF =>
    R.carrier_ht _ (srProd_facet_ne_zero facets (Finset.mem_coe.mp hF))

/-- **The period-rank obstruction, in realization form.**  A finite facet antichain with a facet that
omits three vertices of the ambient vertex set admits no scalar realization. -/
theorem no_scalarSRRealization_of_three_omitted {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) {V : Finset α}
    (R : ScalarSRRealization facets) {A : Finset α} (hA : A ∈ facets)
    (hcard : 3 ≤ (V \ A).card) : False :=
  no_scalarFacetRealization_of_three_omitted (toScalarFacetRealization R hanti V)
    (Finset.mem_coe.mpr hA) hcard

omit [DecidableEq α] in
/-- **Dimension-functional packaging.**  A dimension functional characterized as the least realizable
dimension equals `2` once dimension `2` is realizable and dimensions `0` and `1` are excluded.  This
is the corpus idiom for intrinsic dimensions (`FullHTRealizable` with a least-element hypothesis). -/
theorem htDim_eq_two_of_realizability {HTRealizable : ℕ → Prop} {htDim : ℕ}
    (hfull : HTRealizable htDim) (hleast : ∀ d, HTRealizable d → htDim ≤ d)
    (htwo : HTRealizable 2) (hzero : ¬ HTRealizable 0) (hone : ¬ HTRealizable 1) :
    htDim = 2 := by
  have hle : htDim ≤ 2 := hleast 2 htwo
  interval_cases htDim
  · exact absurd hfull hzero
  · exact absurd hfull hone
  · rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

variable {r s : ℕ}

/-- **The boundary wedge has no one-variable realization.**  Every facet omits the whole opposite
block together with the deleted vertex, so the period-rank obstruction applies through the facet
separator: no scalar Stanley–Reisner realization of `Δ_{r,s}` exists, for any `r, s ≥ 2`. -/
theorem boundaryWedge_no_scalarSRRealization (hr : 2 ≤ r) (hs : 2 ≤ s)
    (R : ScalarSRRealization (boundaryWedgeFacetFinset r s)) : False := by
  refine no_scalarSRRealization_of_three_omitted (V := Finset.univ) ?_ R
    (A := (leftBlock r s).erase none) ?_ ?_
  · rw [coe_boundaryWedgeFacetFinset]
    exact facetAntichain hr hs
  · exact mem_boundaryWedgeFacetFinset.mpr (Or.inl ⟨none, none_mem_leftBlock, rfl⟩)
  · rw [card_sdiff_leftFacet none_mem_leftBlock]
    omega

/-- The same statement in `IsEmpty` form. -/
theorem isEmpty_scalarSRRealization (hr : 2 ≤ r) (hs : 2 ≤ s) :
    IsEmpty (ScalarSRRealization (boundaryWedgeFacetFinset r s)) :=
  ⟨fun R => boundaryWedge_no_scalarSRRealization hr hs R⟩

end GaloisForLFunctions.UniformBoundaryWedge
