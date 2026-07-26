import GaloisForLFunctions.HTGeometry.BoundaryWedgeFacetComplement
import GaloisForLFunctions.HTGeometry.RankThreePeriods
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# One-variable realizations die on facets that omit three vertices

The period-rank obstruction to a scalar (one-variable) hypertranscendental realization of a finite
facet family, and its application to the boundary wedge.

A one-variable realization supplies `ℚ`-independent translation steps `ω v` and, for each facet `F`,
a meromorphic **facet carrier** that is hypertranscendental and is invariant under exactly the
translations the facet omits.  That is packaged as `ScalarFacetRealization`.

If some facet omits three vertices, the carrier acquires three `ℚ`-independent periods.  A rank-three
integer period group in `ℂ` cannot be discrete, so the carrier is constant
(`meromorphicNF_constant_of_rankThree_periods`), and a constant function is differentially algebraic
(`differentiallyAlgebraic_of_const`) — contradicting hypertranscendence.  Hence
`no_scalarFacetRealization_of_three_omitted`.

For the boundary wedge `Δ_{r,s} = ∂σ^r ∨ ∂σ^s` every facet omits the whole opposite block together
with the deleted vertex, so its complement has cardinality `s+1 ≥ 3`
(`card_sdiff_leftFacet`): `boundaryWedge_no_scalarFacetRealization`.  This is the analytic half of the
lower bound `htDim ≥ 2` for the whole two-parameter family, sitting on top of the combinatorial half
`not_facetComplementRankOne`.
-/

open Finset

namespace GaloisForLFunctions

/-! ### Constants are differentially algebraic -/

/-- A constant function satisfies the order-zero relation `y₀ − c = 0`, so it is differentially
algebraic and in particular not hypertranscendental. -/
theorem differentiallyAlgebraic_of_const {f : ℂ → ℂ} (h : ∀ x y, f x = f y) :
    DifferentiallyAlgebraic f := by
  refine differentiallyAlgebraic_of_algebraic (Polynomial.X - Polynomial.C (f 0))
    (Polynomial.X_sub_C_ne_zero _) (fun z => ?_)
  simp [h z 0]

theorem not_hypertranscendental_of_const {f : ℂ → ℂ} (h : ∀ x y, f x = f y) :
    ¬ Hypertranscendental f :=
  fun hf => hf (differentiallyAlgebraic_of_const h)

/-! ### Periods form a subgroup -/

/-- Periodicity at a family of steps propagates to their integer span. -/
theorem periodic_of_mem_span_range {ι : Type*} {f : ℂ → ℂ} (w : ι → ℂ)
    (h : ∀ i, Function.Periodic f (w i)) :
    ∀ p ∈ Submodule.span ℤ (Set.range w), Function.Periodic f p := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => intro x; simp
  | add x y _ _ hx hy => exact hx.add_period hy
  | smul a x _ hx => exact hx.zsmul a

/-! ### The realization interface -/

/-- **A one-variable exact realization datum.**  `ℚ`-independent translation steps together with,
for every facet, a meromorphic hypertranscendental carrier invariant under every translation the
facet omits.  This is exactly the analytic output of the facet-separator and isolated-carrier steps
of the scalar Stanley–Reisner principalization argument. -/
structure ScalarFacetRealization {α : Type*} [DecidableEq α]
    (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers. -/
  carrier : Finset α → (ℂ → ℂ)
  /-- Each carrier is meromorphic in normal form on the whole plane. -/
  carrier_meromorphic : ∀ F ∈ facets, MeromorphicNFOn (carrier F) Set.univ
  /-- Each carrier is invariant under the translations its facet omits. -/
  carrier_periodic : ∀ F ∈ facets, ∀ v ∈ V \ F, Function.Periodic (carrier F) (ω v)
  /-- Each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, Hypertranscendental (carrier F)

/-- **Period-rank obstruction.**  A facet that omits three vertices gives its carrier three
`ℚ`-independent periods; a rank-three integer period group in `ℂ` is not discrete, so the carrier is
constant, hence differentially algebraic — contradicting hypertranscendence.  No one-variable
realization survives. -/
theorem no_scalarFacetRealization_of_three_omitted {α : Type*} [DecidableEq α]
    {V : Finset α} {facets : Set (Finset α)} (R : ScalarFacetRealization V facets)
    {F : Finset α} (hF : F ∈ facets) (hcard : 3 ≤ (V \ F).card) : False := by
  classical
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  set g := Finset.equivFinOfCardEq htcard with hg
  set e : Fin 3 → α := fun i => (g.symm i : α) with he
  have hinj : Function.Injective e := by
    intro i j hij
    have hsub : (g.symm i : { x // x ∈ t }) = g.symm j := Subtype.ext hij
    simpa using congrArg g hsub
  have hmem : ∀ i, e i ∈ V \ F := fun i => hts (g.symm i).2
  have hindep : LinearIndependent ℚ (R.ω ∘ e) := R.indep.comp e hinj
  have hper : ∀ i, Function.Periodic (R.carrier F) ((R.ω ∘ e) i) :=
    fun i => R.carrier_periodic F hF (e i) (hmem i)
  have hspan := periodic_of_mem_span_range (f := R.carrier F) (R.ω ∘ e) hper
  have hconst := meromorphicNF_constant_of_rankThree_periods (R.carrier F)
    (R.carrier_meromorphic F hF) (R.ω ∘ e) hindep hspan
  exact not_hypertranscendental_of_const hconst (R.carrier_hypertranscendental F hF)

end GaloisForLFunctions

namespace GaloisForLFunctions.UniformBoundaryWedge

variable {r s : ℕ}

/-- **The boundary wedge admits no one-variable realization.**  Every facet omits the whole opposite
block together with the deleted vertex, so its complement has cardinality `s+1 ≥ 3`; the period-rank
obstruction then rules out any scalar realization, uniformly in `r, s ≥ 2`.  This is the analytic
half of `htDim ≥ 2`, matching the combinatorial half `not_facetComplementRankOne`. -/
theorem boundaryWedge_no_scalarFacetRealization (hs : 2 ≤ s)
    (R : ScalarFacetRealization (Finset.univ : Finset (BoundaryWedgeVertex r s))
      (boundaryWedgeFacets r s)) : False := by
  refine no_scalarFacetRealization_of_three_omitted R
    (Or.inl ⟨none, none_mem_leftBlock, rfl⟩) ?_
  rw [card_sdiff_leftFacet none_mem_leftBlock]
  omega

/-- The same obstruction in `IsEmpty` form. -/
theorem isEmpty_scalarFacetRealization (hs : 2 ≤ s) :
    IsEmpty (ScalarFacetRealization (Finset.univ : Finset (BoundaryWedgeVertex r s))
      (boundaryWedgeFacets r s)) :=
  ⟨fun R => boundaryWedge_no_scalarFacetRealization hs R⟩

end GaloisForLFunctions.UniformBoundaryWedge
