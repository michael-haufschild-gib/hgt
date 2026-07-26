import GaloisForLFunctions.HTGeometry.EllipticFreeFacetCodimension

/-!
# Entire realizations need no elliptic input

The one alternative left open by `facetComplement_rankOne_or_lattice` is a facet carrier that is a
hypertranscendental function invariant under a full lattice.  For a **meromorphic** carrier ruling
that out is the elliptic structure theorem, packaged as `EllipticHypertranscendenceFree`.  For an
**entire** carrier it is Liouville's theorem: a lattice-periodic entire function has compact range,
hence is bounded, hence constant.

Since the periodic-pencil realization theorem produces *entire* systems, this removes the elliptic
input entirely for the realizations that actually arise:

* `const_of_lattice_periodic_differentiable` — elliptic Liouville, from mathlib's
  `IsZLattice.isCompact_range_of_periodic` and `Differentiable.apply_eq_apply_of_bounded`;
* `not_hypertranscendental_of_lattice_periodic_differentiable`;
* **`facetComplementRankOne_of_entire`** — for a one-variable realization with entire carriers, every
  facet omits at most one ambient vertex.  Unconditional: no named analytic input.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **Elliptic Liouville.**  An entire function invariant under a full lattice is constant: its range
is the continuous image of a compact fundamental set, hence bounded. -/
theorem const_of_lattice_periodic_differentiable (L : PeriodPair) {f : ℂ → ℂ}
    (hdiff : Differentiable ℂ f) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    ∀ x y, f x = f y := by
  intro x y
  exact hdiff.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous
      (fun z w hw => hper w hw z)).isBounded x y

/-- An entire function with a full lattice of periods is not hypertranscendental. -/
theorem not_hypertranscendental_of_lattice_periodic_differentiable (L : PeriodPair) {f : ℂ → ℂ}
    (hdiff : Differentiable ℂ f) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    ¬ Hypertranscendental f :=
  not_hypertranscendental_of_const (const_of_lattice_periodic_differentiable L hdiff hper)

/-- **The facet-codimension law for entire realizations.**  A one-variable realization whose carriers
are entire forces every facet to omit at most one ambient vertex.  The rank-three and real-dependent
rank-two cases are excluded by period rigidity as before; the remaining lattice case is excluded by
Liouville's theorem, so no elliptic structure theory is needed. -/
theorem facetComplementRankOne_of_entire {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ScalarSRRealization facets)
    (hentire : ∀ q, Differentiable ℂ (R.carrier q))
    {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) := by
  intro F hF
  refine ⟨hsub F (Finset.mem_coe.mp hF), ?_⟩
  rcases facetComplement_rankOne_or_lattice hanti R (Finset.mem_coe.mp hF) (V := V) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab, hs, hindep⟩ := h
    have hindep' : LinearIndependent ℝ ![R.ω a, R.ω b] := by
      rwa [comp_cons_two] at hindep
    have haV : a ∈ V \ F := by rw [hs]; simp
    have hbV : b ∈ V \ F := by rw [hs]; simp
    have haF : a ∉ F := (Finset.mem_sdiff.mp haV).2
    have hbF : b ∉ F := (Finset.mem_sdiff.mp hbV).2
    set L : PeriodPair := ⟨R.ω a, R.ω b, hindep'⟩ with hL
    set q := ∏ w ∈ F, srVertexX ℂ facets w with hq
    have hqne : q ≠ 0 := srProd_facet_ne_zero facets (Finset.mem_coe.mp hF)
    have hpera : Function.Periodic (R.carrier q) (R.ω a) :=
      periodic_carrier_of_mul_eq_zero R
        (srVertexX_mul_srProd_facet_eq_zero facets hanti (Finset.mem_coe.mp hF) haF)
    have hperb : Function.Periodic (R.carrier q) (R.ω b) :=
      periodic_carrier_of_mul_eq_zero R
        (srVertexX_mul_srProd_facet_eq_zero facets hanti (Finset.mem_coe.mp hF) hbF)
    have hspan : ∀ p ∈ Submodule.span ℤ (Set.range ![R.ω a, R.ω b]),
        Function.Periodic (R.carrier q) p := by
      refine periodic_of_mem_span_range ![R.ω a, R.ω b] (fun i => ?_)
      fin_cases i
      · exact hpera
      · exact hperb
    have hlat : ∀ p ∈ L.lattice, Function.Periodic (R.carrier q) p := by
      intro p hp
      refine hspan p ?_
      rw [range_cons_two]
      exact hp
    exact not_hypertranscendental_of_lattice_periodic_differentiable L (hentire q) hlat
      (R.carrier_ht q hqne)

end GaloisForLFunctions.HTGeometry
