import GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge
import GaloisForLFunctions.HTGeometry.RankTwoRealDependentPeriods

/-!
# What a one-variable realization forces on facet complements

The scalar Stanley–Reisner principalization law asserts that an exact one-variable hypertranscendental
realization makes every facet omit at most one ambient vertex.  Its proof runs through the period-rank
law, whose rank-three case and whose real-dependent rank-two case are unconditional in Lean, while the
rank-two *lattice* case is the classical elliptic statement.  This file records exactly what the
formalized part yields, in full generality:

* `facetComplement_card_le_two_of_scalarSRRealization` — a facet never omits three vertices;
* **`facetComplement_rankOne_or_lattice`** — every facet omits at most one vertex, *or* omits exactly
  two whose translation steps are `ℝ`-linearly independent, i.e. generate a genuine lattice;
* `facetComplementRankOne_of_no_lattice` — hence one-variable period codimension as soon as no two
  distinct steps span a lattice.

The second alternative is precisely the elliptic configuration: it is where the missing Weierstrass
input would be used, and it is the only escape left open by the formalized analysis.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **No facet omits three vertices.**  Three omitted vertices give the facet carrier three
`ℚ`-independent periods, hence a non-discrete period group, hence constancy — contradicting
hypertranscendence. -/
theorem facetComplement_card_le_two_of_scalarSRRealization {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ScalarSRRealization facets)
    {V F : Finset α} (hF : F ∈ facets) : (V \ F).card ≤ 2 := by
  by_contra h
  exact no_scalarSRRealization_of_three_omitted (V := V) hanti R hF (by omega)

/-- **The exact alternative left by the formalized period-rank analysis.**  Under a one-variable
realization every facet either omits at most one ambient vertex — the conclusion of the
principalization law — or omits exactly two, whose translation steps are `ℝ`-linearly independent and
therefore generate a lattice.  The second case is the elliptic configuration. -/
theorem facetComplement_rankOne_or_lattice {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ScalarSRRealization facets)
    {V F : Finset α} (hF : F ∈ facets) :
    (V \ F).card ≤ 1 ∨
      ∃ a b : α, a ≠ b ∧ V \ F = {a, b} ∧ LinearIndependent ℝ (R.ω ∘ ![a, b]) := by
  rcases Nat.lt_or_ge (V \ F).card 2 with hlt | hge
  · exact Or.inl (by omega)
  · have h2 : (V \ F).card = 2 :=
      le_antisymm (facetComplement_card_le_two_of_scalarSRRealization hanti R hF) hge
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2
    refine Or.inr ⟨a, b, hab, hs, ?_⟩
    by_contra hdep
    refine no_scalarFacetRealization_of_two_omitted_realDependent
      (toScalarFacetRealization R hanti V) (Finset.mem_coe.mpr hF) ?_ ?_ hab hdep
    · rw [hs]; simp
    · rw [hs]; simp

/-- **One-variable period codimension when no lattice arises.**  If no two distinct translation steps
are `ℝ`-independent, the elliptic alternative is empty and every facet omits at most one ambient
vertex: the combinatorial output `FacetComplementRankOne` of the period-rank argument. -/
theorem facetComplementRankOne_of_no_lattice {facets : Finset (Finset α)}
    (hanti : FacetAntichain (↑facets : Set (Finset α))) (R : ScalarSRRealization facets)
    {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V)
    (hno : ∀ a b : α, a ≠ b → ¬ LinearIndependent ℝ (R.ω ∘ ![a, b])) :
    FacetComplementRankOne V (↑facets : Set (Finset α)) := by
  intro F hF
  refine ⟨hsub F (Finset.mem_coe.mp hF), ?_⟩
  rcases facetComplement_rankOne_or_lattice hanti R (Finset.mem_coe.mp hF) (V := V) with h | h
  · exact h
  · obtain ⟨a, b, hab, _, hindep⟩ := h
    exact absurd hindep (hno a b hab)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

variable {r s : ℕ}

/-- The boundary wedge is excluded outright: its facets omit `s+1 ≥ 3` vertices, past the bound a
one-variable realization allows. -/
theorem boundaryWedge_facetComplement_too_large (hr : 2 ≤ r) (hs : 2 ≤ s)
    (R : ScalarSRRealization (boundaryWedgeFacetFinset r s)) : False := by
  have hanti : FacetAntichain (↑(boundaryWedgeFacetFinset r s) :
      Set (Finset (BoundaryWedgeVertex r s))) := by
    rw [coe_boundaryWedgeFacetFinset]
    exact facetAntichain hr hs
  have hF : (leftBlock r s).erase none ∈ boundaryWedgeFacetFinset r s :=
    mem_boundaryWedgeFacetFinset.mpr (Or.inl ⟨none, none_mem_leftBlock, rfl⟩)
  have hbound := facetComplement_card_le_two_of_scalarSRRealization hanti R
    (V := (Finset.univ : Finset (BoundaryWedgeVertex r s))) hF
  rw [card_sdiff_leftFacet none_mem_leftBlock] at hbound
  omega

end GaloisForLFunctions.UniformBoundaryWedge
