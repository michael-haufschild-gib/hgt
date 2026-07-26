import GaloisForLFunctions.HTGeometry.ScalarRealizationFacetComplementBound
import GaloisForLFunctions.HTGeometry.WeierstrassPDifferentiallyAlgebraic

/-!
# The facet-codimension law modulo one named analytic input

`facetComplement_rankOne_or_lattice` leaves exactly one alternative open: a facet omitting two
vertices whose translation steps are `ℝ`-independent.  Those two steps are then a `PeriodPair`, and
the facet carrier is a hypertranscendental meromorphic function invariant under the whole lattice they
span — that is, a hypertranscendental *elliptic* function.

`EllipticHypertranscendenceFree` names exactly the statement that no such function exists (equivalently
that every elliptic function is differentially algebraic).  Modulo it,
`facetComplementRankOne_of_ellipticFree` proves the facet-codimension law `(6)` of the scalar
Stanley–Reisner principalization argument in full generality.

The Weierstrass function itself is already known to be differentially algebraic
(`differentiallyAlgebraic_weierstrassP`, from mathlib's `derivWeierstrassP_sq`), so the named input is
the *structure* half: that every lattice-periodic meromorphic function lies in `ℂ(℘, ℘')`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **The elliptic input of the period-rank law.**  No hypertranscendental meromorphic function is
invariant under a full lattice; equivalently, every elliptic function is differentially algebraic.
It is proved in `EllipticHypertranscendenceFreeProof`, so every result stated relative to it is
unconditional. -/
def EllipticHypertranscendenceFree : Prop :=
  ∀ (L : PeriodPair) (f : ℂ → ℂ), MeromorphicNFOn f Set.univ →
    (∀ p ∈ L.lattice, Function.Periodic f p) → ¬ Hypertranscendental f

omit [DecidableEq α] in
/-- The pair of steps attached to two vertices, as a tuple. -/
theorem comp_cons_two {R : Type*} (ω : α → R) (a b : α) : (ω ∘ ![a, b]) = ![ω a, ω b] := by
  funext i
  fin_cases i <;> rfl

omit [DecidableEq α] in
/-- The range of a two-element tuple is the corresponding pair. -/
theorem range_cons_two {R : Type*} (x y : R) : Set.range ![x, y] = {x, y} := by
  ext u
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- **The facet-codimension law, modulo the elliptic input.**  If no hypertranscendental function has
a full lattice of periods, then a one-variable realization forces every facet to omit at most one
ambient vertex — the conclusion `(6)` of the scalar Stanley–Reisner principalization argument. -/
theorem facetComplementRankOne_of_ellipticFree (hell : EllipticHypertranscendenceFree)
    {facets : Finset (Finset α)} (hanti : FacetAntichain (↑facets : Set (Finset α)))
    (R : ScalarSRRealization facets) {V : Finset α} (hsub : ∀ F ∈ facets, F ⊆ V) :
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
    exact hell L (R.carrier q) (R.carrier_meromorphic q) hlat (R.carrier_ht q hqne)

end GaloisForLFunctions.HTGeometry
