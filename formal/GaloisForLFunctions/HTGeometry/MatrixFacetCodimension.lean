import GaloisForLFunctions.HTGeometry.SmallTranslationDerivInvariance
import GaloisForLFunctions.HTGeometry.ScalarRealizationFacetComplementBound

/-!
# Finite internal state does not enlarge a facet complement

A facet datum whose carrier takes values in `ℂ^m` and which each omitted translation reproduces up
to a **constant matrix** obeys the same codimension law as the scalar one, with the same two cases
open and closed:

* three omitted vertices are impossible — three `ℚ`-independent steps have a non-discrete integer
  span;
* two omitted vertices with `ℝ`-dependent steps are impossible for the same reason.

Both follow from `differentiallyAlgebraic_component_of_matrix_monodromy`: the components of the
carrier span a finite-dimensional space of entire functions stable under the step group, arbitrarily
small steps make it stable under differentiation, and every component then has a nonzero
constant-coefficient annihilator — contradicting the hypertranscendence of some component.

* `MatrixFacetRealization` — the datum;
* `no_matrixFacetRealization_of_three_omitted`, `no_matrixFacetRealization_of_two_omitted_realDependent`;
* **`matrixFacetComplement_rankOne_or_lattice`** — every facet omits at most one ambient vertex, or
  exactly two whose steps are `ℝ`-independent, i.e. span a lattice;
* `matrix_facetComplementRankOne_of_no_lattice`.

The internal transition matrices are **not** assumed invertible: on a finite-dimensional space a
translation that maps the space into itself is automatically invertible on it.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **A finite-state facet datum.**  `ℚ`-independent translation steps together with, for every
facet, an entire `ℂ^m`-valued carrier which each omitted translation reproduces up to a constant
matrix, some component of which is hypertranscendental. -/
structure MatrixFacetRealization (m : ℕ) (V : Finset α) (facets : Set (Finset α)) where
  /-- The translation steps attached to the vertices. -/
  ω : α → ℂ
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The facet carriers. -/
  carrier : Finset α → (ℂ → (Fin m → ℂ))
  /-- Every component of every carrier is entire. -/
  carrier_entire : ∀ F ∈ facets, ∀ i, Differentiable ℂ (fun z => carrier F z i)
  /-- Each omitted translation reproduces the carrier up to a constant internal matrix. -/
  carrier_monodromy : ∀ F ∈ facets, ∀ v ∈ V \ F,
    ∃ M : Matrix (Fin m) (Fin m) ℂ, ∀ z, carrier F (z + ω v) = M.mulVec (carrier F z)
  /-- Some component of each carrier is hypertranscendental. -/
  carrier_hypertranscendental : ∀ F ∈ facets, ∃ i, Hypertranscendental (fun z => carrier F z i)

/-- Omitted vertices whose steps have a non-discrete integer span kill a finite-state carrier. -/
theorem no_matrixFacetRealization_of_steps {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MatrixFacetRealization m V facets) {F : Finset α} (hF : F ∈ facets)
    {n : ℕ} (e : Fin n → α) (hmem : ∀ i, e i ∈ V \ F)
    (hnd : ¬ DiscreteTopology (Submodule.span ℤ (Set.range (R.ω ∘ e)))) : False := by
  obtain ⟨i, hi⟩ := R.carrier_hypertranscendental F hF
  exact hi (differentiallyAlgebraic_component_of_matrix_monodromy (R.carrier F)
    (R.carrier_entire F hF) (R.ω ∘ e)
    (fun k => (R.carrier_monodromy F hF (e k) (hmem k)).choose)
    (fun k z => (R.carrier_monodromy F hF (e k) (hmem k)).choose_spec z) hnd i)

/-- **Three omitted vertices are impossible.**  Their steps are three `ℚ`-independent complex
numbers, whose integer span is not discrete. -/
theorem no_matrixFacetRealization_of_three_omitted {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MatrixFacetRealization m V facets) {F : Finset α} (hF : F ∈ facets)
    (hcard : 3 ≤ (V \ F).card) : False := by
  classical
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  set q := Finset.equivFinOfCardEq htcard with hq
  set e : Fin 3 → α := fun i => (q.symm i : α) with he
  have hinj : Function.Injective e := by
    intro i j hij
    have hsub : (q.symm i : { x // x ∈ t }) = q.symm j := Subtype.ext hij
    simpa using congrArg q hsub
  have hmem : ∀ i, e i ∈ V \ F := fun i => hts (q.symm i).2
  exact no_matrixFacetRealization_of_steps R hF e hmem
    (not_discrete_intSpan_fin_three (R.ω ∘ e) (R.indep.comp e hinj))

/-- **Two omitted vertices with `ℝ`-dependent steps are impossible.** -/
theorem no_matrixFacetRealization_of_two_omitted_realDependent {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : MatrixFacetRealization m V facets) {F : Finset α}
    (hF : F ∈ facets) {a b : α} (ha : a ∈ V \ F) (hb : b ∈ V \ F) (hab : a ≠ b)
    (hdep : ¬ LinearIndependent ℝ (R.ω ∘ ![a, b])) : False := by
  have hmem : ∀ i : Fin 2, ![a, b] i ∈ V \ F := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  exact no_matrixFacetRealization_of_steps R hF ![a, b] hmem
    (not_discrete_intSpan_fin_two_of_not_linearIndependent_real (R.ω ∘ ![a, b])
      (R.indep.comp _ (injective_cons_two hab)) hdep)

/-- **The finite-state codimension alternative.**  Every facet either omits at most one ambient
vertex or omits exactly two, whose translation steps are `ℝ`-linearly independent and therefore span
a lattice.  This is the scalar alternative `facetComplement_rankOne_or_lattice` verbatim, now with an
arbitrary constant internal state. -/
theorem matrixFacetComplement_rankOne_or_lattice {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MatrixFacetRealization m V facets) {F : Finset α} (hF : F ∈ facets) :
    (V \ F).card ≤ 1 ∨
      ∃ a b : α, a ≠ b ∧ V \ F = {a, b} ∧ LinearIndependent ℝ (R.ω ∘ ![a, b]) := by
  classical
  rcases Nat.lt_or_ge (V \ F).card 2 with hlt | hge
  · exact Or.inl (by omega)
  · have hle : (V \ F).card ≤ 2 := by
      by_contra h
      exact no_matrixFacetRealization_of_three_omitted R hF (by omega)
    have h2 : (V \ F).card = 2 := le_antisymm hle hge
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2
    refine Or.inr ⟨a, b, hab, hs, ?_⟩
    by_contra hdep
    refine no_matrixFacetRealization_of_two_omitted_realDependent R hF ?_ ?_ hab hdep
    · rw [hs]; simp
    · rw [hs]; simp

/-- **Finite-state period codimension when no lattice arises.**  If no two distinct translation steps
are `ℝ`-independent, every facet omits at most one ambient vertex — the conclusion `(6)` of the
principalization law, now for an arbitrary constant internal channel. -/
theorem matrix_facetComplementRankOne_of_no_lattice {m : ℕ} {V : Finset α}
    {facets : Set (Finset α)} (R : MatrixFacetRealization m V facets)
    (hsub : ∀ F ∈ facets, F ⊆ V)
    (hno : ∀ a b : α, a ≠ b → ¬ LinearIndependent ℝ (R.ω ∘ ![a, b])) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  rcases matrixFacetComplement_rankOne_or_lattice R hF with h | ⟨a, b, hab, _, hindep⟩
  · exact h
  · exact absurd hindep (hno a b hab)

end GaloisForLFunctions.HTGeometry
