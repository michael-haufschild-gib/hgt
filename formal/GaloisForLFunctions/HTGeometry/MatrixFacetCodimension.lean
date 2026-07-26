import GaloisForLFunctions.HTGeometry.ShiftStableLatticeStructure
import GaloisForLFunctions.HTGeometry.ScalarRealizationFacetComplementBound

/-!
# Finite internal state does not enlarge a facet complement

A facet datum whose carrier takes values in `ℂ^m` and which each omitted translation reproduces up
to a **constant matrix** obeys the facet-codimension law unconditionally: no facet omits two
vertices, so every facet omits at most one.

The reason is `differentiallyAlgebraic_component_of_matrix_monodromy_two`: the components of the
carrier span a finite-dimensional space of entire functions stable under both omitted translations,
and such a space sits inside a finite-dimensional derivation-invariant space, so every component has
a nonzero constant-coefficient annihilator — contradicting the hypertranscendence of some component.
Neither invertibility of the internal matrices nor any condition on the two steps beyond
`ℚ`-independence is used; in particular the lattice configuration, which is the last open
alternative in the scalar meromorphic setting, is closed here.

* `MatrixFacetRealization` — the datum;
* **`no_matrixFacetRealization_of_two_omitted`**;
* **`matrix_facetComplementRankOne`** — every facet omits at most one ambient vertex.
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

/-- **Two omitted vertices are impossible.**  Their steps are `ℚ`-independent, so every component of
the carrier is differentially algebraic. -/
theorem no_matrixFacetRealization_of_two_omitted {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MatrixFacetRealization m V facets) {F : Finset α} (hF : F ∈ facets) {u v : α}
    (hu : u ∈ V \ F) (hv : v ∈ V \ F) (huv : u ≠ v) : False := by
  obtain ⟨A, hA⟩ := R.carrier_monodromy F hF u hu
  obtain ⟨B, hB⟩ := R.carrier_monodromy F hF v hv
  obtain ⟨i, hi⟩ := R.carrier_hypertranscendental F hF
  have hindep : LinearIndependent ℚ ![R.ω u, R.ω v] := by
    rw [← comp_cons_two]
    exact R.indep.comp _ (injective_cons_two huv)
  exact hi (differentiallyAlgebraic_component_of_matrix_monodromy_two (R.carrier F)
    (R.carrier_entire F hF) hindep A B hA hB i)

/-- **The finite-state facet-codimension law.**  Every facet omits at most one ambient vertex.
Unconditional: an arbitrary constant internal channel supplies no extra analytic direction. -/
theorem matrix_facetComplementRankOne {m : ℕ} {V : Finset α} {facets : Set (Finset α)}
    (R : MatrixFacetRealization m V facets) (hsub : ∀ F ∈ facets, F ⊆ V) :
    FacetComplementRankOne V facets := by
  intro F hF
  refine ⟨hsub F hF, ?_⟩
  by_contra hlt
  have h2 : 2 ≤ (V \ F).card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp h2
  exact no_matrixFacetRealization_of_two_omitted R hF hu hv huv

end GaloisForLFunctions.HTGeometry
