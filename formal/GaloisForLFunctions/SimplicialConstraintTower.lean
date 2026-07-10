import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Tactic

/-!
# Simplicial constraint towers

This file begins the unconditional Lean formalization of the combinatorial layer behind the
all-order multiple-elliptic-gamma structural differential matroid. It isolates two-thickness as
the exact local coface condition, proves that purity and ridge thickness imply it, and records the
antichain-star lemma which removes purity from the global maximal-face gluing argument.

No special-function, differential-algebraic, or Picard--Vessiot hypothesis occurs here.
-/

namespace GaloisForLFunctions

noncomputable section

open Finset

variable {α : Type*} [DecidableEq α]

/-- A face of a facet family is a finite set contained in one of its facets. -/
def IsFaceOf (facets : Set (Finset α)) (J : Finset α) : Prop :=
  ∃ F ∈ facets, J ⊆ F

/-- A facet family is an inclusion antichain. -/
def FacetAntichain (facets : Set (Finset α)) : Prop :=
  ∀ ⦃F⦄, F ∈ facets → ∀ ⦃G⦄, G ∈ facets → F ⊆ G → F = G

/-- Every nonfacet face has two distinct immediate coface directions. No purity assumption is
included. -/
def TwoThick (facets : Set (Finset α)) : Prop :=
  ∀ J, IsFaceOf facets J → J ∉ facets →
    ∃ q u : α, q ≠ u ∧ q ∉ J ∧ u ∉ J ∧
      IsFaceOf facets (insert q J) ∧ IsFaceOf facets (insert u J)

/-- Every facet in the family has the same number of vertices. -/
def PureOfCard (facets : Set (Finset α)) (d : ℕ) : Prop :=
  ∀ ⦃F⦄, F ∈ facets → F.card = d

/-- Every codimension-one face lies in two distinct facets. -/
def RidgeThick (facets : Set (Finset α)) (d : ℕ) : Prop :=
  ∀ R, IsFaceOf facets R → R.card + 1 = d →
    ∃ F₁ ∈ facets, ∃ F₂ ∈ facets, F₁ ≠ F₂ ∧ R ⊆ F₁ ∧ R ⊆ F₂

/-- If a star in a facet antichain contains a facet other than `J`, then every seed `A ⊆ J`
has a fresh vertex in `J \ A`. This is the termination step for nested-star gluing with facets of
unequal cardinalities. -/
theorem exists_fresh_vertex_of_facetAntichain_star_nontrivial
    {facets : Set (Finset α)} (hanti : FacetAntichain facets)
    {A J G : Finset α} (hJ : J ∈ facets) (hG : G ∈ facets)
    (hAG : A ⊆ G) (hJG : J ≠ G) :
    ∃ q, q ∈ J ∧ q ∉ A := by
  by_contra h
  push Not at h
  have hJA : J ⊆ A := fun q hqJ => h q hqJ
  have hJGsub : J ⊆ G := hJA.trans hAG
  exact hJG (hanti hJ hG hJGsub)

omit [DecidableEq α] in
/-- Seeding a facet antichain star by a facet makes that star a singleton. -/
theorem eq_of_mem_facetAntichain_of_facet_subset
    {facets : Set (Finset α)} (hanti : FacetAntichain facets)
    {J G : Finset α} (hJ : J ∈ facets) (hG : G ∈ facets) (hJG : J ⊆ G) : G = J :=
  (hanti hJ hG hJG).symm

/-- The facets of the full `d`-uniform skeleton on a finite vertex set. -/
def uniformFacets (V : Finset α) (d : ℕ) : Set (Finset α) :=
  {F | F ⊆ V ∧ F.card = d}

omit [DecidableEq α] in
@[simp]
theorem mem_uniformFacets {V F : Finset α} {d : ℕ} :
    F ∈ uniformFacets V d ↔ F ⊆ V ∧ F.card = d :=
  Iff.rfl

omit [DecidableEq α] in
/-- The full uniform skeleton is pure. -/
@[aesop safe]
theorem pureOfCard_uniformFacets (V : Finset α) (d : ℕ) :
    PureOfCard (uniformFacets V d) d := by
  intro F hF
  exact hF.2

/-- If the ambient vertex set has more than `d` vertices, every ridge of its full uniform
skeleton belongs to two distinct facets. -/
@[aesop safe]
theorem ridgeThick_uniformFacets {V : Finset α} {d : ℕ} (hdV : d < V.card) :
    RidgeThick (uniformFacets V d) d := by
  intro R hRface hRcard
  rcases hRface with ⟨F, hF, hRF⟩
  have hRV : R ⊆ V := hRF.trans hF.1
  have hdiff : 1 < (V \ R).card := by
    rw [card_sdiff_of_subset hRV]
    omega
  rcases one_lt_card.mp hdiff with ⟨q, hq, u, hu, hqu⟩
  have hqV := (mem_sdiff.mp hq).1
  have hqR := (mem_sdiff.mp hq).2
  have huV := (mem_sdiff.mp hu).1
  have huR := (mem_sdiff.mp hu).2
  have hcardq : (insert q R).card = d := by rw [card_insert_of_notMem hqR, hRcard]
  have hcardu : (insert u R).card = d := by rw [card_insert_of_notMem huR, hRcard]
  have hne : insert q R ≠ insert u R := by
    intro h
    have hqin : q ∈ insert u R := by rw [← h]; simp
    exact hqu ((mem_insert.mp hqin).resolve_right hqR)
  exact ⟨insert q R, ⟨insert_subset hqV hRV, hcardq⟩,
    insert u R, ⟨insert_subset huV hRV, hcardu⟩,
    hne, subset_insert q R, subset_insert u R⟩

/-- In a pure ridge-thick facet family, every proper face has two distinct immediate coface
directions. This is the combinatorial input needed to replace the full simplex skeleton by an
arbitrary pure constraint complex in the paired-telescoping induction. -/
@[aesop safe]
theorem exists_two_coface_directions_of_pure_ridgeThick
    {facets : Set (Finset α)} {d : ℕ}
    (hpure : PureOfCard facets d) (hthick : RidgeThick facets d)
    {J : Finset α} (hJface : IsFaceOf facets J) (hJcard : J.card < d) :
    ∃ q u : α, q ≠ u ∧ q ∉ J ∧ u ∉ J ∧
      IsFaceOf facets (insert q J) ∧ IsFaceOf facets (insert u J) := by
  rcases hJface with ⟨F, hFfacets, hJF⟩
  by_cases hridge : J.card + 1 = d
  · rcases hthick J ⟨F, hFfacets, hJF⟩ hridge with
      ⟨F₁, hF₁facets, F₂, hF₂facets, hF₁F₂, hJF₁, hJF₂⟩
    have hdiff₁ : (F₁ \ J).card = 1 := by
      rw [card_sdiff_of_subset hJF₁, hpure hF₁facets]
      omega
    have hdiff₂ : (F₂ \ J).card = 1 := by
      rw [card_sdiff_of_subset hJF₂, hpure hF₂facets]
      omega
    rcases card_eq_one.mp hdiff₁ with ⟨q, hq⟩
    rcases card_eq_one.mp hdiff₂ with ⟨u, hu⟩
    have hqmem : q ∈ F₁ \ J := by simp [hq]
    have humem : u ∈ F₂ \ J := by simp [hu]
    have hqu : q ≠ u := by
      intro h
      apply hF₁F₂
      calc
        F₁ = J ∪ (F₁ \ J) := (union_sdiff_of_subset hJF₁).symm
        _ = J ∪ {q} := by rw [hq]
        _ = J ∪ {u} := by rw [h]
        _ = J ∪ (F₂ \ J) := by rw [hu]
        _ = F₂ := union_sdiff_of_subset hJF₂
    refine ⟨q, u, hqu, (mem_sdiff.mp hqmem).2, (mem_sdiff.mp humem).2, ?_, ?_⟩
    · exact ⟨F₁, hF₁facets, insert_subset (mem_sdiff.mp hqmem).1 hJF₁⟩
    · exact ⟨F₂, hF₂facets, insert_subset (mem_sdiff.mp humem).1 hJF₂⟩
  · have hgap : J.card + 1 < d := by omega
    have hdiff : 1 < (F \ J).card := by
      rw [card_sdiff_of_subset hJF, hpure hFfacets]
      omega
    rcases one_lt_card.mp hdiff with ⟨q, hq, u, hu, hqu⟩
    refine ⟨q, u, hqu, (mem_sdiff.mp hq).2, (mem_sdiff.mp hu).2, ?_, ?_⟩
    · exact ⟨F, hFfacets, insert_subset (mem_sdiff.mp hq).1 hJF⟩
    · exact ⟨F, hFfacets, insert_subset (mem_sdiff.mp hu).1 hJF⟩

/-- Pure ridge-thick facet families are two-thick. Purity is a sufficient local criterion, not a
necessary global hypothesis for the constraint-tower theorem. -/
theorem twoThick_of_pure_ridgeThick
    {facets : Set (Finset α)} {d : ℕ}
    (hpure : PureOfCard facets d) (hthick : RidgeThick facets d) :
    TwoThick facets := by
  intro J hJface hJnotfacet
  rcases hJface with ⟨F, hFfacets, hJF⟩
  have hJle : J.card ≤ d := by
    rw [← hpure hFfacets]
    exact card_le_card hJF
  have hJlt : J.card < d := by
    apply lt_of_le_of_ne hJle
    intro hcard
    have hJF_eq : J = F := eq_of_subset_of_card_le hJF (by simpa [hpure hFfacets] using hcard.ge)
    exact hJnotfacet (hJF_eq ▸ hFfacets)
  exact exists_two_coface_directions_of_pure_ridgeThick hpure hthick
    ⟨F, hFfacets, hJF⟩ hJlt

end

end GaloisForLFunctions
