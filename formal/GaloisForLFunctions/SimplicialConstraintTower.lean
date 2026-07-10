import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Tactic

/-!
# Simplicial constraint towers

This file begins the unconditional Lean formalization of the combinatorial layer behind the
all-order multiple-elliptic-gamma structural differential matroid.  It proves that the full
simplex skeleton is not essential: purity and ridge thickness already force the two distinct
coface directions required by the paired-telescoping descent.

No special-function, differential-algebraic, or Picard--Vessiot hypothesis occurs here.
-/

namespace GaloisForLFunctions

noncomputable section

open Finset

variable {α : Type*} [DecidableEq α]

/-- A face of a facet family is a finite set contained in one of its facets. -/
def IsFaceOf (facets : Set (Finset α)) (J : Finset α) : Prop :=
  ∃ F ∈ facets, J ⊆ F

/-- Every facet in the family has the same number of vertices. -/
def PureOfCard (facets : Set (Finset α)) (d : ℕ) : Prop :=
  ∀ ⦃F⦄, F ∈ facets → F.card = d

/-- Every codimension-one face lies in two distinct facets. -/
def RidgeThick (facets : Set (Finset α)) (d : ℕ) : Prop :=
  ∀ R, IsFaceOf facets R → R.card + 1 = d →
    ∃ F₁ ∈ facets, ∃ F₂ ∈ facets, F₁ ≠ F₂ ∧ R ⊆ F₁ ∧ R ⊆ F₂

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

end

end GaloisForLFunctions
