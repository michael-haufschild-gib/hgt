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

/-! ### Rank-one facet principalization -/

/-- The facets obtained by deleting one vertex from a set `U` of ambient vertices. -/
def deletionFacets (V U : Finset α) : Set (Finset α) :=
  {F | ∃ u ∈ U, F = V.erase u}

/-- A facet family has one-variable period codimension when every facet misses at most one
ambient vertex. This is the exact combinatorial output of the HT period-rank argument. -/
def FacetComplementRankOne (V : Finset α) (facets : Set (Finset α)) : Prop :=
  ∀ ⦃F⦄, F ∈ facets → F ⊆ V ∧ (V \ F).card ≤ 1

/-- Rank-one facet complements force the simplex-or-deletion-family classification. In the
non-simplex case the omitted vertices form a nonempty block `U`. -/
theorem facetAntichain_eq_singleton_or_deletionFacets
    {V : Finset α} {facets : Set (Finset α)}
    (hne : facets.Nonempty) (hanti : FacetAntichain facets)
    (hrank : FacetComplementRankOne V facets) :
    facets = {V} ∨
      ∃ U : Finset α, U.Nonempty ∧ U ⊆ V ∧ facets = deletionFacets V U := by
  classical
  by_cases hV : V ∈ facets
  · left
    ext F
    constructor
    · intro hF
      have hFV : F ⊆ V := (hrank hF).1
      exact Set.mem_singleton_iff.mpr (hanti hF hV hFV)
    · intro hF
      exact Set.mem_singleton_iff.mp hF ▸ hV
  · right
    let U : Finset α := V.filter fun u => V.erase u ∈ facets
    have hUsub : U ⊆ V := filter_subset _ _
    have hfacets : facets = deletionFacets V U := by
      ext F
      constructor
      · intro hF
        have hFV : F ⊆ V := (hrank hF).1
        have hdiff_ne : (V \ F).Nonempty := by
          rw [sdiff_nonempty]
          intro hVF
          have hFVeq : F = V := Finset.Subset.antisymm hFV hVF
          exact hV (hFVeq ▸ hF)
        obtain ⟨u, hu⟩ := hdiff_ne
        have hdiff : V \ F = {u} := by
          ext x
          constructor
          · intro hx
            have hxu := card_le_one.mp (hrank hF).2 x hx u hu
            simp [hxu]
          · intro hx
            have hxu : x = u := by simpa using hx
            exact hxu ▸ hu
        have huV : u ∈ V := (mem_sdiff.mp hu).1
        have hFerase : F = V.erase u := by
          apply Finset.Subset.antisymm
          · exact fun x hx =>
              mem_erase.mpr ⟨fun hxu => (mem_sdiff.mp hu).2 (hxu ▸ hx), hFV hx⟩
          · intro x hx
            have hxV : x ∈ V := (mem_erase.mp hx).2
            by_contra hxF
            have hxsdiff : x ∈ V \ F := mem_sdiff.mpr ⟨hxV, hxF⟩
            have hxu : x = u := by simpa [hdiff] using hxsdiff
            exact (mem_erase.mp hx).1 hxu
        have huU : u ∈ U := by
          rw [mem_filter]
          exact ⟨huV, hFerase ▸ hF⟩
        exact ⟨u, huU, hFerase⟩
      · rintro ⟨u, huU, rfl⟩
        exact (mem_filter.mp huU).2
    have hUne : U.Nonempty := by
      obtain ⟨F, hF⟩ := hne
      rw [hfacets] at hF
      obtain ⟨u, huU, -⟩ := hF
      exact ⟨u, huU⟩
    exact ⟨U, hUne, hUsub, hfacets⟩

/-- The faces of a deletion family are exactly the ambient subsets which omit at least one
vertex of `U`. -/
theorem isFaceOf_deletionFacets_iff {V U J : Finset α} :
    IsFaceOf (deletionFacets V U) J ↔ J ⊆ V ∧ ¬ U ⊆ J := by
  constructor
  · rintro ⟨F, ⟨u, huU, rfl⟩, hJF⟩
    refine ⟨hJF.trans (erase_subset u V), ?_⟩
    intro hUJ
    exact (mem_erase.mp (hJF (hUJ huU))).1 rfl
  · rintro ⟨hJV, hUnotJ⟩
    rw [Finset.not_subset] at hUnotJ
    obtain ⟨u, huU, huJ⟩ := hUnotJ
    refine ⟨V.erase u, ⟨u, huU, rfl⟩, ?_⟩
    exact fun x hx => mem_erase.mpr ⟨fun hxu => huJ (hxu ▸ hx), hJV hx⟩

/-- A deletion family has one unique minimal forbidden block: `U` itself is a nonface, and every
ambient nonface contains `U`. This is the combinatorial principalization statement. -/
theorem deletionFacets_unique_minimalNonface {V U : Finset α} (hUsub : U ⊆ V) :
    (¬ IsFaceOf (deletionFacets V U) U) ∧
      ∀ J, J ⊆ V → ¬ IsFaceOf (deletionFacets V U) J → U ⊆ J := by
  constructor
  · rw [isFaceOf_deletionFacets_iff]
    simp [hUsub]
  · intro J hJV hJ
    by_contra hUnotJ
    exact hJ ((isFaceOf_deletionFacets_iff).2 ⟨hJV, hUnotJ⟩)

end

end GaloisForLFunctions
