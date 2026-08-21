import GaloisForLFunctions.HTGeometry.BorsukUlam.FlagComplex
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets

/-!
# Barycentric subdivision of a flag complex

The barycentric subdivision of a `FlagComplex n` has the faces of `K` as vertices and the nonempty
chains of faces as its own faces.  The level of a vertex is the carrier dimension of the
corresponding face and its sign is the carrier sign, so the flag of hemispheres is inherited.

This file proves that every axiom of `FlagComplex` survives, in particular the two facet-counting
axioms:  a chain missing one card in the middle of its range can be completed in exactly two ways,
and a maximal chain is contained in exactly one chain of the next carrier dimension of each sign.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset

namespace FlagComplex

variable {n : ℕ} (K : FlagComplex n)

/-- Vertices of the barycentric subdivision: the faces of `K`. -/
abbrev SdV : Type := {σ : Finset K.V // σ ∈ K.faces}

/-- A finset of faces is a chain when its members are pairwise comparable. -/
def SdChain (c : Finset (SdV K)) : Prop := ∀ x ∈ c, ∀ y ∈ c, x.1 ⊆ y.1 ∨ y.1 ⊆ x.1

instance (c : Finset (SdV K)) : Decidable (SdChain K c) := by
  unfold SdChain; infer_instance

/-- The faces of the barycentric subdivision: the nonempty chains. -/
def sdFaces : Finset (Finset (SdV K)) :=
  Finset.univ.filter (fun c => c.Nonempty ∧ SdChain K c)

variable {K}

theorem mem_sdFaces {c : Finset (SdV K)} : c ∈ sdFaces K ↔ (c.Nonempty ∧ SdChain K c) := by
  rw [sdFaces, mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩

theorem sdChain_card_inj {c : Finset (SdV K)} (hc : SdChain K c) {x y : SdV K} (hx : x ∈ c)
    (hy : y ∈ c) (h : x.1.card = y.1.card) : x = y := by
  refine Subtype.ext ?_
  rcases hc x hx y hy with hsub | hsub
  · exact eq_of_subset_of_card_le hsub (le_of_eq h.symm)
  · exact (eq_of_subset_of_card_le hsub (le_of_eq h)).symm

/-- A nonempty chain has a largest member. -/
theorem sdChain_max {c : Finset (SdV K)} (hc : SdChain K c) (hne : c.Nonempty) :
    ∃ m ∈ c, ∀ x ∈ c, x.1 ⊆ m.1 := by
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image c (fun x => x.1.card) hne
  refine ⟨m, hm, fun x hx => ?_⟩
  rcases hc x hx m hm with hsub | hsub
  · exact hsub
  · rw [eq_of_subset_of_card_le hsub (hmax x hx)]

/-- The cards occurring in a chain are distinct positive numbers bounded by the largest card. -/
theorem sdChain_card_le {c : Finset (SdV K)} (hc : SdChain K c) {m : SdV K} (hm : m ∈ c)
    (hmax : ∀ x ∈ c, x.1 ⊆ m.1) : c.card ≤ m.1.card := by
  have hmaps : ∀ x ∈ c, x.1.card ∈ Finset.Icc 1 m.1.card := by
    intro x hx
    have h1 : 0 < x.1.card := card_pos.mpr (K.faces_nonempty x.1 x.2)
    have h2 : x.1.card ≤ m.1.card := card_le_card (hmax x hx)
    simp only [Finset.mem_Icc]
    omega
  have hmapsTo : Set.MapsTo (fun x : SdV K => x.1.card) (↑c) (↑(Finset.Icc 1 m.1.card)) := by
    intro x hx
    exact hmaps x (Finset.mem_coe.mp hx)
  have hinj : Set.InjOn (fun x : SdV K => x.1.card) (↑c) := by
    intro x hx y hy h
    exact sdChain_card_inj hc (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) h
  have hle := Finset.card_le_card_of_injOn (fun x : SdV K => x.1.card) hmapsTo hinj
  rw [Nat.card_Icc] at hle
  omega

/-- The cards occurring in a chain, as a finset of naturals. -/
def sdCards (c : Finset (SdV K)) : Finset ℕ := c.image (fun x => x.1.card)

theorem card_sdCards {c : Finset (SdV K)} (hc : SdChain K c) : (sdCards c).card = c.card :=
  card_image_of_injOn (fun x hx y hy h =>
    sdChain_card_inj hc (Finset.mem_coe.mp hx) (Finset.mem_coe.mp hy) h)

theorem mem_sdCards {c : Finset (SdV K)} {k : ℕ} :
    k ∈ sdCards c ↔ ∃ x ∈ c, x.1.card = k := by
  rw [sdCards, mem_image]

/-- The level of a subdivision vertex is the carrier dimension of the corresponding face. -/
theorem sdChain_sup_lev {c : Finset (SdV K)} {m : SdV K} (hm : m ∈ c)
    (hmax : ∀ x ∈ c, x.1 ⊆ m.1) : c.sup (fun x => K.cdim x.1) = K.cdim m.1 := by
  refine le_antisymm (Finset.sup_le fun x hx => cdim_mono (hmax x hx)) ?_
  exact Finset.le_sup (f := fun x => K.cdim x.1) hm

section Facets

variable (K)

/-- Level of a subdivision vertex. -/
def sdLev (x : SdV K) : ℕ := K.cdim x.1

/-- Sign of a subdivision vertex. -/
def sdSgn (x : SdV K) : Bool := K.csgn x.1

variable {K}

/-- The extension relation between chains used by the facet axioms. -/
def SdExt (c c' : Finset (SdV K)) : Prop :=
  c ⊆ c' ∧ c'.card = c.card + 1 ∧ c'.sup (sdLev K) = c.sup (sdLev K)

theorem sup_insert_le {c : Finset (SdV K)} {ρ : SdV K} {D : ℕ}
    (hρ : sdLev K ρ ≤ D) (hc : c.sup (sdLev K) ≤ D) : (insert ρ c).sup (sdLev K) ≤ D := by
  rw [Finset.sup_insert]
  exact sup_le hρ hc

/-- Top extension: the chain already has all cards up to that of its maximum. -/
theorem sd_facets_two_top {c : Finset (SdV K)} (hc : SdChain K c) (hne : c.Nonempty)
    {m : SdV K} (hm : m ∈ c) (hmax : ∀ x ∈ c, x.1 ⊆ m.1)
    (hMD : m.1.card = K.cdim m.1) (hcards : sdCards c = Finset.Icc 1 m.1.card) :
    ∃ c₁ ∈ sdFaces K, ∃ c₂ ∈ sdFaces K, c₁ ≠ c₂ ∧ SdExt c c₁ ∧ SdExt c c₂ ∧
      ∀ c' ∈ sdFaces K, SdExt c c' → c' = c₁ ∨ c' = c₂ := by
  have hsup : c.sup (sdLev K) = K.cdim m.1 := sdChain_sup_lev hm hmax
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hne12, ⟨hs1, hc1, hd1⟩, ⟨hs2, hc2, hd2⟩, huniq⟩ :=
    facets_two_cdim m.2 hMD
  -- a face of card `m.1.card + 1` is not one of the chain's members
  have hnotin : ∀ (ρ : SdV K), ρ.1.card = m.1.card + 1 → ρ ∉ c := by
    intro ρ hρcard hmem
    have : ρ.1.card ∈ sdCards c := mem_sdCards.mpr ⟨ρ, hmem, rfl⟩
    rw [hcards, Finset.mem_Icc] at this
    omega
  have hchain : ∀ (ρ : SdV K), m.1 ⊆ ρ.1 → SdChain K (insert ρ c) := by
    intro ρ hsub x hx y hy
    rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
    · exact Or.inl (subset_refl _)
    · exact Or.inr (subset_trans (hmax y hy') hsub)
    · exact Or.inl (subset_trans (hmax x hx') hsub)
    · exact hc x hx' y hy'
  have hext : ∀ (ρ : SdV K), m.1 ⊆ ρ.1 → ρ.1.card = m.1.card + 1 → K.cdim ρ.1 = K.cdim m.1 →
      (insert ρ c ∈ sdFaces K ∧ SdExt c (insert ρ c)) := by
    intro ρ hsub hρcard hρd
    have hρc : ρ ∉ c := hnotin ρ hρcard
    refine ⟨mem_sdFaces.mpr ⟨⟨ρ, mem_insert_self _ _⟩, hchain ρ hsub⟩,
      subset_insert _ _, card_insert_of_notMem hρc, ?_⟩
    rw [Finset.sup_insert, hsup, sdLev, hρd]
    simp
  obtain ⟨hm1, he1⟩ := hext ⟨τ₁, hτ₁⟩ hs1 (by rw [hc1]) hd1
  obtain ⟨hm2, he2⟩ := hext ⟨τ₂, hτ₂⟩ hs2 (by rw [hc2]) hd2
  refine ⟨insert ⟨τ₁, hτ₁⟩ c, hm1, insert ⟨τ₂, hτ₂⟩ c, hm2, ?_, he1, he2, ?_⟩
  · intro hcon
    have h1 : (⟨τ₁, hτ₁⟩ : SdV K) ∈ insert (⟨τ₂, hτ₂⟩ : SdV K) c := by
      rw [← hcon]; exact mem_insert_self _ _
    rcases mem_insert.mp h1 with heq | hmem
    · exact hne12 (congrArg Subtype.val heq)
    · exact hnotin _ (by rw [hc1]) hmem
  · intro c' hc' hext'
    obtain ⟨ρ, hρc, rfl⟩ := exists_insert hext'.1 hext'.2.1
    have hchain' : SdChain K (insert ρ c) := (mem_sdFaces.mp hc').2
    have hcompm : m.1 ⊆ ρ.1 ∨ ρ.1 ⊆ m.1 :=
      hchain' m (mem_insert_of_mem hm) ρ (mem_insert_self _ _)
    have hρnotcard : ρ.1.card ∉ sdCards c := by
      intro hmem
      obtain ⟨x, hx, hxcard⟩ := mem_sdCards.mp hmem
      have := sdChain_card_inj hchain' (mem_insert_self ρ c) (mem_insert_of_mem hx) hxcard.symm
      rw [this] at hρc
      exact hρc hx
    have hρcard_gt : m.1.card < ρ.1.card := by
      have h0 : 0 < ρ.1.card := card_pos.mpr (K.faces_nonempty ρ.1 ρ.2)
      rw [hcards, Finset.mem_Icc] at hρnotcard
      omega
    have hsubm : m.1 ⊆ ρ.1 := by
      rcases hcompm with h | h
      · exact h
      · exact absurd (card_le_card h) (by omega)
    have hρD : K.cdim ρ.1 ≤ K.cdim m.1 := by
      have := hext'.2.2
      rw [Finset.sup_insert, hsup] at this
      have hle : sdLev K ρ ≤ K.cdim m.1 := by
        rw [← this]
        exact le_sup_left
      exact hle
    have hρcard : ρ.1.card = m.1.card + 1 := by
      have h1 : ρ.1.card ≤ K.cdim ρ.1 + 1 := K.card_le ρ.1 ρ.2
      omega
    have hρd : K.cdim ρ.1 = K.cdim m.1 := by
      have h1 : ρ.1.card ≤ K.cdim ρ.1 + 1 := K.card_le ρ.1 ρ.2
      omega
    rcases huniq ρ.1 ρ.2 hsubm (by omega) hρd with h | h
    · exact Or.inl (by rw [show ρ = (⟨τ₁, hτ₁⟩ : SdV K) from Subtype.ext h])
    · exact Or.inr (by rw [show ρ = (⟨τ₂, hτ₂⟩ : SdV K) from Subtype.ext h])

/-- Middle extension: the chain misses one card `j` inside its range. -/
theorem sd_facets_two_middle {c : Finset (SdV K)} (hc : SdChain K c)
    {m : SdV K} (hm : m ∈ c) (hmax : ∀ x ∈ c, x.1 ⊆ m.1)
    (hM : m.1.card = K.cdim m.1 + 1) {j : ℕ} (hj1 : 1 ≤ j) (hjM : j < m.1.card)
    (hcards : Finset.Icc 1 m.1.card = insert j (sdCards c)) (hjnot : j ∉ sdCards c)
    {A : Finset K.V} {b : SdV K} (hb : b ∈ c) (hbcard : b.1.card = j + 1)
    (hAb : A ⊆ b.1) (hAcard : A.card + 2 = b.1.card)
    (hlow : ∀ x ∈ c, x.1.card < j → x.1 ⊆ A)
    (hAsub : ∀ ρ : Finset K.V, (∀ x ∈ c, x.1 ⊆ ρ ∨ ρ ⊆ x.1) → ρ.card = j → A ⊆ ρ) :
    ∃ c₁ ∈ sdFaces K, ∃ c₂ ∈ sdFaces K, c₁ ≠ c₂ ∧ SdExt c c₁ ∧ SdExt c c₂ ∧
      ∀ c' ∈ sdFaces K, SdExt c c' → c' = c₁ ∨ c' = c₂ := by
  have hsup : c.sup (sdLev K) = K.cdim m.1 := sdChain_sup_lev hm hmax
  have hhigh : ∀ x ∈ c, j < x.1.card → b.1 ⊆ x.1 := by
    intro x hx hxc
    rcases hc b hb x hx with h | h
    · exact h
    · have heq : x.1 = b.1 := eq_of_subset_of_card_le h (by omega)
      rw [heq]
  obtain ⟨p, q, hpq, hpB, hqB, hpA, hqA, hmid⟩ := two_middles hAb (by omega)
  -- the two candidate faces
  have hface : ∀ ρ : Finset K.V, ρ ⊆ b.1 → ρ.card = j → ρ ∈ K.faces := by
    intro ρ hρb hρcard
    exact K.faces_down b.1 b.2 ρ hρb (card_pos.mp (by omega))
  have hchain : ∀ ρ : SdV K, A ⊆ ρ.1 → ρ.1 ⊆ b.1 → ρ.1.card = j → SdChain K (insert ρ c) := by
    intro ρ hAρ hρb hρcard x hx y hy
    have hcomp : ∀ z ∈ c, z.1 ⊆ ρ.1 ∨ ρ.1 ⊆ z.1 := by
      intro z hz
      rcases lt_trichotomy z.1.card j with h | h | h
      · exact Or.inl (subset_trans (hlow z hz h) hAρ)
      · exact absurd (mem_sdCards.mpr ⟨z, hz, h⟩) hjnot
      · exact Or.inr (subset_trans hρb (hhigh z hz h))
    rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
    · exact Or.inl (subset_refl _)
    · exact (hcomp y hy').symm
    · exact hcomp x hx'
    · exact hc x hx' y hy'
  have hnotin : ∀ ρ : SdV K, ρ.1.card = j → ρ ∉ c := by
    intro ρ hρcard hmem
    exact hjnot (mem_sdCards.mpr ⟨ρ, hmem, hρcard⟩)
  have hext : ∀ ρ : SdV K, A ⊆ ρ.1 → ρ.1 ⊆ b.1 → ρ.1.card = j →
      (insert ρ c ∈ sdFaces K ∧ SdExt c (insert ρ c)) := by
    intro ρ hAρ hρb hρcard
    refine ⟨mem_sdFaces.mpr ⟨⟨ρ, mem_insert_self _ _⟩, hchain ρ hAρ hρb hρcard⟩,
      subset_insert _ _, card_insert_of_notMem (hnotin ρ hρcard), ?_⟩
    have hle : sdLev K ρ ≤ K.cdim m.1 := by
      have h1 : K.cdim ρ.1 ≤ K.cdim b.1 := cdim_mono hρb
      have h2 : K.cdim b.1 ≤ K.cdim m.1 := cdim_mono (hmax b hb)
      exact le_trans h1 h2
    rw [Finset.sup_insert, hsup]
    exact sup_eq_right.mpr hle
  have hp1 : (insert p A).card = j := by
    rw [card_insert_of_notMem hpA]; omega
  have hq1 : (insert q A).card = j := by
    rw [card_insert_of_notMem hqA]; omega
  have hpsub : insert p A ⊆ b.1 := insert_subset hpB hAb
  have hqsub : insert q A ⊆ b.1 := insert_subset hqB hAb
  set ρ₁ : SdV K := ⟨insert p A, hface _ hpsub hp1⟩ with hρ₁
  set ρ₂ : SdV K := ⟨insert q A, hface _ hqsub hq1⟩ with hρ₂
  obtain ⟨hm1, he1⟩ := hext ρ₁ (subset_insert _ _) hpsub hp1
  obtain ⟨hm2, he2⟩ := hext ρ₂ (subset_insert _ _) hqsub hq1
  refine ⟨insert ρ₁ c, hm1, insert ρ₂ c, hm2, ?_, he1, he2, ?_⟩
  · intro hcon
    have h1 : ρ₁ ∈ insert ρ₂ c := by rw [← hcon]; exact mem_insert_self _ _
    rcases mem_insert.mp h1 with heq | hmem
    · have : insert p A = insert q A := congrArg Subtype.val heq
      have hpin : p ∈ insert q A := by rw [← this]; exact mem_insert_self _ _
      rcases mem_insert.mp hpin with hh | hh
      · exact hpq hh
      · exact hpA hh
    · exact hnotin ρ₁ hp1 hmem
  · intro c' hc' hext'
    obtain ⟨ρ, hρc, rfl⟩ := exists_insert hext'.1 hext'.2.1
    have hchain' : SdChain K (insert ρ c) := (mem_sdFaces.mp hc').2
    have hcomp : ∀ x ∈ c, x.1 ⊆ ρ.1 ∨ ρ.1 ⊆ x.1 := by
      intro x hx
      exact hchain' x (mem_insert_of_mem hx) ρ (mem_insert_self _ _)
    have hρnotcard : ρ.1.card ∉ sdCards c := by
      intro hmem
      obtain ⟨x, hx, hxcard⟩ := mem_sdCards.mp hmem
      have := sdChain_card_inj hchain' (mem_insert_self ρ c) (mem_insert_of_mem hx) hxcard.symm
      rw [this] at hρc
      exact hρc hx
    have hρD : K.cdim ρ.1 ≤ K.cdim m.1 := by
      have hh := hext'.2.2
      rw [Finset.sup_insert, hsup] at hh
      have : sdLev K ρ ≤ K.cdim m.1 := by
        rw [← hh]; exact le_sup_left
      exact this
    have hρcardj : ρ.1.card = j := by
      have h1 : ρ.1.card ≤ K.cdim ρ.1 + 1 := K.card_le ρ.1 ρ.2
      have h2 : 0 < ρ.1.card := card_pos.mpr (K.faces_nonempty ρ.1 ρ.2)
      have h3 : ρ.1.card ∈ Finset.Icc 1 m.1.card := by
        simp only [Finset.mem_Icc]
        omega
      rw [hcards, mem_insert] at h3
      rcases h3 with h | h
      · exact h
      · exact absurd h hρnotcard
    have hAρ : A ⊆ ρ.1 := hAsub ρ.1 hcomp hρcardj
    have hρb : ρ.1 ⊆ b.1 := by
      rcases hcomp b hb with h | h
      · exact absurd (card_le_card h) (by omega)
      · exact h
    rcases (hmid ρ.1).mp ⟨hAρ, hρb, by omega⟩ with h | h
    · exact Or.inl (by rw [show ρ = ρ₁ from Subtype.ext h])
    · exact Or.inr (by rw [show ρ = ρ₂ from Subtype.ext h])

theorem sdCards_subset {c : Finset (SdV K)} {m : SdV K} (hmax : ∀ x ∈ c, x.1 ⊆ m.1) :
    sdCards c ⊆ Finset.Icc 1 m.1.card := by
  intro k hk
  obtain ⟨x, hx, rfl⟩ := mem_sdCards.mp hk
  have h1 : 0 < x.1.card := card_pos.mpr (K.faces_nonempty x.1 x.2)
  have h2 : x.1.card ≤ m.1.card := card_le_card (hmax x hx)
  simp only [Finset.mem_Icc]
  omega

theorem sdCards_eq_Icc {c : Finset (SdV K)} (hc : SdChain K c) {m : SdV K}
    (hmax : ∀ x ∈ c, x.1 ⊆ m.1) (hcard : c.card = m.1.card) :
    sdCards c = Finset.Icc 1 m.1.card := by
  refine eq_of_subset_of_card_le (sdCards_subset hmax) ?_
  rw [Nat.card_Icc, card_sdCards hc, hcard]
  omega

/-- The two facet extensions of a chain of maximal length in its carrier dimension. -/
theorem sd_facets_two {c : Finset (SdV K)} (hcf : c ∈ sdFaces K)
    (hcard : c.card = c.sup (sdLev K)) :
    ∃ c₁ ∈ sdFaces K, ∃ c₂ ∈ sdFaces K, c₁ ≠ c₂ ∧ SdExt c c₁ ∧ SdExt c c₂ ∧
      ∀ c' ∈ sdFaces K, SdExt c c' → c' = c₁ ∨ c' = c₂ := by
  obtain ⟨hne, hc⟩ := mem_sdFaces.mp hcf
  obtain ⟨m, hm, hmax⟩ := sdChain_max hc hne
  have hsup : c.sup (sdLev K) = K.cdim m.1 := sdChain_sup_lev hm hmax
  have hD : c.card = K.cdim m.1 := by rw [hcard, hsup]
  have hle : c.card ≤ m.1.card := sdChain_card_le hc hm hmax
  have hMle : m.1.card ≤ K.cdim m.1 + 1 := K.card_le m.1 m.2
  rcases Nat.lt_or_ge (K.cdim m.1) m.1.card with hlt | hge
  · -- middle case: the chain misses one card
    have hMeq : m.1.card = K.cdim m.1 + 1 := by omega
    have hsub := sdCards_subset (K := K) (c := c) hmax
    have hcardS : (sdCards c).card + 1 = (Finset.Icc 1 m.1.card).card := by
      rw [Nat.card_Icc, card_sdCards hc]
      omega
    have hd1 : ((Finset.Icc 1 m.1.card) \ (sdCards c)).card = 1 := by
      rw [card_sdiff_of_subset hsub]
      omega
    obtain ⟨j, hj⟩ := card_eq_one.mp hd1
    have hjmem : j ∈ Finset.Icc 1 m.1.card ∧ j ∉ sdCards c := by
      have : j ∈ (Finset.Icc 1 m.1.card) \ (sdCards c) := by rw [hj]; exact mem_singleton_self j
      exact mem_sdiff.mp this
    have hIcc : Finset.Icc 1 m.1.card = insert j (sdCards c) := by
      ext k
      simp only [mem_insert]
      constructor
      · intro hk
        by_cases hks : k ∈ sdCards c
        · exact Or.inr hks
        · left
          have : k ∈ (Finset.Icc 1 m.1.card) \ (sdCards c) := mem_sdiff.mpr ⟨hk, hks⟩
          rw [hj, mem_singleton] at this
          exact this
      · rintro (rfl | hk)
        · exact hjmem.1
        · exact hsub hk
    have hjM : j < m.1.card := by
      have hMin : m.1.card ∈ sdCards c := mem_sdCards.mpr ⟨m, hm, rfl⟩
      have h1 := hjmem.1
      simp only [Finset.mem_Icc] at h1
      rcases Nat.lt_or_ge j m.1.card with h | h
      · exact h
      · exfalso
        apply hjmem.2
        have hje : j = m.1.card := by omega
        rw [hje]
        exact hMin
    have hj1 : 1 ≤ j := by
      have h1 := hjmem.1
      simp only [Finset.mem_Icc] at h1
      exact h1.1
    obtain ⟨b, hb, hbcard⟩ : ∃ b ∈ c, b.1.card = j + 1 := by
      have hmem : j + 1 ∈ Finset.Icc 1 m.1.card := by
        simp only [Finset.mem_Icc]
        omega
      rw [hIcc, mem_insert] at hmem
      rcases hmem with h | h
      · omega
      · obtain ⟨x, hx, hxc⟩ := mem_sdCards.mp h
        exact ⟨x, hx, hxc⟩
    by_cases hjone : j = 1
    · refine sd_facets_two_middle hc hm hmax hMeq hj1 hjM hIcc hjmem.2 hb hbcard
        (empty_subset _) (by simp only [card_empty]; omega) ?_ ?_
      · intro x hx hxc
        exfalso
        have := card_pos.mpr (K.faces_nonempty x.1 x.2)
        omega
      · intro ρ _ _
        exact empty_subset _
    · obtain ⟨a, ha, hacard⟩ : ∃ a ∈ c, a.1.card = j - 1 := by
        have hmem : j - 1 ∈ Finset.Icc 1 m.1.card := by
          simp only [Finset.mem_Icc]
          omega
        rw [hIcc, mem_insert] at hmem
        rcases hmem with h | h
        · omega
        · obtain ⟨x, hx, hxc⟩ := mem_sdCards.mp h
          exact ⟨x, hx, hxc⟩
      have hab : a.1 ⊆ b.1 := by
        rcases hc a ha b hb with h | h
        · exact h
        · exact absurd (card_le_card h) (by omega)
      refine sd_facets_two_middle hc hm hmax hMeq hj1 hjM hIcc hjmem.2 hb hbcard hab
        (by omega) ?_ ?_
      · intro x hx hxc
        rcases hc x hx a ha with h | h
        · exact h
        · have heq : a.1 = x.1 := eq_of_subset_of_card_le h (by omega)
          rw [heq]
      · intro ρ hcomp hρcard
        rcases hcomp a ha with h | h
        · exact h
        · exact absurd (card_le_card h) (by omega)
  · -- top case
    have hMeq : m.1.card = K.cdim m.1 := by omega
    exact sd_facets_two_top hc hne hm hmax hMeq (sdCards_eq_Icc hc hmax (by omega))

/-- The unique extension of a maximal chain into the next hemisphere of a given sign. -/
theorem sd_facets_one {c : Finset (SdV K)} (hcf : c ∈ sdFaces K)
    (hcard : c.card = c.sup (sdLev K) + 1) (hltn : c.sup (sdLev K) < n) (ε : Bool) :
    ∃ c' ∈ sdFaces K, (c ⊆ c' ∧ c'.card = c.card + 1 ∧
        c'.sup (sdLev K) = c.sup (sdLev K) + 1 ∧
        ∃ x ∈ c', sdLev K x = c'.sup (sdLev K) ∧ sdSgn K x = ε) ∧
      ∀ c'' ∈ sdFaces K, c ⊆ c'' → c''.card = c.card + 1 →
        c''.sup (sdLev K) = c.sup (sdLev K) + 1 →
        (∃ x ∈ c'', sdLev K x = c''.sup (sdLev K) ∧ sdSgn K x = ε) → c'' = c' := by
  obtain ⟨hne, hc⟩ := mem_sdFaces.mp hcf
  obtain ⟨m, hm, hmax⟩ := sdChain_max hc hne
  have hsup : c.sup (sdLev K) = K.cdim m.1 := sdChain_sup_lev hm hmax
  have hle : c.card ≤ m.1.card := sdChain_card_le hc hm hmax
  have hMle : m.1.card ≤ K.cdim m.1 + 1 := K.card_le m.1 m.2
  have hMeq : m.1.card = K.cdim m.1 + 1 := by omega
  have hcards : sdCards c = Finset.Icc 1 m.1.card := sdCards_eq_Icc hc hmax (by omega)
  obtain ⟨ρ, hρ, ⟨hsubm, hρcard, hρd, hρsgn⟩, huniq⟩ :=
    facets_one_cdim m.2 hMeq (by rw [← hsup]; exact hltn) ε
  have hnotin : ∀ x : SdV K, m.1.card < x.1.card → x ∉ c := by
    intro x hx hmem
    have hmm : x.1.card ∈ sdCards c := mem_sdCards.mpr ⟨x, hmem, rfl⟩
    rw [hcards, Finset.mem_Icc] at hmm
    omega
  have hchain : ∀ x : SdV K, m.1 ⊆ x.1 → SdChain K (insert x c) := by
    intro x hsub y hy z hz
    rcases mem_insert.mp hy with rfl | hy' <;> rcases mem_insert.mp hz with rfl | hz'
    · exact Or.inl (subset_refl _)
    · exact Or.inr (subset_trans (hmax z hz') hsub)
    · exact Or.inl (subset_trans (hmax y hy') hsub)
    · exact hc y hy' z hz'
  set ρ' : SdV K := ⟨ρ, hρ⟩ with hρ'def
  have hlevρ : sdLev K ρ' = K.cdim m.1 + 1 := hρd
  have hsupins : ∀ x : SdV K, sdLev K x = K.cdim m.1 + 1 →
      (insert x c).sup (sdLev K) = K.cdim m.1 + 1 := by
    intro x hx
    rw [Finset.sup_insert, hsup, hx]
    omega
  refine ⟨insert ρ' c, mem_sdFaces.mpr ⟨⟨ρ', mem_insert_self _ _⟩, hchain ρ' hsubm⟩,
    ⟨subset_insert _ _, card_insert_of_notMem (hnotin ρ' (by show m.1.card < ρ.card; omega)), ?_, ?_⟩, ?_⟩
  · rw [hsupins ρ' hlevρ, hsup]
  · exact ⟨ρ', mem_insert_self _ _, by rw [hsupins ρ' hlevρ, hlevρ], hρsgn⟩
  · intro c'' hc'' hsub'' hcard'' hsup'' hex
    obtain ⟨ρ₂, hρ₂c, rfl⟩ := exists_insert hsub'' hcard''
    have hchain2 : SdChain K (insert ρ₂ c) := (mem_sdFaces.mp hc'').2
    have hsup2 : sdLev K ρ₂ = K.cdim m.1 + 1 := by
      rw [Finset.sup_insert, hsup] at hsup''
      omega
    have hcard2 : ρ₂.1.card = m.1.card + 1 := by
      have h1 : ρ₂.1.card ≤ K.cdim ρ₂.1 + 1 := K.card_le ρ₂.1 ρ₂.2
      have h2 : 0 < ρ₂.1.card := card_pos.mpr (K.faces_nonempty ρ₂.1 ρ₂.2)
      have h3 : ρ₂.1.card ∉ sdCards c := by
        intro hmem
        obtain ⟨x, hx, hxcard⟩ := mem_sdCards.mp hmem
        have := sdChain_card_inj hchain2 (mem_insert_self ρ₂ c) (mem_insert_of_mem hx) hxcard.symm
        rw [this] at hρ₂c
        exact hρ₂c hx
      rw [hcards, Finset.mem_Icc] at h3
      have hlev : K.cdim ρ₂.1 = K.cdim m.1 + 1 := hsup2
      omega
    have hsubm2 : m.1 ⊆ ρ₂.1 := by
      rcases hchain2 m (mem_insert_of_mem hm) ρ₂ (mem_insert_self _ _) with h | h
      · exact h
      · exact absurd (card_le_card h) (by omega)
    have hsgn2 : K.csgn ρ₂.1 = ε := by
      obtain ⟨x, hx, hxlev, hxsgn⟩ := hex
      rw [hsupins ρ₂ hsup2] at hxlev
      rcases mem_insert.mp hx with rfl | hx'
      · exact hxsgn
      · exfalso
        have : sdLev K x ≤ K.cdim m.1 := by
          rw [← hsup]
          exact Finset.le_sup hx'
        omega
    have := huniq ρ₂.1 ρ₂.2 hsubm2 (by omega) hsup2 hsgn2
    rw [show ρ₂ = ρ' from Subtype.ext this]

end Facets

section Sd

variable (K)

/-- The antipodal involution on subdivision vertices. -/
def sdNeg (x : SdV K) : SdV K := ⟨K.negF x.1, negF_mem x.2⟩

/-- **Barycentric subdivision** of a flag complex. -/
def sd : FlagComplex n where
  V := SdV K
  decEq := inferInstance
  neg := sdNeg K
  lev := sdLev K
  sgn := sdSgn K
  faces := sdFaces K
  base := ⟨{K.base}, K.base_face⟩
  neg_neg := fun x => Subtype.ext (negF_negF x.1)
  lev_le := fun x => cdim_le x.1
  lev_neg := fun x => cdim_negF x.1
  sgn_neg := fun x => csgn_negF x.2 (K.faces_nonempty x.1 x.2)
  faces_nonempty := fun c hc => (mem_sdFaces.mp hc).1
  faces_down := by
    intro c hc c' hsub hne
    exact mem_sdFaces.mpr ⟨hne, fun x hx y hy => (mem_sdFaces.mp hc).2 x (hsub hx) y (hsub hy)⟩
  faces_neg := by
    intro c hc
    obtain ⟨hne, hchain⟩ := mem_sdFaces.mp hc
    refine mem_sdFaces.mpr ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨sdNeg K x, mem_image_of_mem _ hx⟩
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
      rcases hchain x' hx' y' hy' with h | h
      · exact Or.inl (negF_subset h)
      · exact Or.inr (negF_subset h)
  coherent := by
    intro c hc u hu v hv hulev hvlev
    obtain ⟨-, hchain⟩ := mem_sdFaces.mp hc
    have hcd : K.cdim u.1 = K.cdim v.1 := by
      have h1 : sdLev K u = sdLev K v := by rw [hulev, hvlev]
      exact h1
    rcases hchain u hu v hv with h | h
    · exact csgn_eq_of_subset u.2 v.2 h hcd
    · exact (csgn_eq_of_subset v.2 u.2 h hcd.symm).symm
  card_le := by
    intro c hc
    obtain ⟨hne, hchain⟩ := mem_sdFaces.mp hc
    obtain ⟨m, hm, hmax⟩ := sdChain_max hchain hne
    have h1 : c.card ≤ m.1.card := sdChain_card_le hchain hm hmax
    have h2 : m.1.card ≤ K.cdim m.1 + 1 := K.card_le m.1 m.2
    have h3 : c.sup (sdLev K) = K.cdim m.1 := sdChain_sup_lev hm hmax
    omega
  facets_two := by
    intro c hc hcard
    obtain ⟨c₁, hc₁, c₂, hc₂, hne, he₁, he₂, huniq⟩ := sd_facets_two hc hcard
    exact ⟨c₁, hc₁, c₂, hc₂, hne, he₁, he₂,
      fun τ hτ h1 h2 h3 => huniq τ hτ ⟨h1, h2, h3⟩⟩
  facets_one := by
    intro c hc hcard hlt ε
    exact sd_facets_one hc hcard hlt ε
  base_face := by
    refine mem_sdFaces.mpr ⟨⟨⟨{K.base}, K.base_face⟩, mem_singleton_self _⟩, ?_⟩
    intro x hx y hy
    rw [mem_singleton] at hx hy
    rw [hx, hy]
    exact Or.inl (subset_refl _)
  base_lev := base_cdim
  lev_zero := by
    intro c hc x hx hlev
    have hcd : K.cdim x.1 = 0 := hlev
    have hne : x.1.Nonempty := K.faces_nonempty x.1 x.2
    have hall : ∀ v ∈ x.1, v = K.base ∨ v = K.neg K.base := by
      intro v hv
      refine K.lev_zero x.1 x.2 v hv ?_
      have : K.lev v ≤ K.cdim x.1 := lev_le_cdim hv
      omega
    have hnotboth : ¬(K.base ∈ x.1 ∧ K.neg K.base ∈ x.1) := by
      rintro ⟨h1, h2⟩
      have hl1 : K.lev K.base = K.cdim x.1 := by rw [K.base_lev, hcd]
      have hl2 : K.lev (K.neg K.base) = K.cdim x.1 := by rw [K.lev_neg, K.base_lev, hcd]
      have := K.coherent x.1 x.2 K.base h1 (K.neg K.base) h2 hl1 hl2
      rw [K.sgn_neg] at this
      simp at this
    obtain ⟨v, hv⟩ := hne
    rcases hall v hv with rfl | rfl
    · left
      refine Subtype.ext ?_
      ext z
      simp only [mem_singleton]
      constructor
      · intro hz
        rcases hall z hz with h | h
        · exact h
        · exact absurd ⟨hv, by rw [← h]; exact hz⟩ hnotboth
      · rintro rfl
        exact hv
    · right
      refine Subtype.ext ?_
      have himg : (sdNeg K ⟨{K.base}, K.base_face⟩).1 = {K.neg K.base} := by
        show K.negF {K.base} = {K.neg K.base}
        simp [negF]
      rw [himg]
      ext z
      simp only [mem_singleton]
      constructor
      · intro hz
        rcases hall z hz with h | h
        · exact absurd ⟨by rw [← h]; exact hz, hv⟩ hnotboth
        · exact h
      · rintro rfl
        exact hv

end Sd

end FlagComplex

end GaloisForLFunctions.BorsukUlam
