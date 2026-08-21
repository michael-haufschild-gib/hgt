import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardBoost

/-!
# CASE 4.1 of Grynkiewicz’s proof

CASE 4.1 is the branch in which the structural witnesses for the Dyson pair `(X, Y)` omit at
least one point.  Its estimate combines three contributions to `∑_{i≤t} #(A ·_i B)`: the core
`t·#(A′·B′)`, the cumulative coset contributions `l·(#H − ρ)`, and a set `S` of already
`t`-representable products lying outside `A′·B′`, each worth `t − l`.  `case41_core` is that
combination; the two branches differ only in how `S` is produced.

* `case41_branch` — the omitted point lies in `X`, and its products fill one translate, so a
  single deletion is enough.
* `case41_branch_two` — the omitted point lies in `Y ⊆ A ∩ B`, and its products split between
  two translates, so the pigeonhole of `exists_erase_drop` is used instead.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

theorem case41_arith {n m repS P l s d Sp : ℕ} (hs : 1 ≤ s)
    (hKn : n + m ≤ P + d + l)
    (hcount : (l + s) * P + l * d + Sp * s ≤ repS)
    (hSp : d + 2 ≤ Sp + 2 * (l + s)) :
    (l + s) * n + (l + s) * m + 1 ≤ repS + 2 * (l + s) ^ 2 := by
  have h1 : (l + s) * (n + m) ≤ (l + s) * (P + d + l) := Nat.mul_le_mul_left _ hKn
  have h2 : (d + 2) * s ≤ (Sp + 2 * (l + s)) * s := Nat.mul_le_mul_right _ hSp
  nlinarith [h1, h2, hcount, hs, Nat.zero_le l, Nat.zero_le s, Nat.zero_le d, Nat.zero_le Sp]

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- **The core estimate of Grynkiewicz's CASE 4.**  A set `S` of `t`-representable products lying
outside `A' · B'` and large enough relative to `#H − ρ` forces the weak Pollard bound. -/
theorem case41_core {A B X Y A' B' S : Finset G} {t : ℕ}
    (hXY : X.card + Y.card = A.card + B.card)
    (hA' : A' ⊆ X) (hB' : B' ⊆ Y) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hrep : ∀ c : G, rep X Y c ≤ rep A B c)
    (hsubAB : A' * B' ⊆ repSet A B t)
    (hdef : defect X A' Y B' + 1 ≤ t)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    (hsatA : ∀ z ∈ X, z ∈ A' * mulStab (A' * B') → z ∈ A')
    (hsatB : ∀ z ∈ Y, z ∈ B' * mulStab (A' * B') → z ∈ B')
    (hS : S ⊆ Finset.univ \ (A' * B')) (hSt : ∀ c ∈ S, t ≤ rep A B c)
    (hScard : (mulStab (A' * B')).card + 2
        ≤ S.card + 2 * t + holes (mulStab (A' * B')) A' B') :
    PollardWeak A B t := by
  classical
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  have hKn := card_mul_le_card_mul_mulStab A' B' hA'ne hB'ne
  rw [← hHdef] at hKn
  have hhA := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul A')
  have hhB := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul B')
  have hrho : holes H A' B' = ((A' * H) \ A').card + ((B' * H) \ B').card := rfl
  have hrhole : holes H A' B' + 2 ≤ H.card := by rw [hrho]; omega
  obtain ⟨d, hd⟩ : ∃ d, H.card = holes H A' B' + d := ⟨H.card - holes H A' B', by omega⟩
  obtain ⟨s, hsdef⟩ : ∃ s, t = defect X A' Y B' + s := ⟨t - defect X A' Y B', by omega⟩
  have hs : 1 ≤ s := by omega
  have hboost := repSum_ge_boost hA' hB' hrep hsubAB (by omega) hS hSt
  have hmix := mixed_sum_ge hA'ne hB'ne hsmall hsatA hsatB
  rw [← hHdef, hd] at hmix
  have hdsub : holes H A' B' + d - holes H A' B' = d := by omega
  rw [hdsub] at hmix
  have hts : t - defect X A' Y B' = s := by omega
  rw [hts] at hboost
  have hcardA := Finset.card_sdiff_add_card_eq_card hA'
  have hcardB := Finset.card_sdiff_add_card_eq_card hB'
  have hdefeq : defect X A' Y B' = (X \ A').card + (Y \ B').card := rfl
  have hKn2 : A'.card + B'.card + holes H A' B' ≤ (A' * B').card + H.card := by
    rw [hrho]; omega
  have hKnfinal : A.card + B.card ≤ (A' * B').card + d + defect X A' Y B' := by
    omega
  have hcount : (defect X A' Y B' + s) * (A' * B').card
      + defect X A' Y B' * d + S.card * s ≤ repSum A B t := by
    rw [← hsdef]
    omega
  have hSp : d + 2 ≤ S.card + 2 * (defect X A' Y B' + s) := by
    rw [← hsdef]
    omega
  rw [PollardWeak]
  have hfin := case41_arith (n := A.card) (m := B.card) (repS := repSum A B t)
    (P := (A' * B').card) (l := defect X A' Y B') (s := s) (d := d) (Sp := S.card)
    hs hKnfinal hcount hSp
  rw [← hsdef] at hfin
  exact hfin

/-- **One deletion branch of Grynkiewicz's CASE 4.1.**  Either the weak bound holds, or deleting
the point `a` drops `repSum` by at least `t`, which is the hypothesis of STEP 2. -/
theorem case41_branch {A B X Y A' B' W : Finset G} {t : ℕ} {a : G} {R : ℕ}
    (hXY : X.card + Y.card = A.card + B.card)
    (hA' : A' ⊆ X) (hB' : B' ⊆ Y) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hrep : ∀ c : G, rep X Y c ≤ rep A B c)
    (hsubAB : A' * B' ⊆ repSet A B t)
    (hdef : defect X A' Y B' + 1 ≤ t)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    (hsatA : ∀ z ∈ X, z ∈ A' * mulStab (A' * B') → z ∈ A')
    (hsatB : ∀ z ∈ Y, z ∈ B' * mulStab (A' * B') → z ∈ B')
    (ha : a ∈ X) (hna : a ∉ A') (hB'W : B' ⊆ W)
    (hdel : R + ((a • W).filter (fun c => rep A B c ≤ t)).card ≤ repSum A B t) :
    PollardWeak A B t ∨ (R + t ≤ repSum A B t) := by
  classical
  set F := (a • W).filter (fun c => rep A B c ≤ t) with hFdef
  by_cases hF : t ≤ F.card
  · exact Or.inr (by omega)
  left
  have hFsmall : F.card + 1 ≤ t := by omega
  set Bfil := B'.filter (fun b => a * b ∉ A' * B') with hBfil
  set Sset := Bfil.image (fun b => a * b) with hSset
  have hcardSset : Sset.card = Bfil.card := by
    rw [hSset]
    exact Finset.card_image_of_injective _ (mul_right_injective a)
  have hSsetsub : Sset ⊆ Finset.univ \ (A' * B') := by
    intro c hc
    rw [hSset, Finset.mem_image] at hc
    obtain ⟨b, hb, rfl⟩ := hc
    rw [hBfil, Finset.mem_filter] at hb
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hb.2⟩
  set S := Sset.filter (fun c => t < rep A B c) with hSdef
  have hSsub : S ⊆ Finset.univ \ (A' * B') :=
    (Finset.filter_subset _ _).trans hSsetsub
  have hSt : ∀ c ∈ S, t ≤ rep A B c := by
    intro c hc
    rw [hSdef, Finset.mem_filter] at hc
    omega
  have hsplit : Sset.card ≤ S.card + F.card := by
    have hsub : Sset ⊆ S ∪ F := by
      intro c hc
      by_cases hlt : t < rep A B c
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, hlt⟩)
      · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨?_, by omega⟩)
        rw [hSset, Finset.mem_image] at hc
        obtain ⟨b, hb, rfl⟩ := hc
        rw [hBfil, Finset.mem_filter] at hb
        exact mem_smul_finset_iff.2 (by simpa using hB'W hb.1)
    calc Sset.card ≤ (S ∪ F).card := Finset.card_le_card hsub
      _ ≤ S.card + F.card := Finset.card_union_le _ _
  have hcos := card_mulStab_le_filter_add_holes' hB'ne hsmall ha hna hsatA
  have hrho : holes (mulStab (A' * B')) A' B'
      = ((A' * mulStab (A' * B')) \ A').card + ((B' * mulStab (A' * B')) \ B').card := rfl
  refine case41_core hXY hA' hB' hA'ne hB'ne hrep hsubAB hdef hsmall hsatA hsatB hSsub hSt ?_
  rw [hrho]
  rw [← hBfil] at hcos
  omega

/-- **The two-sided deletion branch of Grynkiewicz's CASE 4.1.**  When the omitted point lies in
`Y ⊆ A ∩ B`, its products split between the two translates `b · A` and `b · B`, and the pigeonhole
of the unstuffing lemma applies. -/
theorem case41_branch_two {A B X Y A' B' : Finset G} {t : ℕ} {b : G}
    (hXY : X.card + Y.card = A.card + B.card)
    (hA' : A' ⊆ X) (hB' : B' ⊆ Y) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hrep : ∀ c : G, rep X Y c ≤ rep A B c)
    (hsubAB : A' * B' ⊆ repSet A B t)
    (hdef : defect X A' Y B' + 1 ≤ t)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    (hsatA : ∀ z ∈ X, z ∈ A' * mulStab (A' * B') → z ∈ A')
    (hsatB : ∀ z ∈ Y, z ∈ B' * mulStab (A' * B') → z ∈ B')
    (hXAB : X ⊆ A ∪ B)
    (hb : b ∈ Y) (hnb : b ∉ B') (hbA : b ∈ A) (hbB : b ∈ B) :
    PollardWeak A B t
      ∨ (repSum (A.erase b) B t + t ≤ repSum A B t)
      ∨ (repSum A (B.erase b) t + t ≤ repSum A B t) := by
  classical
  set F₁ := (b • A).filter (fun c => rep A B c ≤ t) with hF₁
  set F₂ := (b • B).filter (fun c => rep A B c ≤ t) with hF₂
  by_cases hbig : 2 * t ≤ F₂.card + F₁.card + 1
  · exact Or.inr (exists_erase_drop A B t hbA hbB hbig)
  left
  have hFsmall : F₂.card + F₁.card + 2 ≤ 2 * t := by omega
  have hBA : B' * A' = A' * B' := mul_comm B' A'
  have hsatB' : ∀ z ∈ Y, z ∈ B' * mulStab (B' * A') → z ∈ B' := by
    intro z hz hmem
    rw [hBA] at hmem
    exact hsatB z hz hmem
  have hsmall' : (B' * A').card + 2 ≤ B'.card + A'.card := by rw [hBA]; omega
  have hcos := card_mulStab_le_filter_add_holes' hA'ne hsmall' hb hnb hsatB'
  rw [hBA] at hcos
  set Afil := A'.filter (fun a => b * a ∉ A' * B') with hAfil
  set Sset := Afil.image (fun a => b * a) with hSset
  have hcardSset : Sset.card = Afil.card := by
    rw [hSset]
    exact Finset.card_image_of_injective _ (mul_right_injective b)
  have hSsetsub : Sset ⊆ Finset.univ \ (A' * B') := by
    intro c hc
    rw [hSset, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    rw [hAfil, Finset.mem_filter] at ha
    exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, ha.2⟩
  set S := Sset.filter (fun c => t < rep A B c) with hSdef
  have hSsub : S ⊆ Finset.univ \ (A' * B') := (Finset.filter_subset _ _).trans hSsetsub
  have hSt : ∀ c ∈ S, t ≤ rep A B c := by
    intro c hc
    rw [hSdef, Finset.mem_filter] at hc
    omega
  have hsplit : Sset.card ≤ S.card + F₁.card + F₂.card := by
    have hsub : Sset ⊆ S ∪ (F₁ ∪ F₂) := by
      intro c hc
      by_cases hlt : t < rep A B c
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hc, hlt⟩)
      refine Finset.mem_union_right _ ?_
      rw [hSset, Finset.mem_image] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      rw [hAfil, Finset.mem_filter] at ha
      rcases Finset.mem_union.1 (hXAB (hA' ha.1)) with haA | haB
      · exact Finset.mem_union_left _ (Finset.mem_filter.2
          ⟨mem_smul_finset_iff.2 (by simpa using haA), by omega⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2
          ⟨mem_smul_finset_iff.2 (by simpa using haB), by omega⟩)
    calc Sset.card ≤ (S ∪ (F₁ ∪ F₂)).card := Finset.card_le_card hsub
      _ ≤ S.card + (F₁ ∪ F₂).card := Finset.card_union_le _ _
      _ ≤ S.card + (F₁.card + F₂.card) := by
          have := Finset.card_union_le F₁ F₂
          omega
      _ = S.card + F₁.card + F₂.card := by omega
  have hrho : holes (mulStab (A' * B')) A' B'
      = ((A' * mulStab (A' * B')) \ A').card + ((B' * mulStab (A' * B')) \ B').card := rfl
  refine case41_core hXY hA' hB' hA'ne hB'ne hrep hsubAB hdef hsmall hsatA hsatB hSsub hSt ?_
  rw [hrho]
  omega

end GaloisForLFunctions.HTGeometry.AddComb
