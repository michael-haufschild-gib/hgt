import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCoset

/-!
# The stabiliser bound of Grynkiewicz's STEP 1

`pollard_step1_smallDoubling` proves the stabiliser alternative of Grynkiewicz's theorem in the
branch `#(A' · B') + 2 ≤ #A' + #B'`, assuming that `A'` and `B'` are saturated in `A` and `B` for
the stabiliser `H = S(A' · B')` and that `A' · B'` is the set of `t`-representable products.

The proof combines three inputs: the counting bound `repSum_ge_of_repSet_eq`, Fubini
(`sum_rep_eq_sum_card_filter`, `sum_rep_eq_sum_card_filter'`), and the coset claim
`card_mulStab_le_filter_add_holes'`, which together give
`repSum ≥ t·#(A'·B') + l·(#H − ρ)`; Kneser then converts `#(A'·B')` into `#A' + #B' + ρ − #H`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
theorem rep_eq_card_filter_left (A B : Finset G) (c : G) :
    rep A B c = (A.filter (fun x => x⁻¹ * c ∈ B)).card := by
  classical
  rw [rep_eq_card_inter]
  congr 1
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_smul_finset, Finset.mem_inv',
    smul_eq_mul]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    exact ⟨hx, by simpa using hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, c⁻¹ * x, by simpa using hy, by group⟩

omit [Fintype G] in
/-- Fubini for representation counts restricted to a target set. -/
theorem sum_rep_eq_sum_card_filter (X Y S : Finset G) :
    ∑ c ∈ S, rep X Y c = ∑ x ∈ X, (Y.filter (fun y => x * y ∈ S)).card := by
  classical
  have hL : ∑ c ∈ S, rep X Y c
      = ∑ c ∈ S, ∑ x ∈ X, (if x⁻¹ * c ∈ Y then 1 else 0) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [rep_eq_card_filter_left, ← Finset.card_filter]
  rw [hL, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← Finset.card_filter]
  apply Finset.card_nbij (fun c => x⁻¹ * c)
  · intro c hc
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
    refine ⟨hc.2, ?_⟩
    rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact hc.1
  · intro c hc d hd hcd
    simpa using hcd
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hy ⊢
    refine ⟨x * y, ⟨hy.2, ?_⟩, inv_mul_cancel_left x y⟩
    rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact hy.1


omit [Fintype G] in
theorem rep_comm (A B : Finset G) (c : G) : rep A B c = rep B A c := by
  classical
  rw [rep, rep]
  apply Finset.card_nbij (fun p => (p.2, p.1))
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, by rw [mul_comm]; exact hp.2⟩
  · rintro ⟨x, y⟩ _ ⟨u, v⟩ _ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2]
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢
    exact ⟨(y, x), ⟨⟨hp.1.2, hp.1.1⟩, by rw [mul_comm]; exact hp.2⟩, rfl⟩

omit [Fintype G] in
/-- Fubini grouped by the second factor. -/
theorem sum_rep_eq_sum_card_filter' (X Y S : Finset G) :
    ∑ c ∈ S, rep X Y c = ∑ y ∈ Y, (X.filter (fun x => x * y ∈ S)).card := by
  classical
  rw [Finset.sum_congr rfl (fun c _ => rep_comm X Y c), sum_rep_eq_sum_card_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  congr 1
  apply Finset.filter_congr
  intro x _
  rw [mul_comm]


/-- **STEP 1, small-doubling branch.**  Under saturation and `#(A'·B') + 2 ≤ #A' + #B'`, the
stabiliser bound of Grynkiewicz's theorem holds.  The defect is only required to be at most `t`,
so that the same statement also serves the structural branch of STEP 2, where it equals `t`. -/
theorem pollard_step1_smallDoubling (A B A' B' : Finset G) (t : ℕ)
    (hA' : A' ⊆ A) (hB' : B' ⊆ B) (hA'ne : A'.Nonempty) (hB'ne : B'.Nonempty)
    (hl : defect A A' B B' ≤ t)
    (heq2 : A' * B' ⊆ repSet A B t)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    (hsatA : ∀ x ∈ A, x ∈ A' * mulStab (A' * B') → x ∈ A')
    (hsatB : ∀ y ∈ B, y ∈ B' * mulStab (A' * B') → y ∈ B') :
    t * A.card + t * B.card + (t - defect A A' B B') * holes (mulStab (A' * B')) A' B'
      ≤ repSum A B t + (t - defect A A' B B') * (mulStab (A' * B')).card
        + t * defect A A' B B' := by
  classical
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  -- Kneser and the hole count
  have hKn := card_mul_le_card_mul_mulStab A' B' hA'ne hB'ne
  rw [← hHdef] at hKn
  have hhA := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul A')
  have hhB := Finset.card_sdiff_add_card_eq_card (hHgrp.subset_mul B')
  have hrho : holes H A' B' = ((A' * H) \ A').card + ((B' * H) \ B').card := rfl
  -- the counting bound
  have hcount := repSum_ge_of_repSet_eq A B A' B' t hA' hB' heq2 hl
  -- the two mixed sums, bounded by the coset claim
  have hAsum : (A \ A').card * (H.card - holes H A' B')
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), rep (A \ A') B' c := by
    rw [sum_rep_eq_sum_card_filter]
    calc (A \ A').card * (H.card - holes H A' B')
        = ∑ _a ∈ A \ A', (H.card - holes H A' B') := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ a ∈ A \ A', (B'.filter (fun b => a * b ∈ Finset.univ \ (A' * B'))).card := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          rw [Finset.mem_sdiff] at ha
          have hcos := card_mulStab_le_filter_add_holes' hB'ne hsmall ha.1 ha.2 hsatA
          rw [← hHdef] at hcos
          have hfeq : (B'.filter (fun b => a * b ∈ Finset.univ \ (A' * B'))).card
              = (B'.filter (fun b => a * b ∉ A' * B')).card := by
            congr 1
            apply Finset.filter_congr
            intro b _
            simp
          rw [hfeq, hrho]
          omega
  have hBsum : (B \ B').card * (H.card - holes H A' B')
      ≤ ∑ c ∈ Finset.univ \ (A' * B'), rep A' (B \ B') c := by
    rw [sum_rep_eq_sum_card_filter']
    calc (B \ B').card * (H.card - holes H A' B')
        = ∑ _b ∈ B \ B', (H.card - holes H A' B') := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ B \ B', (A'.filter (fun a => a * b ∈ Finset.univ \ (A' * B'))).card := by
          refine Finset.sum_le_sum (fun b hb => ?_)
          rw [Finset.mem_sdiff] at hb
          have hBA : B' * A' = A' * B' := mul_comm B' A'
          have hsatB' : ∀ y ∈ B, y ∈ B' * mulStab (B' * A') → y ∈ B' := by
            intro y hy hmem
            rw [hBA] at hmem
            exact hsatB y hy hmem
          have hsmall' : (B' * A').card + 2 ≤ B'.card + A'.card := by
            rw [hBA]; omega
          have hcos := card_mulStab_le_filter_add_holes' hA'ne hsmall' hb.1 hb.2 hsatB'
          rw [hBA, ← hHdef] at hcos
          have hfeq : (A'.filter (fun a => a * b ∈ Finset.univ \ (A' * B'))).card
              = (A'.filter (fun a => b * a ∉ A' * B')).card := by
            congr 1
            apply Finset.filter_congr
            intro a _
            simp [mul_comm b a]
          rw [hfeq, hrho]
          omega
  -- assemble
  have hcardA : (A \ A').card + A'.card = A.card := Finset.card_sdiff_add_card_eq_card hA'
  have hcardB : (B \ B').card + B'.card = B.card := Finset.card_sdiff_add_card_eq_card hB'
  have hdef : defect A A' B B' = (A \ A').card + (B \ B').card := rfl
  have hrhole : holes H A' B' + 2 ≤ H.card := by
    rw [hrho]
    omega
  obtain ⟨d, hd⟩ : ∃ d, H.card = holes H A' B' + d := ⟨H.card - holes H A' B', by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, t = defect A A' B B' + s := ⟨t - defect A A' B B', by omega⟩
  have hdval : H.card - holes H A' B' = d := by omega
  have hts : t - defect A A' B B' = s := by omega
  rw [hdval] at hAsum hBsum
  have hPd : A'.card + B'.card ≤ (A' * B').card + d := by omega
  have hsum : t * (A' * B').card + defect A A' B B' * d ≤ repSum A B t := by
    have h1 : (A \ A').card * d + (B \ B').card * d
        ≤ ∑ c ∈ Finset.univ \ (A' * B'), (rep (A \ A') B' c + rep A' (B \ B') c) := by
      rw [Finset.sum_add_distrib]
      omega
    have h2 : defect A A' B B' * d = (A \ A').card * d + (B \ B').card * d := by
      simp only [defect]
      ring
    omega
  have hmain : t * (A'.card + B'.card) ≤ repSum A B t + s * d := by
    have h1 : t * (A'.card + B'.card) ≤ t * ((A' * B').card + d) := Nat.mul_le_mul_left t hPd
    have h2 : t * ((A' * B').card + d) = t * (A' * B').card + t * d := by ring
    have h3 : t * d = defect A A' B B' * d + s * d := by
      rw [hs]
      ring
    omega
  have hexp : t * A.card + t * B.card
      = t * (A'.card + B'.card) + t * defect A A' B B' := by
    rw [← hcardA, ← hcardB]
    simp only [defect]
    ring
  rw [hexp, hd, hts]
  have h4 : s * (holes H A' B' + d) = s * holes H A' B' + s * d := by ring
  omega

end GaloisForLFunctions.HTGeometry.AddComb
