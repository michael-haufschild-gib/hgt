import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepOne

/-!
# The coset claim of Grynkiewicz's STEP 1

Let `H = S(A' · B')`, suppose `A'` is *saturated* in `A` (no point of `A` outside `A'` lies in
`A' · H`), and suppose the small-doubling hypothesis `#(A' · B') + 2 ≤ #A' + #B'`.  Then every
`a ∈ A \ A'` sends at least `#H − ρ_B` points of `B'` outside `A' · B'`, where `ρ_B` is the number
of `H`-holes of `B'`.

The source routes this through the quotient `G ⧸ H`, the equality
`#(φA' · φB') = #φA' + #φB' − 1`, and the critical-pair lemma.  The argument used here is shorter
and stays inside `G`: if `a · B' ⊆ A' · B'` then `(A' ∪ {a}) · B' = A' · B'`, so Kneser applies to
the pair `(A' ∪ {a}, B')` with the same stabiliser `H`; since `a ∉ A' · H`, the coset `a • H` is
disjoint from `A' · H`, and Kneser then forces `#A' + #B' ≤ #(A' · B')`, contradicting small
doubling.  The witness `b'` produced this way carries its whole `H`-coset slice of `B'` with it,
because `A' · B'` is `H`-stable.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- A point of `A` outside a saturated `A'` produces a product outside `A' · B'`.  The proof
compares Kneser's bound for `(A' ∪ {a}, B')` with the small-doubling hypothesis. -/
theorem exists_mul_notMem {A' B' : Finset G} (hB'ne : B'.Nonempty)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    {a : G} (haH : a ∉ A' * mulStab (A' * B')) :
    ∃ b ∈ B', a * b ∉ A' * B' := by
  classical
  by_contra hcon
  push Not at hcon
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  set C : Finset G := insert a A' with hCdef
  have hCB : C * B' = A' * B' := by
    refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_mul] at hx
      obtain ⟨u, hu, v, hv, rfl⟩ := hx
      rw [hCdef, Finset.mem_insert] at hu
      rcases hu with rfl | hu
      · exact hcon v hv
      · exact mul_mem_mul hu hv
    · rw [mem_mul] at hx ⊢
      obtain ⟨u, hu, v, hv, rfl⟩ := hx
      exact ⟨u, by rw [hCdef]; exact Finset.mem_insert_of_mem hu, v, hv, rfl⟩
  have hCne : C.Nonempty := ⟨a, by rw [hCdef]; exact Finset.mem_insert_self a A'⟩
  have hkn := card_mul_le_card_mul_mulStab C B' hCne hB'ne
  rw [hCB, ← hHdef] at hkn
  -- `C * H` is the disjoint union of `A' * H` and the coset `a • H`
  have hCH : C * H = A' * H ∪ (a • H) := by
    rw [hCdef, Finset.insert_eq, Finset.union_mul, Finset.singleton_mul, Finset.union_comm]
  have hdisj : Disjoint (A' * H) (a • H) := by
    rw [Finset.disjoint_right]
    intro z hz hz'
    apply haH
    have hcoset : z • H = a • H := hHgrp.smul_eq_smul_of_mem hz
    have hzH : z • H ⊆ A' * H := hHgrp.smul_subset_mul hz'
    rw [hcoset] at hzH
    exact hzH (hHgrp.mem_smul_self a)
  have hcardCH : (C * H).card = (A' * H).card + H.card := by
    rw [hCH, Finset.card_union_of_disjoint hdisj, Finset.card_smul_finset]
  have hA'sub : A'.card ≤ (A' * H).card :=
    Finset.card_le_card (hHgrp.subset_mul A')
  have hB'sub : B'.card ≤ (B' * H).card :=
    Finset.card_le_card (hHgrp.subset_mul B')
  rw [hcardCH] at hkn
  omega


/-- A whole coset's worth of elements of `B'` is pushed outside `A' · B'` by a single witness. -/
theorem card_mulStab_le_filter_add_holes {A' B' : Finset G} {a b' : G}
    (hb' : b' ∈ B') (hab' : a * b' ∉ A' * B') :
    (mulStab (A' * B')).card
      ≤ (B'.filter (fun b => a * b ∉ A' * B')).card
        + ((B' * mulStab (A' * B')) \ B').card := by
  classical
  set H := mulStab (A' * B') with hHdef
  have hHgrp : IsSubgroupFinset H := isSubgroupFinset_mulStab (A' * B')
  have hcosetout : ∀ y ∈ (a * b') • H, y ∉ A' * B' := by
    intro y hy hyin
    apply hab'
    have hcoset : y • H = (a * b') • H := hHgrp.smul_eq_smul_of_mem hy
    have hsub : y • H ⊆ A' * B' := smul_mulStab_subset hyin
    rw [hcoset] at hsub
    exact hsub (hHgrp.mem_smul_self (a * b'))
  have hsub1 : B' ∩ (b' • H) ⊆ B'.filter (fun b => a * b ∉ A' * B') := by
    intro b hb
    rw [Finset.mem_inter] at hb
    rw [Finset.mem_filter]
    refine ⟨hb.1, ?_⟩
    obtain ⟨h, hh, hbh⟩ := mem_smul_finset.1 hb.2
    simp only [smul_eq_mul] at hbh
    have hmem : a * b ∈ (a * b') • H := by
      rw [mem_smul_finset]
      refine ⟨h, hh, ?_⟩
      simp only [smul_eq_mul]
      rw [← hbh, mul_assoc]
    exact hcosetout _ hmem
  have hsub2 : (b' • H) \ (B' ∩ (b' • H)) ⊆ (B' * H) \ B' := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_inter] at hz
    refine Finset.mem_sdiff.2 ⟨?_, fun hzB => hz.2 ⟨hzB, hz.1⟩⟩
    obtain ⟨h, hh, rfl⟩ := mem_smul_finset.1 hz.1
    exact mul_mem_mul hb' hh
  have hc1 := Finset.card_le_card hsub1
  have hc2 := Finset.card_le_card hsub2
  have hc3 := Finset.card_sdiff_add_card_eq_card
    (Finset.inter_subset_right : B' ∩ (b' • H) ⊆ b' • H)
  have hc4 : (b' • H).card = H.card := Finset.card_smul_finset _ _
  omega

/-- **The coset claim of STEP 1.**  Under saturation and small doubling, every point of `A`
outside `A'` sends at least `#H − ρ_B` points of `B'` outside `A' · B'`. -/
theorem card_mulStab_le_filter_add_holes' {A A' B' : Finset G} (hB'ne : B'.Nonempty)
    (hsmall : (A' * B').card + 2 ≤ A'.card + B'.card)
    {a : G} (ha : a ∈ A) (hana : a ∉ A')
    (hsat : ∀ x ∈ A, x ∈ A' * mulStab (A' * B') → x ∈ A') :
    (mulStab (A' * B')).card
      ≤ (B'.filter (fun b => a * b ∉ A' * B')).card
        + ((B' * mulStab (A' * B')) \ B').card := by
  have haH : a ∉ A' * mulStab (A' * B') := fun h => hana (hsat a ha h)
  obtain ⟨b', hb', hab'⟩ := exists_mul_notMem hB'ne hsmall haH
  exact card_mulStab_le_filter_add_holes hb' hab'

end GaloisForLFunctions.HTGeometry.AddComb
