import Mathlib

/-!
# The weight gap of a zero-sum dominant integer vector

A dominant integer weight of the collective adjoint action is a decreasing integer vector of total
sum zero, and its Casimir value is the sum of its squares plus the sum of all its ordered
differences.  This file proves that a nonzero such weight has Casimir value at least twice the
dimension.

The proof splits the index set into its positive, zero and negative blocks.  Writing `A` for the
positive mass, the squares contribute at least `2A`, because every positive entry is at least one
and every negative entry is at most minus one.  Every pair with a positive first entry and a
non-positive second entry, and every pair with a zero first entry and a negative second entry, is
already ordered, so the ordered differences contribute at least `(D + z)A` with `z` the number of
zeros.  Since `2A` is at least the number of nonzero entries and `A` is at least one, the two
contributions add up to at least `2D`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section WeightGap

variable {α : Type*} [Fintype α] [LinearOrder α]

/-- The Casimir value of a weight: the sum of squares plus the sum of ordered differences. -/
def weightCasimir (mu : α → ℤ) : ℤ :=
  (∑ a, (mu a) ^ (2 : ℕ)) +
    ∑ p ∈ Finset.univ.filter (fun p : α × α => p.1 < p.2), (mu p.1 - mu p.2)

/-- **The weight gap.**  A nonzero decreasing zero-sum integer weight has Casimir value at least
twice the dimension. -/
theorem two_mul_card_le_weightCasimir (mu : α → ℤ)
    (hsum : ∑ a, mu a = 0)
    (hmono : ∀ a b : α, a < b → mu b ≤ mu a)
    (hne : ∃ a, mu a ≠ 0) :
    2 * (Fintype.card α : ℤ) ≤ weightCasimir mu := by
  classical
  set Pos : Finset α := Finset.univ.filter fun a => 0 < mu a with hPos
  set Neg : Finset α := Finset.univ.filter fun a => mu a < 0 with hNeg
  set Zer : Finset α := Finset.univ.filter fun a => mu a = 0 with hZer
  set A : ℤ := ∑ a ∈ Pos, mu a with hA
  have hmemPos : ∀ a : α, a ∈ Pos ↔ 0 < mu a := by intro a; simp [hPos]
  have hmemNeg : ∀ a : α, a ∈ Neg ↔ mu a < 0 := by intro a; simp [hNeg]
  have hmemZer : ∀ a : α, a ∈ Zer ↔ mu a = 0 := by intro a; simp [hZer]
  have hcompl : (Pos : Finset α)ᶜ = Zer ∪ Neg := by
    ext a
    simp only [Finset.mem_compl, Finset.mem_union, hmemPos, hmemZer, hmemNeg]
    omega
  have hZNdisj : Disjoint Zer Neg := by
    rw [Finset.disjoint_left]
    intro a ha han
    rw [hmemZer] at ha
    rw [hmemNeg] at han
    omega
  have hunion : (Finset.univ : Finset α) = Pos ∪ Zer ∪ Neg := by
    ext a
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, hmemPos, hmemZer, hmemNeg]
    omega
  have hzerosum : (∑ a ∈ Zer, mu a) = 0 :=
    Finset.sum_eq_zero fun a ha => (hmemZer a).mp ha
  have hcomplsum : (∑ a ∈ (Pos : Finset α)ᶜ, mu a) = -A := by
    have hall : (∑ a, mu a) = (∑ a ∈ Pos, mu a) + ∑ a ∈ (Pos : Finset α)ᶜ, mu a := by
      rw [← Finset.sum_add_sum_compl Pos mu]
    rw [hsum] at hall
    omega
  have hnegsum : (∑ a ∈ Neg, mu a) = -A := by
    rw [hcompl, Finset.sum_union hZNdisj, hzerosum, zero_add] at hcomplsum
    exact hcomplsum
  -- the positive block is nonempty and carries mass at least one
  have hposne : Pos.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hle : ∀ b : α, mu b ≤ 0 := by
      intro b
      by_contra hb
      have hmem : b ∈ Pos := (hmemPos b).mpr (by omega)
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty b)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hle b)).mp hsum
    obtain ⟨a, ha⟩ := hne
    exact ha (hall a (Finset.mem_univ a))
  have hposge : ∀ b ∈ Pos, 1 ≤ mu b := fun b hb => by
    have := (hmemPos b).mp hb
    omega
  have hnegle : ∀ b ∈ Neg, mu b ≤ -1 := fun b hb => by
    have := (hmemNeg b).mp hb
    omega
  have hA1 : 1 ≤ A := by
    obtain ⟨a, ha⟩ := hposne
    calc (1 : ℤ) ≤ mu a := hposge a ha
      _ ≤ ∑ b ∈ Pos, mu b :=
        Finset.single_le_sum (fun b hb => le_trans zero_le_one (hposge b hb)) ha
  have hposcard : (Pos.card : ℤ) ≤ A := by
    have h := Finset.card_nsmul_le_sum Pos mu 1 hposge
    simpa using h
  have hnegcard : (Neg.card : ℤ) ≤ A := by
    have h := Finset.sum_le_card_nsmul Neg mu (-1) hnegle
    rw [hnegsum] at h
    simp only [nsmul_eq_mul, mul_neg, mul_one] at h
    omega
  -- the squares
  have hsq : 2 * A ≤ ∑ a, (mu a) ^ (2 : ℕ) := by
    have hPN : Disjoint Pos Neg := by
      rw [Finset.disjoint_left]
      intro a ha han
      rw [hmemPos] at ha
      rw [hmemNeg] at han
      omega
    have hsub : (∑ a ∈ Pos ∪ Neg, (mu a) ^ (2 : ℕ)) ≤ ∑ a, (mu a) ^ (2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun a _ _ => sq_nonneg _
    have hposq : A ≤ ∑ a ∈ Pos, (mu a) ^ (2 : ℕ) := by
      refine le_trans (le_of_eq rfl) (Finset.sum_le_sum ?_)
      intro b hb
      have h1 := hposge b hb
      nlinarith [h1]
    have hnegq : A ≤ ∑ a ∈ Neg, (mu a) ^ (2 : ℕ) := by
      have hstep : (∑ a ∈ Neg, -mu a) ≤ ∑ a ∈ Neg, (mu a) ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun b hb => ?_
        have h1 := hnegle b hb
        nlinarith [h1]
      rw [Finset.sum_neg_distrib, hnegsum] at hstep
      simpa using hstep
    rw [Finset.sum_union hPN] at hsub
    omega
  -- the ordered differences
  have hpair : ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * A ≤
      ∑ p ∈ Finset.univ.filter (fun p : α × α => p.1 < p.2), (mu p.1 - mu p.2) := by
    set S : Finset (α × α) := Finset.univ.filter (fun p : α × α => p.1 < p.2) with hS
    set T1 : Finset (α × α) := Pos ×ˢ (Pos : Finset α)ᶜ with hT1
    set T2 : Finset (α × α) := Zer ×ˢ Neg with hT2
    have hT1S : T1 ⊆ S := by
      intro p hp
      rw [hT1, Finset.mem_product] at hp
      have hp1 : 0 < mu p.1 := (hmemPos p.1).mp hp.1
      have hp2 : ¬ (0 < mu p.2) := by
        intro h
        exact (Finset.mem_compl.mp hp.2) ((hmemPos p.2).mpr h)
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ p, ?_⟩
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact h
      · rw [h] at hp1; omega
      · have := hmono p.2 p.1 h; omega
    have hT2S : T2 ⊆ S := by
      intro p hp
      rw [hT2, Finset.mem_product] at hp
      have hp1 : mu p.1 = 0 := (hmemZer p.1).mp hp.1
      have hp2 : mu p.2 < 0 := (hmemNeg p.2).mp hp.2
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ p, ?_⟩
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact h
      · rw [h] at hp1; omega
      · have := hmono p.2 p.1 h; omega
    have hTdisj : Disjoint T1 T2 := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [hT1, Finset.mem_product] at hp1
      rw [hT2, Finset.mem_product] at hp2
      have h1 : 0 < mu p.1 := (hmemPos p.1).mp hp1.1
      have h2 : mu p.1 = 0 := (hmemZer p.1).mp hp2.1
      omega
    have hnonneg : ∀ p ∈ S, 0 ≤ mu p.1 - mu p.2 := by
      intro p hp
      rw [hS, Finset.mem_filter] at hp
      have := hmono p.1 p.2 hp.2
      omega
    have hsubset : T1 ∪ T2 ⊆ S := Finset.union_subset hT1S hT2S
    have hbig : (∑ p ∈ T1 ∪ T2, (mu p.1 - mu p.2)) ≤ ∑ p ∈ S, (mu p.1 - mu p.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun p hp _ => hnonneg p hp
    have hT1sum : (∑ p ∈ T1, (mu p.1 - mu p.2)) = (Fintype.card α : ℤ) * A := by
      rw [hT1, Finset.sum_product]
      have hstep : ∀ a ∈ Pos, (∑ b ∈ (Pos : Finset α)ᶜ, (mu a - mu b))
          = ((Pos : Finset α)ᶜ.card : ℤ) * mu a + A := by
        intro a _
        rw [Finset.sum_sub_distrib, Finset.sum_const, hcomplsum, nsmul_eq_mul]
        ring
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, ← hA, nsmul_eq_mul]
      have hcard : ((Pos : Finset α)ᶜ.card : ℤ) + (Pos.card : ℤ) = (Fintype.card α : ℤ) := by
        have := Finset.card_add_card_compl Pos
        push_cast [← this]
        ring
      rw [← hcard]
      ring
    have hT2sum : (∑ p ∈ T2, (mu p.1 - mu p.2)) = (Zer.card : ℤ) * A := by
      rw [hT2, Finset.sum_product]
      have hstep : ∀ a ∈ Zer, (∑ b ∈ Neg, (mu a - mu b)) = A := by
        intro a ha
        rw [Finset.sum_sub_distrib, Finset.sum_const, hnegsum, (hmemZer a).mp ha, nsmul_eq_mul,
          mul_zero, zero_sub, neg_neg]
      rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_union hTdisj, hT1sum, hT2sum] at hbig
    calc ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * A
        = (Fintype.card α : ℤ) * A + (Zer.card : ℤ) * A := by ring
      _ ≤ ∑ p ∈ S, (mu p.1 - mu p.2) := hbig
  -- assemble
  have hcardsum : (Pos.card : ℤ) + (Zer.card : ℤ) + (Neg.card : ℤ) = (Fintype.card α : ℤ) := by
    have hPZ : Disjoint Pos Zer := by
      rw [Finset.disjoint_left]
      intro a ha haz
      rw [hmemPos] at ha
      rw [hmemZer] at haz
      omega
    have hPZN : Disjoint (Pos ∪ Zer) Neg := by
      rw [Finset.disjoint_left]
      intro a ha han
      rw [Finset.mem_union, hmemPos, hmemZer] at ha
      rw [hmemNeg] at han
      omega
    have hc := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hPZN, Finset.card_union_of_disjoint hPZ,
      Finset.card_univ] at hc
    rw [hc]
    push_cast
    ring
  have hzA : ((Fintype.card α : ℤ) + (Zer.card : ℤ)) ≤
      ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * A := by
    have hnn : (0 : ℤ) ≤ (Fintype.card α : ℤ) + (Zer.card : ℤ) := by
      have h1 : (0 : ℤ) ≤ (Fintype.card α : ℤ) := Int.natCast_nonneg _
      have h2 : (0 : ℤ) ≤ (Zer.card : ℤ) := Int.natCast_nonneg _
      linarith
    have hprod : 0 ≤ ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * (A - 1) :=
      mul_nonneg hnn (by linarith)
    have hexp : ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * (A - 1)
        = ((Fintype.card α : ℤ) + (Zer.card : ℤ)) * A
          - ((Fintype.card α : ℤ) + (Zer.card : ℤ)) := by ring
    rw [hexp] at hprod
    linarith
  rw [weightCasimir]
  linarith [hsq, hpair, hzA, hposcard, hnegcard, hcardsum]

end WeightGap

end GaloisForLFunctions.HTGeometry
