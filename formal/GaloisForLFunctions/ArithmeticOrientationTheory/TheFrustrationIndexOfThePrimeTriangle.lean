import GaloisForLFunctions.ArithmeticOrientationTheory.FrustrationIndexControlsTheGroundEnergy

/-!
# The frustration index of the prime triangle

Two general facts about the frustration index of a symmetric form, and one arithmetic instance.

* **Misaligned pairs come in mirror pairs** (`misalignedCount_eq_two_mul`): for a symmetric
  coupling on a linearly ordered set the misaligned count of any sign vector is twice the number
  of misaligned pairs `i < j`; so the frustration index is even, and an unbalanced form has index
  at least `2` (`two_le_frustrationIndex_of_not_isBalanced`).
* **Three points have index at most two** (`frustrationIndex_le_two_fin3`): switching the two
  neighbours of a vertex into alignment leaves at most one misaligned overlap.
* **The prime triangle has index exactly two** (`frustrationIndex_primeTriangle`): at the
  positions with pairwise sums `log 2, log 3, log 5` and every sufficiently small archimedean
  weight, the odd Weil ledger is unbalanced (Signed Arithmetic Energy Incidence), hence its
  frustration index is `2`: one overlap, in either order, must stay misaligned after every
  switching.  The integer that measures the frustration of the first arithmetic obstruction is
  computed without evaluating a single coupling.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-! ### Mirror pairs -/

theorem orientSign_mul_nonneg (t : ℝ) : 0 ≤ orientSign t * t := by
  rcases lt_trichotomy 0 t with h | rfl | h
  · rw [orientSign_of_pos h]; linarith
  · simp
  · rw [orientSign_of_neg h]; linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For a symmetric coupling on a linearly ordered set, the misaligned count is twice the number
of misaligned pairs `i < j`. -/
theorem misalignedCount_eq_two_mul [LinearOrder ι] {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (s : ι → ℝ) :
    misalignedCount s c =
      2 * (univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2).card := by
  unfold misalignedCount
  set L := univ.filter fun p : ι × ι => p.1 < p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2 with hL
  set G := univ.filter fun p : ι × ι => p.2 < p.1 ∧ 0 < s p.1 * s p.2 * c p.1 p.2 with hG
  have hsplit : (univ.filter fun p : ι × ι => p.1 ≠ p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2) = L ∪ G := by
    ext p
    simp only [hL, hG, mem_union, mem_filter, mem_univ, true_and, ne_eq]
    constructor
    · rintro ⟨hne, hpos⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h, hpos⟩
      · exact Or.inr ⟨h, hpos⟩
    · rintro (⟨h, hpos⟩ | ⟨h, hpos⟩)
      · exact ⟨h.ne, hpos⟩
      · exact ⟨h.ne', hpos⟩
  have hdisj : Disjoint L G := by
    rw [disjoint_left]
    intro p hpL hpG
    simp only [hL, hG, mem_filter, mem_univ, true_and] at hpL hpG
    exact absurd (hpL.1.trans hpG.1) (lt_irrefl _)
  have hcard : G.card = L.card := by
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [hG, hL, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have := hp.2
      rw [hc p.2 p.1]
      linarith [show s p.2 * s p.1 * c p.1 p.2 = s p.1 * s p.2 * c p.1 p.2 by ring]
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [hG, hL, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hq ⊢
      refine ⟨hq.1, ?_⟩
      have := hq.2
      rw [hc q.2 q.1]
      linarith [show s q.2 * s q.1 * c q.1 q.2 = s q.1 * s q.2 * c q.1 q.2 by ring]
  rw [hsplit, card_union_of_disjoint hdisj, hcard]
  ring

/-- **An unbalanced symmetric form has frustration index at least two.** -/
theorem two_le_frustrationIndex_of_not_isBalanced [LinearOrder ι] {c : ι → ι → ℝ}
    (hc : IsSymmetricCoupling c) (hnb : ¬ IsBalanced c) : 2 ≤ frustrationIndex c := by
  obtain ⟨s, hs, hseq⟩ := frustrationIndex_mem c
  have hne : frustrationIndex c ≠ 0 := fun h =>
    hnb ((isBalanced_iff_frustrationIndex_eq_zero c).2 h)
  rw [← hseq, misalignedCount_eq_two_mul hc s] at hne ⊢
  omega

/-! ### Three points -/

/-- **Three points have frustration index at most two.** -/
theorem frustrationIndex_le_two_fin3 {c : Fin 3 → Fin 3 → ℝ} (hc : IsSymmetricCoupling c) :
    frustrationIndex c ≤ 2 := by
  set s : Fin 3 → ℝ := fun i => if i = 0 then 1 else if i = 1 then -orientSign (c 0 1)
    else -orientSign (c 0 2) with hs_def
  have hs0 : s 0 = 1 := by simp [hs_def]
  have hs1 : s 1 = -orientSign (c 0 1) := by simp [hs_def]
  have hs2 : s 2 = -orientSign (c 0 2) := by simp [hs_def]
  have hs : IsSignVector s := by
    intro i
    by_cases h0 : i = 0
    · rw [h0, hs0]; norm_num
    by_cases h1 : i = 1
    · rw [h1, hs1, neg_sq, orientSign_sq]
    have h2 : i = 2 := by omega
    rw [h2, hs2, neg_sq, orientSign_sq]
  refine le_trans (frustrationIndex_le hs c) ?_
  unfold misalignedCount
  have h01 := orientSign_mul_nonneg (c 0 1)
  have h02 := orientSign_mul_nonneg (c 0 2)
  have h10 : c 1 0 = c 0 1 := hc 1 0
  have h20 : c 2 0 = c 0 2 := hc 2 0
  calc (univ.filter fun p : Fin 3 × Fin 3 => p.1 ≠ p.2 ∧ 0 < s p.1 * s p.2 * c p.1 p.2).card
      ≤ ({(1, 2), (2, 1)} : Finset (Fin 3 × Fin 3)).card := by
        apply card_le_card
        intro p hp
        simp only [mem_filter, mem_univ, true_and] at hp
        obtain ⟨hne, hpos⟩ := hp
        obtain ⟨i, j⟩ := p
        fin_cases i <;> fin_cases j <;>
          first
          | exact (hne rfl).elim
          | (simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hs0, hs1, hs2,
                h10, h20] at hpos
             exfalso
             nlinarith [h01, h02])
          | simp
    _ = 2 := card_pair (by decide)

/-! ### The prime triangle -/

/-- **The prime triangle has frustration index two**: at the positions with pairwise sums
`log 2, log 3, log 5` and every sufficiently small archimedean–polar weight, the odd Weil ledger
has exactly one misaligned overlap (in either order) after every switching. -/
theorem frustrationIndex_primeTriangle :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, |α| < α₀ → ∀ b : Fin 3 → ℝ,
      frustrationIndex (oddFold primeTrianglePos (weilLedgerKernel α 1) b) = 2 := by
  obtain ⟨α₀, hα₀, hunb⟩ := exists_weight_oddWeilLedger_primeTriangle_not_isBalanced
  refine ⟨α₀, hα₀, fun α hα b => ?_⟩
  have hsym : IsSymmetricCoupling (oddFold primeTrianglePos (weilLedgerKernel α 1) b) :=
    oddFold_isSymmetric (weilLedgerKernel_neg α 1)
  exact le_antisymm (frustrationIndex_le_two_fin3 hsym)
    (two_le_frustrationIndex_of_not_isBalanced hsym (hunb α hα b))

end

end GaloisForLFunctions.ArithmeticOrientationTheory
