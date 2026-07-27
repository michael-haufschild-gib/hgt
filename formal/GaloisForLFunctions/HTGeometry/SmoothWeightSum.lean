import GaloisForLFunctions.HTGeometry.SmoothWeight

/-!
# The smoothed sum differs from the sharp one by at most the window length

Replacing the sharp cutoff `n ≤ K` by the smooth one costs only the terms in the transition window
`(K, K+H]`, of which there are at most `H + 1`.  With unit-bounded coefficients the two sums
therefore differ by at most `H + 1`.

This is the elementary half of the smoothed Perron argument: the analytic half bounds the smoothed
sum by `N^{Θ+ε}`, and choosing `H` of that size makes the two errors the same order.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The smoothing error.**  For unit-bounded coefficients the smoothed sum and the sharp partial
sum differ by at most `H + 1`. -/
theorem norm_weighted_sub_partialSum_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {H : ℝ} (hH : 0 < H)
    (K m : ℕ) (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ‖(∑ n ∈ Finset.range m, a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
        - ∑ n ∈ Finset.range (K + 1), a n‖ ≤ H + 1 := by
  classical
  set f : ℕ → ℂ := fun n => a n * ((smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ) with hf
  have hKm : K + 1 ≤ m := by
    by_contra hc
    have hle : (m : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le hc)
    linarith
  have hdiff : (∑ n ∈ Finset.range m, f n) - ∑ n ∈ Finset.range (K + 1), a n
      = ∑ n ∈ Finset.Ico (K + 1) m, f n := by
    have hsplit : (∑ n ∈ Finset.range (K + 1), f n) + ∑ n ∈ Finset.Ico (K + 1) m, f n
        = ∑ n ∈ Finset.range m, f n := Finset.sum_range_add_sum_Ico f hKm
    have hone : ∑ n ∈ Finset.range (K + 1), f n = ∑ n ∈ Finset.range (K + 1), a n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      have hnK : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hn
      rw [hf]
      simp only
      rw [smoothWeight_eq_one hH hnK]
      simp
    rw [← hsplit, hone]
    ring
  rw [hdiff]
  -- terms vanish once `n ≥ K + 1 + ⌈H⌉₊`
  have hvanish : ∀ n : ℕ, K + 1 + ⌈H⌉₊ ≤ n → f n = 0 := by
    intro n hn
    have hge : (K : ℝ) + H ≤ (n : ℝ) := by
      have h1 : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
      have h2 : ((K + 1 + ⌈H⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    rw [hf]
    simp only
    rw [smoothWeight_eq_zero hH hge]
    simp
  have hsub : ∑ n ∈ Finset.Ico (K + 1) m, f n
      = ∑ n ∈ Finset.Ico (K + 1) (min m (K + 1 + ⌈H⌉₊)), f n := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro n hn
      rw [Finset.mem_Ico] at hn ⊢
      exact ⟨hn.1, lt_of_lt_of_le hn.2 (min_le_left _ _)⟩
    · intro n hn hnot
      rw [Finset.mem_Ico] at hn hnot
      exact hvanish n (by omega)
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.Ico (K + 1) (min m (K + 1 + ⌈H⌉₊)), ‖f n‖ ≤ 1 := by
    intro n _
    rw [hf]
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (smoothWeight_nonneg _ _ _)]
    nlinarith [ha n, norm_nonneg (a n), smoothWeight_le_one (K : ℝ) H (n : ℝ),
      smoothWeight_nonneg (K : ℝ) H (n : ℝ)]
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 hterm) ?_
  rw [nsmul_eq_mul, mul_one, Nat.card_Ico]
  have hcard : (min m (K + 1 + ⌈H⌉₊) - (K + 1) : ℕ) ≤ ⌈H⌉₊ := by omega
  have hcast : ((min m (K + 1 + ⌈H⌉₊) - (K + 1) : ℕ) : ℝ) ≤ (⌈H⌉₊ : ℝ) := by exact_mod_cast hcard
  have hceil : (⌈H⌉₊ : ℝ) < H + 1 := Nat.ceil_lt_add_one hH.le
  linarith

end GaloisForLFunctions.HTGeometry
