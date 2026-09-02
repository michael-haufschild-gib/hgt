import GaloisForLFunctions.RHTower.Sieve.FibreMovingWindowNormalization

namespace RHTower.Sieve

open Finset

noncomputable section

theorem variableWindowSq_le_quantized (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (z : ℕ) (L Q : ℕ) :
    fixedWindowSq f L z ≤ 2 * fixedWindowSq f Q z + 2 * |(L : ℝ) - (Q : ℝ)| ^ 2 := by
  have hbase := fixedWindowSq_le_of_close hf z L z Q
  have hend : |(((z + L : ℕ) : ℝ) - ((z + Q : ℕ) : ℝ))| = |(L : ℝ) - (Q : ℝ)| := by
    push_cast
    ring_nf
  simpa [hend] using hbase

theorem sum_quantizedWindowSq_le_sum_dyadicMeanSquare_image (f : ℕ → ℝ)
    (Q : ℕ → ℕ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ y ∈ Finset.Icc A B, fixedWindowSq f (Q y) (y - 1))
      ≤ ∑ ℓ ∈ (Finset.Icc A B).image Q, dyadicMeanSquare f ℓ (A - 1) (B - 1) := by
  classical
  have hterm : ∀ y ∈ Finset.Icc A B,
      fixedWindowSq f (Q y) (y - 1)
        ≤ ∑ ℓ ∈ (Finset.Icc A B).image Q, fixedWindowSq f ℓ (y - 1) := by
    intro y hy
    exact Finset.single_le_sum
      (fun ℓ _ => fixedWindowSq_nonneg f ℓ (y - 1))
      (Finset.mem_image.2 ⟨y, hy, rfl⟩)
  calc
    (∑ y ∈ Finset.Icc A B, fixedWindowSq f (Q y) (y - 1))
        ≤ ∑ y ∈ Finset.Icc A B,
            ∑ ℓ ∈ (Finset.Icc A B).image Q, fixedWindowSq f ℓ (y - 1) :=
      Finset.sum_le_sum hterm
    _ = ∑ ℓ ∈ (Finset.Icc A B).image Q,
          ∑ y ∈ Finset.Icc A B, fixedWindowSq f ℓ (y - 1) := by
      rw [Finset.sum_comm]
    _ = ∑ ℓ ∈ (Finset.Icc A B).image Q,
          dyadicMeanSquare f ℓ (A - 1) (B - 1) := by
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      exact sum_fixedWindowSq_pred_Icc f ℓ A B hA hAB

theorem sum_variableWindowSq_le_sum_dyadicMeanSquare_image_add_quantizationError
    (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (L Q : ℕ → ℕ)
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ y ∈ Finset.Icc A B, fixedWindowSq f (L y) (y - 1))
      ≤ 2 * ∑ ℓ ∈ (Finset.Icc A B).image Q,
          dyadicMeanSquare f ℓ (A - 1) (B - 1)
        + 2 * ∑ y ∈ Finset.Icc A B, |(L y : ℝ) - (Q y : ℝ)| ^ 2 := by
  have hpoint : ∀ y ∈ Finset.Icc A B,
      fixedWindowSq f (L y) (y - 1)
        ≤ 2 * fixedWindowSq f (Q y) (y - 1)
          + 2 * |(L y : ℝ) - (Q y : ℝ)| ^ 2 :=
    fun y _ => variableWindowSq_le_quantized f hf (y - 1) (L y) (Q y)
  have hsum := Finset.sum_le_sum hpoint
  have hfixed := sum_quantizedWindowSq_le_sum_dyadicMeanSquare_image f Q hA hAB
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  nlinarith

/-- Terminal finite-partition normalization of the fibre mean square. -/
theorem sum_innerFibre_sq_le_finitePartition (f : ℕ → ℝ)
    (hf : ∀ n, |f n| ≤ 1) {x h : ℝ} (hx : 4 < x) (hh : 0 ≤ h) (Q : ℕ → ℕ) :
    (∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ 2)
      ≤ 16 * ∑ ℓ ∈
          (Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊).image Q,
            dyadicMeanSquare f ℓ (⌈Real.sqrt x / 2⌉₊ - 1) (⌈Real.sqrt x⌉₊ - 1)
        + 16 * ∑ y ∈ Finset.Icc ⌈Real.sqrt x / 2⌉₊ ⌈Real.sqrt x⌉₊,
            |(movingFibreWindowLength x h y : ℝ) - (Q y : ℝ)| ^ 2
        + 2 * ((outerBlock x h).card : ℝ) * (h / Real.sqrt x + 2) ^ 2 := by
  have hs2 : 2 < Real.sqrt x := by
    have hs := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hx
    norm_num at hs ⊢
    exact hs
  have hA : 1 ≤ ⌈Real.sqrt x / 2⌉₊ := by
    exact Nat.one_le_ceil_iff.2 (by linarith)
  have hAB : ⌈Real.sqrt x / 2⌉₊ ≤ ⌈Real.sqrt x⌉₊ := by
    exact Nat.ceil_mono (by nlinarith [Real.sqrt_nonneg x])
  have hbridge := sum_innerFibre_sq_le_movingWindowSq_add_rounding f hf hx hh
  have hpartition :=
    sum_variableWindowSq_le_sum_dyadicMeanSquare_image_add_quantizationError
      f hf (movingFibreWindowLength x h) Q hA hAB
  nlinarith

end

end RHTower.Sieve
