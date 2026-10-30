import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap

/-!
# The physical mass of overlapping logarithmic atoms

An autocorrelation row meets only atoms in a logarithmic window. Counting
the corresponding integers bounds the full Gram form uniformly at every
fixed overlap, for arbitrary signed coefficients and arbitrary compact bumps.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Finset

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics

private theorem log_window_row_le {w : ℝ} (hw : 0 ≤ w) {N m : ℕ}
    (hm : m ∈ Icc 1 N) :
    (∑ n ∈ Icc 1 N, if |Real.log n - Real.log m| ≤ w then (1 : ℝ) else 0) ≤
      1 + 2 * m * (Real.exp w - 1) := by
  let S := (Icc 1 N).filter (fun n : ℕ => |Real.log n - Real.log m| ≤ w)
  let T := (Icc 1 N).filter
    (fun n => n ≠ m ∧ |(n : ℝ) - m| ≤ m * (Real.exp w - 1))
  have he : 0 ≤ Real.exp w - 1 := by linarith only [Real.add_one_le_exp w, hw]
  have hsub : S ⊆ insert m T := by
    intro n hn
    obtain ⟨hnN, hlog⟩ := mem_filter.mp hn
    by_cases hnm : n = m
    · exact mem_insert.mpr (Or.inl hnm)
    · refine mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hnN, hnm, ?_⟩))
      exact abs_sub_le_of_abs_log_le
        (by exact_mod_cast (mem_Icc.mp hnN).1)
        (by exact_mod_cast (mem_Icc.mp hm).1) hlog
  have hcard : (S.card : ℝ) ≤ 1 + 2 * m * (Real.exp w - 1) := by
    have hnear := card_near_le (Icc 1 N) m (show 0 ≤ (m : ℝ) * (Real.exp w - 1) by positivity)
    have hsubR : (S.card : ℝ) ≤ (insert m T).card := by exact_mod_cast card_le_card hsub
    have hinsR : ((insert m T).card : ℝ) ≤ (T.card : ℝ) + 1 := by
      exact_mod_cast card_insert_le m T
    change (T.card : ℝ) ≤ 2 * ((m : ℝ) * (Real.exp w - 1)) at hnear
    linarith only [hsubR, hinsR, hnear]
  simpa only [S, ← sum_filter, sum_const, nsmul_eq_mul, mul_one] using hcard

/-- A logarithmic window controls the entire overlap Gram form, including signed packets. -/
theorem integral_atomicTest_sq_le_overlap_rows {g : ℝ → ℝ} {w : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw : 0 ≤ w)
    (N : ℕ) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u ^ 2) ≤
      (∫ u, g u ^ 2) * (1 + 2 * N * (Real.exp w - 1)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  let G := ∫ u, g u ^ 2
  let B : ℕ → ℕ → ℝ := fun m n => if |Real.log n - Real.log m| ≤ w then 1 else 0
  have hG : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hB : ∀ m n, 0 ≤ B m n := fun m n => by dsimp only [B]; split_ifs <;> norm_num
  have hBs : ∀ m n, B n m = B m n := fun m n => by simp only [B, abs_sub_comm]
  have hc : ∀ m n : ℕ, |bumpCorr g (-(Real.log n - Real.log m))| ≤ G * B m n := by
    intro m n
    dsimp only [B]
    by_cases h : |Real.log n - Real.log m| ≤ w
    · rw [if_pos h, mul_one]
      exact abs_bumpCorr_le hg hgc _
    · rw [if_neg h, mul_zero, bumpCorr_eq_zero hsupp (by simpa only [abs_neg] using not_le.mp h), abs_zero]
  have hpoint : ∀ m n, x m * x n * bumpCorr g (-(Real.log n - Real.log m)) ≤
      (G / 2) * (x m ^ 2 * B m n + x n ^ 2 * B m n) := by
    intro m n
    have hx : |x m * x n| ≤ (x m ^ 2 + x n ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|x m| - |x n|), sq_abs (x m), sq_abs (x n)]
    calc
      _ ≤ |x m * x n * bumpCorr g (-(Real.log n - Real.log m))| := le_abs_self _
      _ = |x m * x n| * |bumpCorr g (-(Real.log n - Real.log m))| := abs_mul _ _
      _ ≤ ((x m ^ 2 + x n ^ 2) / 2) * (G * B m n) :=
        mul_le_mul hx (hc m n) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hswap : (∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x n ^ 2 * B m n) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m ^ 2 * B m n := by
    rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by rw [hBs]
  have hrow : ∀ m ∈ Icc 1 N, (∑ n ∈ Icc 1 N, B m n) ≤
      1 + 2 * N * (Real.exp w - 1) := by
    intro m hm
    have hlocal := log_window_row_le hw hm
    have he : 0 ≤ Real.exp w - 1 := by linarith only [Real.add_one_le_exp w, hw]
    have hscale := mul_le_mul_of_nonneg_right
      (show (m : ℝ) ≤ N by exact_mod_cast (mem_Icc.mp hm).2) he
    exact hlocal.trans (by linarith only [hscale])
  rw [integral_atomicTest_sq_eq_gram hg hgc]
  calc
    _ ≤ ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        (G / 2) * (x m ^ 2 * B m n + x n ^ 2 * B m n) :=
      sum_le_sum fun m _ => sum_le_sum fun n _ => hpoint m n
    _ = G * ∑ m ∈ Icc 1 N, x m ^ 2 * ∑ n ∈ Icc 1 N, B m n := by
      simp only [← mul_sum, sum_add_distrib, hswap]
      ring
    _ ≤ G * ∑ m ∈ Icc 1 N, x m ^ 2 * (1 + 2 * N * (Real.exp w - 1)) :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)) hG
    _ = _ := by rw [← sum_mul]; ring

/-- At overlap `c`, the physical Gram operator has a bound independent of the horizon. -/
theorem integral_atomicTest_sq_le_fixed_overlap {g : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hc : 0 < c) (hN : 1 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (c / N) → g u = 0) (x : ℕ → ℝ) :
    (∫ u, atomicTest N x g u ^ 2) ≤
      (∫ u, g u ^ 2) * (1 + 2 * c * Real.exp c) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hwc : c / N ≤ c := by
    rw [div_le_iff₀ hNR]
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith only [hNR1, hc]
  have he : (N : ℝ) * (Real.exp (c / N) - 1) ≤ c * Real.exp c := by
    calc
      _ ≤ N * (c / N * Real.exp (c / N)) :=
        mul_le_mul_of_nonneg_left exp_sub_one_le_mul_exp hNR.le
      _ = c * Real.exp (c / N) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hwc) hc.le
  have h := integral_atomicTest_sq_le_overlap_rows hg hgc hsupp (by positivity) N x
  have hG : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith only [he]) hG) hS)

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis

#print axioms GaloisForLFunctions.SpacingScaleHarmonicAnalysis.integral_atomicTest_sq_le_fixed_overlap
