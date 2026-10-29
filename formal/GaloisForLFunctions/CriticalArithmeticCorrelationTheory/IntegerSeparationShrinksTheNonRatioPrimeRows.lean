import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTouchingCrossMatrixHasAUniformErrorBudget
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OverlapLengthControlsTheTouchingCrossError
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap

/-!
# Integer separation shrinks the actual non-ratio prime rows

If one of two distinct positive integers is at most `N`, their logarithmic
distance exceeds `1/(N+1)`. The autocorrelation therefore uses at most the
remaining overlap length. Keeping this factor inside the prime row estimate
makes the first overlap correction small as its width ratio approaches one.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis
open _root_.RHTower (vonMangoldtAtom vonMangoldtAtom_nonneg' vonMangoldtAtom_eq_zero_of_lt_two)

/-- One integer inside the horizon suffices for a reciprocal log-gap bound. -/
theorem inv_succ_horizon_lt_integer_log_gap {N n j : ℕ}
    (hn : n ∈ Icc 1 N) (hj : 1 ≤ j) (hne : n ≠ j) :
    1 / ((N : ℝ) + 1) < |Real.log j - Real.log n| := by
  by_cases hjN : j ≤ N + 1
  · have h := inv_horizon_lt_integer_log_gap
      (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans (Nat.le_succ N)⟩)
      (mem_Icc.mpr ⟨hj, hjN⟩) hne
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hnN : n < N + 1 := Nat.lt_succ_of_le (mem_Icc.mp hn).2
  have hpos : 0 < Real.log (N + 1 : ℕ) - Real.log n :=
    sub_pos.mpr (Real.log_lt_log hn0 (by exact_mod_cast hnN))
  have h := inv_horizon_lt_integer_log_gap
    (mem_Icc.mpr ⟨(mem_Icc.mp hn).1, hnN.le⟩)
    (mem_Icc.mpr ⟨by omega, le_rfl⟩ : N + 1 ∈ Icc 1 (N + 1)) (by omega : n ≠ N + 1)
  rw [abs_of_pos hpos] at h
  have hlog : Real.log (N + 1 : ℕ) ≤ Real.log j :=
    Real.log_le_log (by positivity) (by exact_mod_cast (not_le.mp hjN).le)
  have hgap : 1 / ((N : ℝ) + 1) < Real.log (N + 1 : ℕ) - Real.log n := by
    simpa only [Nat.cast_add, Nat.cast_one] using h
  exact hgap.trans_le
    ((sub_le_sub_right hlog _).trans (le_abs_self _))

private theorem abs_nonRatio_term_le_overlap {g : ℝ → ℝ} {w B : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hB : 0 ≤ B) (hheight : ∀ u, |g u| ≤ B) {N k m n : ℕ}
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hn : n ∈ Icc 1 N) :
    |(if n = k * m then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log m)))| ≤
      (B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) * upInd w k m n := by
  classical
  let A : ℝ := B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg B) (le_max_left _ _)
  unfold upInd upWin
  by_cases hne : n = k * m
  · rw [if_pos hne, abs_zero]
    exact mul_nonneg hA (by split_ifs <;> norm_num)
  rw [if_neg hne]
  by_cases hwin : |Real.log k - (Real.log n - Real.log m)| ≤ w
  · rw [if_pos ⟨hne, hwin⟩, mul_one]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hlog : Real.log k - (Real.log n - Real.log m) =
        Real.log (k * m : ℕ) - Real.log n := by
      rw [Nat.cast_mul, Real.log_mul hk0.ne' hm0.ne']
      ring
    have hgap := inv_succ_horizon_lt_integer_log_gap hn (by nlinarith : 1 ≤ k * m) hne
    rw [← hlog] at hgap
    change |bumpAutocorr g _| ≤ _
    exact (abs_bumpAutocorr_le_overlap_length hg hsupp hB hheight hwin).trans
      (mul_le_mul_of_nonneg_left
        ((sub_le_sub_left hgap.le w).trans (le_max_right _ _)) (sq_nonneg B))
  · rw [if_neg (fun h => hwin h.2), mul_zero,
      bumpCorr_eq_zero hsupp (not_le.mp hwin), abs_zero]

private theorem abs_nonRatioLag_le_overlap {g : ℝ → ℝ} {w B : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hB : 0 ≤ B) (hheight : ∀ u, |g u| ≤ B) (N : ℕ) {k : ℕ}
    (hk : 1 ≤ k) (x : ℕ → ℝ) :
    |nonRatioLag g N k x| ≤ (B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) *
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
        |x m| * |x n| * (upInd w k m n + upInd w k n m) := by
  unfold nonRatioLag
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
  rw [mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
  have h₁ := abs_nonRatio_term_le_overlap hg hsupp hB hheight hk (mem_Icc.mp hm).1 hn
  have h₂ := abs_nonRatio_term_le_overlap hg hsupp hB hheight hk (mem_Icc.mp hn).1 hm
  rw [nonRatio_down_eq, bumpCorr_neg] at *
  rw [abs_mul, abs_mul]
  calc
    _ ≤ |x m| * |x n| *
        ((B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) * upInd w k n m +
          (B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) * upInd w k m n) :=
      mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h₂ h₁)) (by positivity)
    _ = _ := by ring

/-- The actual prime correction pays only the overlap left after integer separation,
including every prime power and every signed coefficient vector. -/
theorem abs_nonRatioForm_le_overlap_rows {g : ℝ → ℝ} {w B : ℝ}
    (hg : Continuous g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (hB : 0 ≤ B) (hheight : ∀ u, |g u| ≤ B) (N : ℕ) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤ (B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))) *
      ∑ m ∈ Icc 1 N, x m ^ 2 * nonRatioRow w N m := by
  classical
  let K := ⌈(N : ℝ) * Real.exp w⌉₊ + 1
  let A : ℝ := B ^ 2 * max 0 (w - 1 / ((N : ℝ) + 1))
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg B) (le_max_left _ _)
  have hfin : nonRatioForm g N x =
      ∑ k ∈ range K, vonMangoldtAtom k * nonRatioLag g N k x := by
    unfold nonRatioForm
    refine tsum_eq_sum fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simp [nonRatioLag]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hbig : (N : ℝ) * Real.exp w < k := by
      have hceil := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have hstep : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at hstep
      linarith only [hceil, hstep]
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [nonRatioLag_eq_zero_of_log_lt hsupp hw hlog, mul_zero]
  let V : ℕ → ℕ → ℝ := fun m n =>
    ∑ k ∈ range K, vonMangoldtAtom k * (upInd w k m n + upInd w k n m)
  have hV0 : ∀ m n, 0 ≤ V m n := fun m n => sum_nonneg fun k _ =>
    mul_nonneg (vonMangoldtAtom_nonneg' k)
      (add_nonneg (upInd_nonneg _ _ _ _) (upInd_nonneg _ _ _ _))
  have hVsym : ∀ m n, V m n = V n m := fun m n => sum_congr rfl fun k _ => by ring
  have h₁ : |nonRatioForm g N x| ≤
      A * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |x m| * |x n| * V m n := by
    rw [hfin]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ k ∈ range K, vonMangoldtAtom k *
          (A * ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            |x m| * |x n| * (upInd w k m n + upInd w k n m)) := by
        refine sum_le_sum fun k _ => ?_
        by_cases hk : 1 ≤ k
        · rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left
            (abs_nonRatioLag_le_overlap hg hsupp hB hheight N hk x) (vonMangoldtAtom_nonneg' k)
        · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega : k < 2), zero_mul, zero_mul, abs_zero]
      _ = _ := by
        simp only [V, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun n _ => sum_congr rfl fun k _ => ?_
        ring
  have h₂ := sum_abs_mul_le_schur N x V hV0 hVsym
  have hrow : ∀ m ∈ Icc 1 N,
      ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n ≤ nonRatioRow w N m := by
    intro m hm
    have heq : (∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * V m n) =
        (∑ k ∈ range K, vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n) +
        ∑ k ∈ range K, vonMangoldtAtom k *
          ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k n m := by
      simp only [V, mul_sum, ← sum_add_distrib]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun n _ => ?_
      ring
    rw [heq]
    exact add_le_add (up_row_le hw (mem_Icc.mp hm).1 K) (down_row_le hw (mem_Icc.mp hm).1 K)
  exact h₁.trans ((mul_le_mul_of_nonneg_left h₂ hA).trans
    (mul_le_mul_of_nonneg_left (sum_le_sum fun m hm =>
      mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)) hA))

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_nonRatioForm_le_overlap_rows
