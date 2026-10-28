import GaloisForLFunctions.HTGeometry.IntegerLogGap

/-!
# Integer logarithmic gaps after a separated window shift

At width at most `c/N`, with `c<1`, each distinct positive integer pair retains
at least the fraction `1-c` of its relative integer gap. The resulting
inverse-square estimate controls literal atom-integral replacement errors.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- A separated window leaves a fixed fraction of every relative integer gap. -/
theorem relative_integer_gap_le_log_gap_sub_window {n j N : ℕ} {c w : ℝ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hc : 0 ≤ c) (hw : w ≤ c / N) :
    (1 - c) * |(n : ℝ) - j| / max (n : ℝ) j ≤
      |Real.log n - Real.log j| - w := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  have hN0 : (0 : ℝ) < N := hn0.trans_le (by exact_mod_cast (mem_Icc.mp hn).2)
  have hmax0 : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  have hmaxN : max (n : ℝ) j ≤ N :=
    max_le (by exact_mod_cast (mem_Icc.mp hn).2) (by exact_mod_cast (mem_Icc.mp hj).2)
  have hd : (1 : ℝ) ≤ |(n : ℝ) - j| := by
    rcases lt_or_gt_of_ne hnj with h | h
    · have hR : (n : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_neg (by linarith only [hR])]
      linarith only [hR]
    · have hR : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_pos (by linarith only [hR])]
      linarith only [hR]
  have hinv : 1 / (N : ℝ) ≤ |(n : ℝ) - j| / max (n : ℝ) j := by
    rw [div_le_div_iff₀ hN0 hmax0]
    nlinarith only [hmaxN, mul_nonneg (sub_nonneg.mpr hd) hN0.le]
  have hscaled : c / N ≤ c * (|(n : ℝ) - j| / max (n : ℝ) j) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv hc
  have hlog := gap_div_le_abs_log_div (mem_Icc.mp hn).1 (mem_Icc.mp hj).1 hnj
  rw [Real.log_div hn0.ne' hj0.ne'] at hlog
  calc
    _ = |(n : ℝ) - j| / max (n : ℝ) j -
        c * (|(n : ℝ) - j| / max (n : ℝ) j) := by ring
    _ ≤ |Real.log n - Real.log j| - w := sub_le_sub hlog (hw.trans hscaled)

/-- Strictly separated width ratios leave every actual logarithmic lag positive. -/
theorem integer_log_gap_sub_window_pos {n j N : ℕ} {c w : ℝ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hc : 0 ≤ c) (hc1 : c < 1) (hw : w ≤ c / N) :
    0 < |Real.log n - Real.log j| - w := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hd : 0 < |(n : ℝ) - j| := by
    rw [abs_pos, sub_ne_zero]
    exact_mod_cast hnj
  have hm : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  exact (div_pos (mul_pos (sub_pos.mpr hc1) hd) hm).trans_le
    (relative_integer_gap_le_log_gap_sub_window hn hj hnj hc hw)

/-- The window-shifted reciprocal square is paid by the integer difference square. -/
theorem inv_sq_integer_log_gap_sub_window_le {n j N : ℕ} {c w : ℝ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hc : 0 ≤ c) (hc1 : c < 1) (hw : w ≤ c / N) :
    1 / (|Real.log n - Real.log j| - w) ^ 2 ≤
      (max (n : ℝ) j) ^ 2 / ((1 - c) ^ 2 * |(n : ℝ) - j| ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  have hd : 0 < |(n : ℝ) - j| := by
    rw [abs_pos, sub_ne_zero]
    exact_mod_cast hnj
  have hm : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  have ha : 0 < (1 - c) * |(n : ℝ) - j| / max (n : ℝ) j :=
    div_pos (mul_pos (sub_pos.mpr hc1) hd) hm
  have hgap := relative_integer_gap_le_log_gap_sub_window hn hj hnj hc hw
  have hsq : ((1 - c) * |(n : ℝ) - j| / max (n : ℝ) j) ^ 2 ≤
      (|Real.log n - Real.log j| - w) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hgap) (add_nonneg (ha.le.trans hgap) ha.le)]
  calc
    _ ≤ 1 / ((1 - c) * |(n : ℝ) - j| / max (n : ℝ) j) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos ha) hsq
    _ = _ := by
      field_simp [hm.ne', hd.ne', (sub_pos.mpr hc1).ne']

end GaloisForLFunctions.HTGeometry
