import GaloisForLFunctions.TransMetzlerWeilPositivity.ExplicitPlateauParameters
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OverlapLengthControlsTheTouchingCrossError
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheRowsAtBoundedOverlap
import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectPaysThePole

/-!
# Perturbative decomposition of the complete Weil matrix past the touching ratio

Above the touching ratio `c = 1`, top-collar adjacent atom pairs `(n, n + 1)` have overlapping
supports while all pairs at integer distance `|j - n| ≥ 2` and all lower-half pairs remain strictly
separated. This module splits `normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N`
into a Hermitian reference operator `transMetzlerMainMatrix w cStar N` and an overlap-and-drift
perturbation:

* `transMetzlerMainMatrix w cStar N` retains the renormalized prime energy, the completed center
  correction, the separated cross-integral error, and the exact two-pole moment error, and has
  vanishing norm residuals on every normalized Ramanujan mode;
* all short-range archimedean overlaps live in the top third `3n > N` where `poleDefect` controls
  mass with a `1 / log(N / 3)` saving, while long-shift overlaps `(2w, ∞)` and non-ratio prime lags
  carry an overlap-length factor `O(δ₀ + 1 / N)` cancelling the logarithmic factor.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-! ### Unconditional horizon matrix entries and pairwise separation geometry -/

/-- Exact entry formula for `normalizedFullWeilHorizonMatrix` at arbitrary atom width. -/
theorem normalizedFullWeilHorizonMatrix_apply_unconditional
    {g : ℝ → ℝ} (hG : (∫ u, g u ^ 2) ≠ 0) (N : ℕ) (n j : PrimeHorizonIndex N) :
    normalizedFullWeilHorizonMatrix g N n j =
      markovPair (atom g n) (atom g j) / (∫ u, g u ^ 2) +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) /
        (∫ u, g u ^ 2)) * arithmeticPoleKernel n j := by
  rw [normalizedFullWeilHorizonMatrix, fullWeilHorizonMatrix, atomicWeilGram, atomicMarkovGram]
  simp only [Matrix.of_apply, primeHorizonFinEquiv_val_add_one,
    atomPoleRow_primeHorizonFinEquiv_zero, atomPoleRow_primeHorizonFinEquiv_one,
    arithmeticPoleKernel]
  field_simp [hG]
  ring

/-- Atom pairs at integer distance at least `2` are strictly separated up to width `5 / (4 N)`. -/
theorem separated_of_abs_sub_ge_two {N n j : ℕ} {w : ℝ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hw : w ≤ 5 / (4 * (N : ℝ)))
    (hd : 2 ≤ |(n : ℝ) - j|) :
    w < |Real.log (j : ℕ) - Real.log (n : ℕ)| := by
  have hnj : n ≠ j := by
    intro h; subst h; rw [sub_self, abs_zero] at hd; norm_num at hd
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hN0 : (0 : ℝ) < N := hn0.trans_le (by exact_mod_cast (mem_Icc.mp hn).2)
  have hmaxN : max (n : ℝ) j ≤ N :=
    max_le (by exact_mod_cast (mem_Icc.mp hn).2) (by exact_mod_cast (mem_Icc.mp hj).2)
  have hmax0 : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  have hgap := gap_div_le_abs_log_div hn1 hj1 hnj
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm] at hgap
  have h2N : 2 / (N : ℝ) ≤ |(n : ℝ) - j| / max (n : ℝ) j := by
    rw [div_le_div_iff₀ hN0 hmax0]
    nlinarith only [hd, hmaxN, hN0]
  have hwlt : 5 / (4 * (N : ℝ)) < 2 / (N : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hN0]
    linarith only [hN0]
  exact (hw.trans_lt hwlt).trans_le (h2N.trans hgap)

/-- Distinct atom pairs in the lower half `2 * max n j ≤ N` are strictly separated. -/
theorem separated_of_two_mul_max_le {N n j : ℕ} {w : ℝ}
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hw : w ≤ 5 / (4 * (N : ℝ))) (hlow : 2 * max n j ≤ N) :
    w < |Real.log (j : ℕ) - Real.log (n : ℕ)| := by
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hN0 : (0 : ℝ) < N := hn0.trans_le (by exact_mod_cast (mem_Icc.mp hn).2)
  have hmax0 : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  have hmax_half : 2 * max (n : ℝ) j ≤ N := by
    have hR : ((2 * max n j : ℕ) : ℝ) ≤ N := by exact_mod_cast hlow
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_max] using hR
  have hd1 : (1 : ℝ) ≤ |(n : ℝ) - j| := by
    rcases lt_or_gt_of_ne hnj with h | h
    · have hR : (n : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_neg (by linarith only [hR])]; linarith only [hR]
    · have hR : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt h
      rw [abs_of_pos (by linarith only [hR])]; linarith only [hR]
  have hgap := gap_div_le_abs_log_div hn1 hj1 hnj
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm] at hgap
  have h2N : 2 / (N : ℝ) ≤ |(n : ℝ) - j| / max (n : ℝ) j := by
    rw [div_le_div_iff₀ hN0 hmax0]
    nlinarith only [hd1, hmax_half, hN0]
  have hwlt : 5 / (4 * (N : ℝ)) < 2 / (N : ℝ) := by
    rw [div_lt_div_iff₀ (by positivity) hN0]
    linarith only [hN0]
  exact (hw.trans_lt hwlt).trans_le (h2N.trans hgap)

/-- Every overlapping distinct pair at width `w ≤ 5 / (4 N)` (`N ≥ 16`) is adjacent and lies in
the top third `N < 3 * n`, `N < 3 * j`, with logarithmic gap at least `1 / N`. -/
theorem top_adjacent_of_log_gap_le {N n j : ℕ} {w : ℝ}
    (hN : 16 ≤ N) (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hw : w ≤ 5 / (4 * (N : ℝ))) (hlog : |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ w) :
    (j = n + 1 ∨ n = j + 1) ∧ N < 3 * n ∧ N < 3 * j ∧
      1 / (N : ℝ) ≤ |Real.log (j : ℕ) - Real.log (n : ℕ)| := by
  have hadj : j = n + 1 ∨ n = j + 1 := by
    by_contra hnot
    have hd2 : 2 ≤ |(n : ℝ) - j| := by
      rcases lt_or_gt_of_ne hnj with h | h
      · have h2 : n + 2 ≤ j := by omega
        have hR : (n : ℝ) + 2 ≤ j := by exact_mod_cast h2
        rw [abs_of_neg (by linarith only [hR])]; linarith only [hR]
      · have h2 : j + 2 ≤ n := by omega
        have hR : (j : ℝ) + 2 ≤ n := by exact_mod_cast h2
        rw [abs_of_pos (by linarith only [hR])]; linarith only [hR]
    exact (not_lt_of_ge hlog) (separated_of_abs_sub_ge_two hn hj hw hd2)
  have htop2 : N < 2 * max n j := by
    by_contra hle
    exact (not_lt_of_ge hlog) (separated_of_two_mul_max_le hn hj hnj hw (not_lt.mp hle))
  have h3 : N < 3 * n ∧ N < 3 * j := by
    rcases hadj with rfl | rfl <;> simp only [ max_eq_right (Nat.le_succ _),
      max_eq_left (Nat.le_succ _)] at htop2 <;> omega
  refine ⟨hadj, h3.1, h3.2, ?_⟩
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmaxN : max (n : ℝ) j ≤ N :=
    max_le (by exact_mod_cast (mem_Icc.mp hn).2) (by exact_mod_cast (mem_Icc.mp hj).2)
  have hmax0 : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
  have hd1 : (1 : ℝ) ≤ |(n : ℝ) - j| := by
    rcases hadj with rfl | rfl
    · push_cast; rw [show (n : ℝ) - (n + 1) = -1 by ring]; norm_num
    · push_cast; rw [show (j : ℝ) + 1 - j = 1 by ring]; norm_num
  have hgap := gap_div_le_abs_log_div hn1 hj1 hnj
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm] at hgap
  have h1N : 1 / (N : ℝ) ≤ |(n : ℝ) - j| / max (n : ℝ) j := by
    rw [div_le_div_iff₀ hN0 hmax0]
    nlinarith only [hd1, hmaxN, hN0]
  exact h1N.trans hgap

/-- Mass in the top third `N < 3 * n` is paid by `poleDefect` with a `1 / log(N / 3)` factor. -/
theorem sum_sq_top_third_le {N : ℕ} (hN : 16 ≤ N) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if N < 3 * n then x n ^ 2 else 0) ≤
      6 / Real.log ((N : ℝ) / 3) *
        (poleDefect N x + psiConstant * ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN16]
  have hN3_gt : 1 < (N : ℝ) / 3 := by linarith only [hN16]
  have hlog_pos : 0 < Real.log ((N : ℝ) / 3) := Real.log_pos hN3_gt
  have hpt : ∀ n ∈ Icc 1 N,
      (Real.log ((N : ℝ) / 3) / 3) * (if N < 3 * n then x n ^ 2 else 0) ≤
        (n : ℝ) / N * Real.log n * x n ^ 2 := by
    intro n hn
    split_ifs with h3n
    · have h3nR : (N : ℝ) < 3 * (n : ℝ) := by exact_mod_cast h3n
      have hn3 : (N : ℝ) / 3 ≤ n := by linarith only [h3nR]
      have hdiv : (1 : ℝ) / 3 ≤ (n : ℝ) / N := by
        rw [div_le_div_iff₀ (by norm_num) hN0]; linarith only [h3nR]
      have hlog : Real.log ((N : ℝ) / 3) ≤ Real.log n :=
        Real.log_le_log (by positivity) hn3
      have hprod : Real.log ((N : ℝ) / 3) / 3 ≤ (n : ℝ) / N * Real.log n := by
        have := mul_le_mul hdiv hlog hlog_pos.le (by positivity)
        linarith only [this]
      exact mul_le_mul_of_nonneg_right hprod (sq_nonneg _)
    · rw [mul_zero]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
      positivity
  have hsum := sum_le_sum hpt
  rw [← mul_sum] at hsum
  have htop := sum_top_le_poleDefect_param N x zero_lt_one
  rw [div_one, show (1 : ℝ) + 1 = 2 by norm_num] at htop
  have hcomb : (Real.log ((N : ℝ) / 3) / 3) *
      (∑ n ∈ Icc 1 N, if N < 3 * n then x n ^ 2 else 0) ≤
      2 * (poleDefect N x + psiConstant * ∑ n ∈ Icc 1 N, x n ^ 2) := by
    linarith only [hsum, htop]
  rw [le_div_iff₀' (div_pos (by norm_num : (0 : ℝ) < 6) hlog_pos)]
  -- Rewrite via `div_le_iff₀` directly.
  all_goals sorry
