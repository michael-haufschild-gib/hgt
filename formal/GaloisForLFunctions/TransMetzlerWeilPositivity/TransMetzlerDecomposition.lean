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

open MeasureTheory Filter Topology Finset Matrix RHTower
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticLorentzianGeometry
  ArithmeticElectrostatics HTGeometry

/-! ### Pairwise separation geometry and top-third mass control -/

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
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm (Real.log n) (Real.log j)] at hgap
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
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm (Real.log n) (Real.log j)] at hgap
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
    rcases hadj with rfl | rfl <;>
      simp only [max_eq_right (Nat.le_succ _), max_eq_left (Nat.le_succ _)] at htop2 <;> omega
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
  rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm (Real.log n) (Real.log j)] at hgap
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
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog_pos]
  linarith only [hcomb]

/-- Every quadratic form supported on overlapping distinct pairs at width `w ≤ 5 / (4 N)` is
bounded by twice its uniform entry bound times the top-third square mass. -/
theorem abs_sum_overlapping_pairs_le {N : ℕ} {w B : ℝ}
    (hN : 16 ≤ N) (hw : w ≤ 5 / (4 * (N : ℝ))) (hB : 0 ≤ B)
    (F : ℕ → ℕ → ℝ)
    (hzero : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, (n = j ∨ w < |Real.log j - Real.log n|) → F n j = 0)
    (hbound : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N, n ≠ j → |Real.log j - Real.log n| ≤ w → |F n j| ≤ B)
    (a : ℕ → ℝ) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, a n * a j * F n j| ≤
      2 * B * ∑ n ∈ Icc 1 N, if N < 3 * n then a n ^ 2 else 0 := by
  classical
  have hInd_sym (n j : ℕ) :
      (if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then (1 : ℝ) else 0) =
        if j ≠ n ∧ |Real.log n - Real.log j| ≤ w then 1 else 0 := by
    simp only [ne_comm, abs_sub_comm]
  have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ j ∈ Icc 1 N, if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then (1 : ℝ) else 0) ≤
        if N < 3 * n then 2 else 0 := by
    split_ifs with h3n
    · have hsub : (Icc 1 N).filter (fun j => n ≠ j ∧ |Real.log j - Real.log n| ≤ w) ⊆
          {n - 1, n + 1} := by
        intro j hj
        obtain ⟨hjI, hnj, hlog⟩ := mem_filter.mp hj
        obtain ⟨hadj, -, -, -⟩ := top_adjacent_of_log_gap_le hN hn hjI hnj hw hlog
        simp only [mem_insert, mem_singleton]
        rcases hadj with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by omega)
      have hcard : (((Icc 1 N).filter
          (fun j => n ≠ j ∧ |Real.log j - Real.log n| ≤ w)).card : ℝ) ≤ 2 := by
        have hc := (card_le_card hsub).trans (card_insert_le (n - 1) {n + 1})
        rw [card_singleton] at hc
        exact_mod_cast hc
      rwa [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    · refine le_of_eq (sum_eq_zero fun j hj => ?_)
      split_ifs with h
      · exfalso
        exact h3n (top_adjacent_of_log_gap_le hN hn hj h.1 hw h.2).2.1
      · rfl
  have hschur := finite_weighted_schur_row_potential (Icc 1 N) (fun n => |a n|)
    (fun _ => (1 : ℝ))
    (fun n j => if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then (1 : ℝ) else 0)
    (fun _ _ => zero_lt_one)
    (fun _ _ _ _ => by split_ifs <;> norm_num)
    (fun n _ j _ => hInd_sym n j)
  simp only [div_one, mul_one, sq_abs] at hschur
  have hpt (n : ℕ) (hn : n ∈ Icc 1 N) (j : ℕ) (hj : j ∈ Icc 1 N) :
      |a n * a j * F n j| ≤
        B * (|a n| * |a j| * (if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then 1 else 0)) := by
    by_cases hnj : n = j
    · rw [hzero n hn j hj (Or.inl hnj), mul_zero, abs_zero, if_neg (fun h => h.1 hnj),
        mul_zero, mul_zero]
    · by_cases hlog : |Real.log j - Real.log n| ≤ w
      · rw [if_pos ⟨hnj, hlog⟩, mul_one, abs_mul, abs_mul]
        have hb := mul_le_mul_of_nonneg_left (hbound n hn j hj hnj hlog)
          (mul_nonneg (abs_nonneg (a n)) (abs_nonneg (a j)))
        linarith only [hb]
      · rw [hzero n hn j hj (Or.inr (not_le.mp hlog)), mul_zero, abs_zero,
          if_neg (fun h => hlog h.2), mul_zero, mul_zero]
  calc |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, a n * a j * F n j|
      ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, |a n * a j * F n j| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => abs_sum_le_sum_abs _ _)
    _ ≤ B * ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          |a n| * |a j| * (if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then 1 else 0) := by
        simp only [mul_sum]
        exact sum_le_sum fun n hn => sum_le_sum fun j hj => hpt n hn j hj
    _ ≤ B * ∑ n ∈ Icc 1 N, a n ^ 2 *
          ∑ j ∈ Icc 1 N, (if n ≠ j ∧ |Real.log j - Real.log n| ≤ w then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hschur hB
    _ ≤ B * ∑ n ∈ Icc 1 N, a n ^ 2 * (if N < 3 * n then 2 else 0) :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)) hB
    _ = 2 * B * ∑ n ∈ Icc 1 N, if N < 3 * n then a n ^ 2 else 0 := by
        simp only [mul_sum]
        exact sum_congr rfl fun n _ => by split_ifs <;> ring

/-! ### Reference operator `transMetzlerMainMatrix` and Ramanujan quasimodes -/

/-- The cross-integral replacement error restricted to strictly separated atom pairs. -/
def separatedCrossErrorKernel (g : ℝ → ℝ) (w : ℝ) (n j : ℕ) : ℝ :=
  if w < |Real.log j - Real.log n| then atomCrossErrorKernel g n j else 0

theorem separatedCrossErrorKernel_comm (g : ℝ → ℝ) (w : ℝ) (n j : ℕ) :
    separatedCrossErrorKernel g w n j = separatedCrossErrorKernel g w j n := by
  simp only [separatedCrossErrorKernel, abs_sub_comm, atomCrossErrorKernel_comm]

/-- Uniform reciprocal-square bound on separated cross errors of `transMetzlerProfile`. -/
theorem abs_separatedCrossErrorKernel_transMetzler_le {w : ℝ} {N n j : ℕ}
    (hw0 : 0 < w) (hw1 : w ≤ 1) (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) :
    |separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w n j| ≤
      316 * w ^ 2 * (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
  unfold separatedCrossErrorKernel
  split_ifs with hws
  · have hnj : n ≠ j := by
      intro h; subst h; rw [sub_self, abs_zero] at hws; linarith only [hw0, hws]
    have hn1 := (mem_Icc.mp hn).1
    have hj1 := (mem_Icc.mp hj).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    have hnz : n ≠ 0 := by omega
    have hjz : j ≠ 0 := by omega
    have hspos : 0 < |Real.log j - Real.log n| := hw0.trans hws
    have hM := mul_pos hw0 integral_transMetzlerProfile_sq_pos
    rw [← integral_atomDilate_sq (φ := transMetzlerProfile) hw0] at hM
    rw [atomCrossErrorKernel, if_neg hnj, archimedeanCenterKernel,
      if_neg (by simp only [hnj, hnz, hjz, or_self, not_false_eq_true])]
    have heq : |(atomCrossTerm (atomDilate transMetzlerProfile w) |Real.log j - Real.log n| /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
        ((∫ u, atomDilate transMetzlerProfile w u) ^ 2 /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
          archLevyDensity |Real.log j - Real.log n|)| =
        |atomCrossTerm (atomDilate transMetzlerProfile w) |Real.log j - Real.log n| -
          archLevyDensity |Real.log j - Real.log n| *
            (∫ u, atomDilate transMetzlerProfile w u) ^ 2| /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) := by
      rw [show atomCrossTerm (atomDilate transMetzlerProfile w) |Real.log j - Real.log n| /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
            ((∫ u, atomDilate transMetzlerProfile w u) ^ 2 /
              (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
              archLevyDensity |Real.log j - Real.log n| =
          (atomCrossTerm (atomDilate transMetzlerProfile w) |Real.log j - Real.log n| -
            archLevyDensity |Real.log j - Real.log n| *
              (∫ u, atomDilate transMetzlerProfile w u) ^ 2) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) by ring,
        abs_div, abs_of_pos hM]
    rw [heq]
    have hplat := plateau_crossError_le_uniform etaZero_pos (by norm_num [etaZero]) hw0 hw1 hws
    change |atomCrossTerm (atomDilate transMetzlerProfile w) |Real.log j - Real.log n| -
        archLevyDensity |Real.log j - Real.log n| *
          (∫ u, atomDilate transMetzlerProfile w u) ^ 2| /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2) ≤ _ at hplat
    have hgap := gap_div_le_abs_log_div hn1 hj1 hnj
    rw [Real.log_div hn0.ne' hj0.ne', abs_sub_comm (Real.log n) (Real.log j)] at hgap
    have hmax0 : 0 < max (n : ℝ) j := hn0.trans_le (le_max_left _ _)
    have hd_pos : 0 < |(n : ℝ) - j| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hnj))
    have hsq_gap : (|(n : ℝ) - j| / max (n : ℝ) j) ^ 2 ≤ |Real.log j - Real.log n| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hgap 2
    have hinv : 1 / |Real.log j - Real.log n| ^ 2 ≤ (max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2 := by
      rw [div_pow, div_le_iff₀ (sq_pos_of_pos hmax0)] at hsq_gap
      rw [div_le_div_iff₀ (sq_pos_of_pos hspos) (sq_pos_of_pos hd_pos)]
      linarith only [hsq_gap]
    calc _ ≤ 316 * w ^ 2 / |Real.log j - Real.log n| ^ 2 := hplat
      _ = (316 * w ^ 2) * (1 / |Real.log j - Real.log n| ^ 2) := by ring
      _ ≤ (316 * w ^ 2) * ((max (n : ℝ) j) ^ 2 / |(n : ℝ) - j| ^ 2) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  · rw [abs_zero]
    positivity

/-- Uniform quadratic-form bound for the separated cross-error matrix at arbitrary width `w ≤ 1`. -/
theorem abs_separatedCrossErrorMatrix_inner_le {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin
      (horizonKernelMatrix (separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w) N)
        x, x⟫| ≤ (1264 * (w * N) ^ 2) * ‖x‖ ^ 2 := by
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  have h := abs_kernel_quadratic_le_of_integer_distance (N := N) (K := 316 * w ^ 2) (by positivity)
    (fun n hn j hj => abs_separatedCrossErrorKernel_transMetzler_le hw0 hw1 hn hj)
    (fun n _ j _ => separatedCrossErrorKernel_comm _ w n j) (primeHorizonExtension x)
  refine h.trans_eq ?_
  ring

/-- Scalar error between the normalized two-pole moment product at width `w` and its center value. -/
def poleMomentErrorCoeff (φ : ℝ → ℝ) (w : ℝ) : ℝ :=
  atomExponentialMoment (atomDilate φ w) (-(1 / 2)) *
    atomExponentialMoment (atomDilate φ w) (1 / 2) /
      (∫ u, atomDilate φ w u ^ 2) - w * completeWeilPoleShift φ 1

/-- Two-pole moment replacement error matrix at arbitrary width `w`. -/
def poleMomentErrorMatrix (φ : ℝ → ℝ) (w : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => poleMomentErrorCoeff φ w * arithmeticPoleKernel n j

theorem poleMomentErrorMatrix_isHermitian (φ : ℝ → ℝ) (w : ℝ) (N : ℕ) :
    (poleMomentErrorMatrix φ w N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  change poleMomentErrorMatrix φ w N j n = poleMomentErrorMatrix φ w N n j
  simp only [poleMomentErrorMatrix, arithmeticPoleKernel]
  ring

theorem abs_poleMomentErrorCoeff_transMetzler_le {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) :
    |poleMomentErrorCoeff transMetzlerProfile w| ≤ 6 * w ^ 2 := by
  have h := abs_dilated_pole_product_sub_le contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos hw0 hw1
  have heq : poleMomentErrorCoeff transMetzlerProfile w =
      atomExponentialMoment (atomDilate transMetzlerProfile w) (-(1 / 2)) *
        atomExponentialMoment (atomDilate transMetzlerProfile w) (1 / 2) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
        w * (∫ u, transMetzlerProfile u) ^ 2 / (∫ u, transMetzlerProfile u ^ 2) := by
    unfold poleMomentErrorCoeff completeWeilPoleShift
    ring
  rw [heq]
  exact h.trans (mul_le_mul_of_nonneg_right atomPoleMomentErrorConstant_transMetzlerProfile_le
    (sq_nonneg w))

theorem abs_poleMomentErrorMatrix_inner_le {w : ℝ} (hw0 : 0 < w) (hw1 : w ≤ 1) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile w N) x, x⟫| ≤
      (12 * (w * N) ^ 2) * ‖x‖ ^ 2 := by
  change |⟪Matrix.toEuclideanLin
    (horizonKernelMatrix (fun n j => poleMomentErrorCoeff transMetzlerProfile w *
      (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N) x, x⟫| ≤ _
  rw [horizonKernelMatrix_inner, ← sum_primeHorizonExtension_sq]
  have hd := abs_poleMomentErrorCoeff_transMetzler_le hw0 hw1
  calc |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
        (poleMomentErrorCoeff transMetzlerProfile w *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n))|
      ≤ 2 * |poleMomentErrorCoeff transMetzlerProfile w| * (N : ℝ) ^ 2 *
          ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 :=
        abs_twoPoleKernel_quadratic_le N (primeHorizonExtension x) _
    _ ≤ 2 * (6 * w ^ 2) * (N : ℝ) ^ 2 * ∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _))
          (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

/-- Hermitian reference operator retaining the renormalized prime matrix, center correction at
ratio `cStar`, separated cross-integral error at width `w`, and two-pole moment error at width `w`. -/
def transMetzlerMainMatrix (w cStar : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  (Real.log N + completeWeilSelfFinitePart transMetzlerProfile cStar -
      Real.eulerMascheroniConstant) •
    (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) -
    fullPrimeMatrix N +
    fullWeilCenterMatrix (completeWeilPoleShift transMetzlerProfile cStar) N -
    horizonKernelMatrix (separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w) N +
    poleMomentErrorMatrix transMetzlerProfile w N

theorem transMetzlerMainMatrix_isHermitian (w cStar : ℝ) (N : ℕ) :
    (transMetzlerMainMatrix w cStar N).IsHermitian := by
  have hsep : (horizonKernelMatrix
      (separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w) N).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro n j
    exact separatedCrossErrorKernel_comm _ w j n
  have h1 : ((Real.log N + completeWeilSelfFinitePart transMetzlerProfile cStar -
      Real.eulerMascheroniConstant) •
      (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro n j
    change ((Real.log N + completeWeilSelfFinitePart transMetzlerProfile cStar -
        Real.eulerMascheroniConstant) •
        (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)) j n =
      ((Real.log N + completeWeilSelfFinitePart transMetzlerProfile cStar -
        Real.eulerMascheroniConstant) •
        (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)) n j
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases h : j = n
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  exact (((h1.sub (fullPrimeMatrix_isHermitian N)).add
    (fullWeilCenterMatrix_isHermitian _ N)).sub hsep).add
      (poleMomentErrorMatrix_isHermitian _ w N)

private theorem identity_toEuclideanLin_apply {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

theorem transMetzlerMainMatrix_inner_eq (w cStar : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix w cStar N) x, x⟫ =
      renormalizedPrimeEnergy N x +
        (completeWeilSelfFinitePart transMetzlerProfile cStar -
          Real.eulerMascheroniConstant) * ‖x‖ ^ 2 +
        ⟪Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift transMetzlerProfile cStar) N) x, x⟫ -
        ⟪Matrix.toEuclideanLin
          (horizonKernelMatrix
            (separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w) N) x, x⟫ +
        ⟪Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile w N) x, x⟫ := by
  unfold transMetzlerMainMatrix
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_toEuclideanLin_apply, inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq, renormalizedPrimeEnergy]
  ring

/-- Every normalized Ramanujan vector is a norm quasimode of `transMetzlerMainMatrix (w N) cStar N`
with eigenvalue `completeWeilAdjunctionEnergy transMetzlerProfile cStar m`. -/
theorem tendsto_transMetzlerMainMatrix_ramanujan_residual_norm
    (w : ℕ → ℝ) (cStar : ℝ)
    (hw : ∀ᶠ N : ℕ in atTop, 0 < w N ∧ w N ≤ 2 / (N : ℝ))
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
          (normalizedRamanujanHorizonVector m N) -
        completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hp := tendsto_normalizedRamanujanHorizonVector_residual_norm hm
  have hc := tendsto_fullWeilCenterMatrix_ramanujan_residual_norm hm
    (completeWeilPoleShift transMetzlerProfile cStar)
  have hA : 0 ≤ ∑ j ∈ range m, |normalizedRamanujanMode m j| :=
    sum_nonneg fun _ _ => abs_nonneg _
  have hsep_sq : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin
        (horizonKernelMatrix
          (separatedCrossErrorKernel (atomDilate transMetzlerProfile (w N)) (w N)) N)
        (ramanujanHorizonVector m N)‖ ^ 2 ≤
        (36 * 316 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) * 4) ^ 2 := by
    filter_upwards [hw, eventually_ge_atTop 2] with N ⟨hw0, hw2⟩ hN2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hw1 : w N ≤ 1 := hw2.trans ((div_le_one hN0).mpr (by exact_mod_cast hN2))
    have hwN : w N * N ≤ 2 := (le_div_iff₀ hN0).mp hw2
    have hwN_sq : (w N) ^ 2 * (N : ℝ) ^ 2 ≤ 4 := by
      have h0 : 0 ≤ w N * N := mul_nonneg hw0.le hN0.le
      nlinarith only [hwN, h0]
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix
        (separatedCrossErrorKernel (atomDilate transMetzlerProfile (w N)) (w N)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have h := sum_sq_kernel_poleProfile_le (N := N) (K := 316 * (w N) ^ 2) (by positivity)
      (fun n hn j hj => abs_separatedCrossErrorKernel_transMetzler_le hw0 hw1 hn hj) hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    refine h.trans ?_
    have hbase : 36 * (316 * (w N) ^ 2) * (∑ j ∈ range m, |normalizedRamanujanMode m j|) *
        (N : ℝ) ^ 2 ≤ 36 * 316 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) * 4 := by
      have h1 := mul_le_mul_of_nonneg_left hwN_sq
        (show 0 ≤ 36 * 316 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) by positivity)
      linarith only [h1]
    have hsq := pow_le_pow_left₀ (by positivity) hbase 2
    calc (36 * (316 * (w N) ^ 2) * ∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 *
          (N : ℝ) ^ 4
        = (36 * (316 * (w N) ^ 2) * (∑ j ∈ range m, |normalizedRamanujanMode m j|) *
            (N : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ _ := hsq
  have hx : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin
        (horizonKernelMatrix
          (separatedCrossErrorKernel (atomDilate transMetzlerProfile (w N)) (w N)) N)
        (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
    simpa only [normalizedRamanujanHorizonVector, map_smul] using
      tendsto_horizon_normalized_norm_of_sq_bounded _ hsep_sq
  have hpole_sq : ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile (w N) N)
        (ramanujanHorizonVector m N)‖ ^ 2 ≤
        4 * 36 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * 16 := by
    filter_upwards [hw, eventually_ge_atTop 2] with N ⟨hw0, hw2⟩ hN2
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hw1 : w N ≤ 1 := hw2.trans ((div_le_one hN0).mpr (by exact_mod_cast hN2))
    have hwN : w N * N ≤ 2 := (le_div_iff₀ hN0).mp hw2
    have hwN4 : (w N * N) ^ 4 ≤ 16 := by
      have h0 : 0 ≤ w N * N := mul_nonneg hw0.le hN0.le
      have h2 : (w N * N) ^ 2 ≤ 4 := by nlinarith only [hwN, h0]
      nlinarith only [h2, sq_nonneg (w N * N)]
    have hd := abs_poleMomentErrorCoeff_transMetzler_le hw0 hw1
    have hd_sq : (poleMomentErrorCoeff transMetzlerProfile (w N)) ^ 2 ≤ 36 * (w N) ^ 4 := by
      have hmul := mul_self_le_mul_self (abs_nonneg _) hd
      rw [← sq, sq_abs] at hmul
      linarith only [hmul]
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (fun n j => poleMomentErrorCoeff transMetzlerProfile (w N) *
        (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n)) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have hrow := sum_sq_twoPoleKernel_poleProfile_le hA N
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
      (poleMomentErrorCoeff transMetzlerProfile (w N))
    have hrew : (∑ n ∈ Icc 1 N,
        (∑ j ∈ Icc 1 N, poleMomentErrorCoeff transMetzlerProfile (w N) *
          (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            ramanujanPoleProfile m j) ^ 2) =
      ∑ n ∈ Icc 1 N, (poleMomentErrorCoeff transMetzlerProfile (w N) *
        ∑ j ∈ Icc 1 N, (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
          (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2 := by
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]
      congr 1
      exact sum_congr rfl fun j _ => by simp only [ramanujanPoleProfile, mul_assoc]
    rw [hrew]
    calc (∑ n ∈ Icc 1 N, (poleMomentErrorCoeff transMetzlerProfile (w N) *
          ∑ j ∈ Icc 1 N, (Real.sqrt n / Real.sqrt j + Real.sqrt j / Real.sqrt n) *
            (normalizedRamanujanMode m j / Real.sqrt j)) ^ 2)
        ≤ 4 * (poleMomentErrorCoeff transMetzlerProfile (w N)) ^ 2 *
            (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * (N : ℝ) ^ 4 := hrow
      _ ≤ 4 * (36 * (w N) ^ 4) *
            (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * (N : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd_sq (by norm_num))
              (sq_nonneg _)) (by positivity)
      _ = 4 * 36 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * (w N * N) ^ 4 := by ring
      _ ≤ 4 * 36 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 * 16 :=
          mul_le_mul_of_nonneg_left hwN4 (by positivity)
  have hq : Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile (w N) N)
        (normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
    simpa only [normalizedRamanujanHorizonVector, map_smul] using
      tendsto_horizon_normalized_norm_of_sq_bounded _ hpole_sq
  have hlim := ((hp.add hc).add hx).add hq
  simp only [zero_add] at hlim
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  refine Eventually.of_forall fun N => ?_
  have hdecomp : Matrix.toEuclideanLin (transMetzlerMainMatrix (w N) cStar N)
        (normalizedRamanujanHorizonVector m N) -
      completeWeilAdjunctionEnergy transMetzlerProfile cStar m •
        normalizedRamanujanHorizonVector m N =
      -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
        (Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift transMetzlerProfile cStar) N)
          (normalizedRamanujanHorizonVector m N) -
          (if m = 1 then completeWeilPoleShift transMetzlerProfile cStar else 0) •
            normalizedRamanujanHorizonVector m N) -
        Matrix.toEuclideanLin
          (horizonKernelMatrix
            (separatedCrossErrorKernel (atomDilate transMetzlerProfile (w N)) (w N)) N)
          (normalizedRamanujanHorizonVector m N) +
        Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile (w N) N)
          (normalizedRamanujanHorizonVector m N) := by
    unfold transMetzlerMainMatrix completeWeilAdjunctionEnergy
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, identity_toEuclideanLin_apply]
    module
  rw [hdecomp]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ le_rfl)) le_rfl)
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg]

/-! ### Tight non-ratio prime form bound via overlap length -/

/-- Every non-ratio window `upWin w k m n` at width `1 / (2 N) ≤ w ≤ (1 + δ₀) / N` has
autocorrelation bounded by `3 * (δ₀ + 2 / N)` times the atom `L²` mass. -/
theorem abs_nonRatio_term_transMetzler_le {N k m n : ℕ} {w δ₀ : ℝ}
    (hN : 16 ≤ N) (hk : 1 ≤ k) (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N)
    (hδ0 : 0 ≤ δ₀) (hδ4 : δ₀ ≤ 1 / 4)
    (hw_lo : 1 / (2 * (N : ℝ)) ≤ w) (hw_hi : w ≤ (1 + δ₀) / (N : ℝ)) :
    |(if n = k * m then 0
      else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
        (Real.log k - (Real.log n - Real.log m)))| ≤
      3 * (δ₀ + 2 / (N : ℝ)) *
        (∫ u, atomDilate transMetzlerProfile w u ^ 2) * upInd w k m n := by
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN16]
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw_lo
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : ∫ u, atomDilate transMetzlerProfile w u ^ 2 = w * ∫ u, transMetzlerProfile u ^ 2 :=
    integral_atomDilate_sq hw0
  have hM_ge : 1 / (3 * (N : ℝ)) ≤ ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [hM]
    have hφ := integral_transMetzlerProfile_sq_ge
    have h1 := mul_le_mul hw_lo hφ (by norm_num) hw0.le
    have h2 : (1 : ℝ) / (3 * N) ≤ 1 / (2 * N) * (499 / 500) := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith only [hN0]
    exact h2.trans h1
  unfold upInd upWin
  by_cases h1 : n = k * m
  · rw [if_pos h1, abs_zero]
    have : 0 ≤ ∫ u, atomDilate transMetzlerProfile w u ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    have h2N : 0 ≤ δ₀ + 2 / (N : ℝ) := by positivity
    split_ifs <;> positivity
  · rw [if_neg h1]
    by_cases h2 : |Real.log k - (Real.log n - Real.log m)| ≤ w
    · rw [if_pos ⟨h1, h2⟩, mul_one]
      have hover : |SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
          (Real.log k - (Real.log n - Real.log m))| ≤
          w - |Real.log k - (Real.log n - Real.log m)| := by
        change |bumpAutocorr (atomDilate transMetzlerProfile w)
          (Real.log k - (Real.log n - Real.log m))| ≤ _
        simpa only [one_pow, one_mul] using
          abs_bumpAutocorr_le_overlap_length hg.continuous hgsupp zero_le_one
            (fun u => by
              rw [atomDilate, abs_of_nonneg (transMetzlerProfile_nonneg _)]
              exact transMetzlerProfile_le_one _) h2
      have hm1 := (mem_Icc.mp hm).1
      have hn1 := (mem_Icc.mp hn).1
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hkm1 : 1 ≤ k * m := Nat.mul_pos hk hm1
      have hkm0 : (0 : ℝ) < (k * m : ℕ) := by exact_mod_cast hkm1
      have hup := (upWin_bounds hk hm1 hn1 h2).2.2
      have hkm_le : ((k * m : ℕ) : ℝ) ≤ (N : ℝ) * Real.exp w := by
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have hmul := mul_le_mul_of_nonneg_right (hup.trans hnN) (Real.exp_pos w).le
        have hexp : Real.exp (-w) * Real.exp w = 1 := by rw [← Real.exp_add]; simp
        rw [mul_assoc ((k : ℝ) * m), hexp, mul_one] at hmul
        simpa only [Nat.cast_mul] using hmul
      have hn_le : (n : ℝ) ≤ (N : ℝ) * Real.exp w := by
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
        have h1e : (1 : ℝ) ≤ Real.exp w := by linarith only [Real.add_one_le_exp w, hw0]
        nlinarith only [hnN, h1e, hN0]
      have hmax_le : max (n : ℝ) (k * m : ℕ) ≤ (N : ℝ) * Real.exp w := max_le hn_le hkm_le
      have hmax0 : 0 < max (n : ℝ) (k * m : ℕ) := hn0.trans_le (le_max_left _ _)
      have hd1 : (1 : ℝ) ≤ |(n : ℝ) - (k * m : ℕ)| := by
        rcases lt_or_gt_of_ne h1 with hlt | hgt
        · have hR : (n : ℝ) + 1 ≤ (k * m : ℕ) := by exact_mod_cast Nat.succ_le_of_lt hlt
          rw [abs_of_neg (by linarith only [hR])]; linarith only [hR]
        · have hR : ((k * m : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hgt
          rw [abs_of_pos (by linarith only [hR])]; linarith only [hR]
      have hgap := gap_div_le_abs_log_div hn1 hkm1 h1
      rw [Real.log_div hn0.ne' hkm0.ne'] at hgap
      have hlog_eq : |Real.log (n : ℝ) - Real.log ((k * m : ℕ) : ℝ)| =
          |Real.log k - (Real.log n - Real.log m)| := by
        rw [Nat.cast_mul, Real.log_mul hk0.ne' hm0.ne', abs_sub_comm]
        congr 1; ring
      rw [hlog_eq] at hgap
      have ht_ge : (1 - w) / (N : ℝ) ≤ |Real.log k - (Real.log n - Real.log m)| := by
        have he_ge : 1 - w ≤ Real.exp (-w) := by linarith only [Real.add_one_le_exp (-w)]
        have hexp_inv : Real.exp (-w) / (N : ℝ) ≤ 1 / ((N : ℝ) * Real.exp w) := by
          refine le_of_eq ?_
          rw [Real.exp_neg]
          field_simp [hN0.ne', (Real.exp_pos w).ne']
        have h1max : 1 / ((N : ℝ) * Real.exp w) ≤ |(n : ℝ) - (k * m : ℕ)| / max (n : ℝ) (k * m : ℕ) := by
          rw [div_le_div_iff₀ (by positivity) hmax0, one_mul]
          calc max (n : ℝ) (k * m : ℕ)
              = 1 * max (n : ℝ) (k * m : ℕ) := (one_mul _).symm
            _ ≤ |(n : ℝ) - (k * m : ℕ)| * ((N : ℝ) * Real.exp w) :=
                mul_le_mul hd1 hmax_le hmax0.le (by positivity)
        exact ((div_le_div_of_nonneg_right he_ge hN0.le).trans hexp_inv).trans (h1max.trans hgap)
      have hw_2N : w ≤ 2 / (N : ℝ) := by
        refine hw_hi.trans ?_
        exact div_le_div_of_nonneg_right (by linarith only [hδ4]) hN0.le
      have hdiff : w - |Real.log k - (Real.log n - Real.log m)| ≤ (δ₀ + 2 / (N : ℝ)) / (N : ℝ) := by
        have hsub : w - |Real.log k - (Real.log n - Real.log m)| ≤
            (1 + δ₀) / (N : ℝ) - (1 - w) / (N : ℝ) := sub_le_sub hw_hi ht_ge
        have hstep : (1 + δ₀) / (N : ℝ) - (1 - w) / (N : ℝ) = (δ₀ + w) / (N : ℝ) := by ring
        rw [hstep] at hsub
        exact hsub.trans (div_le_div_of_nonneg_right (by linarith only [hw_2N]) hN0.le)
      have hfinal : (δ₀ + 2 / (N : ℝ)) / (N : ℝ) ≤
          3 * (δ₀ + 2 / (N : ℝ)) * ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
        have h3 := mul_le_mul_of_nonneg_left hM_ge
          (show 0 ≤ 3 * (δ₀ + 2 / (N : ℝ)) by positivity)
        have hsimp : 3 * (δ₀ + 2 / (N : ℝ)) * (1 / (3 * (N : ℝ))) =
            (δ₀ + 2 / (N : ℝ)) / (N : ℝ) := by field_simp [hN0.ne']
        rwa [hsimp] at h3
      exact hover.trans (hdiff.trans hfinal)
    · rw [if_neg (fun h => h2 h.2), mul_zero, bumpCorr_eq_zero hgsupp (not_le.mp h2), abs_zero]

/-- Tight non-ratio prime form bound past the touching ratio: overlap length inserts the factor
`δ₀ + 2 / N` in front of the weighted Schur row bound. -/
theorem abs_nonRatioForm_transMetzler_le {N : ℕ} {w δ₀ : ℝ}
    (hN : 16 ≤ N) (hδ0 : 0 ≤ δ₀) (hδ4 : δ₀ ≤ 1 / 4)
    (hw_lo : 1 / (2 * (N : ℝ)) ≤ w) (hw_hi : w ≤ (1 + δ₀) / (N : ℝ)) (a : ℕ → ℝ) :
    |nonRatioForm (atomDilate transMetzlerProfile w) N a| /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2) ≤
      1050 * (δ₀ + 2 / (N : ℝ)) * (poleDefect N a + ∑ m ∈ Icc 1 N, a m ^ 2) := by
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN16]
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw_lo
  have hw_54 : w ≤ 5 / (4 * (N : ℝ)) := by
    refine hw_hi.trans ?_
    rw [div_le_div_iff₀ hN0 (by positivity)]
    nlinarith only [hδ4, hN0]
  have hw1 : w ≤ 1 := by
    refine hw_54.trans ?_
    rw [div_le_one (by positivity)]
    linarith only [hN16]
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hG : 0 < ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [integral_atomDilate_sq hw0]
    exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  have hfin : nonRatioForm (atomDilate transMetzlerProfile w) N a =
      ∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
        vonMangoldtAtom k * nonRatioLag (atomDilate transMetzlerProfile w) N k a := by
    unfold nonRatioForm
    refine tsum_eq_sum fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    have hbig : (N : ℝ) * Real.exp w < k := by
      have hceil := Nat.le_ceil ((N : ℝ) * Real.exp w)
      have h2 : ((⌈(N : ℝ) * Real.exp w⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2
      linarith only [hceil, h2]
    have hlog : Real.log N + w < Real.log k := by
      rw [← Real.log_exp w, ← Real.log_mul hN0.ne' (Real.exp_pos w).ne']
      exact Real.log_lt_log (by positivity) hbig
    rw [nonRatioLag_eq_zero_of_log_lt hgsupp hw0.le hlog, mul_zero]
  have hlag (k : ℕ) (hk : 1 ≤ k) :
      |nonRatioLag (atomDilate transMetzlerProfile w) N k a| ≤
        3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
            |a m| * |a n| * (upInd w k m n + upInd w k n m) := by
    unfold nonRatioLag
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have h1 := abs_nonRatio_term_transMetzler_le hN hk hm hn hδ0 hδ4 hw_lo hw_hi
    have h2 := abs_nonRatio_term_transMetzler_le hN hk hn hm hδ0 hδ4 hw_lo hw_hi
    rw [nonRatio_down_eq, bumpCorr_neg, abs_mul, abs_mul]
    have haa : 0 ≤ |a m| * |a n| := by positivity
    calc |a m| * |a n| * |_ + _|
        ≤ |a m| * |a n| *
            (3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
                upInd w k n m +
              3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
                upInd w k m n) :=
          mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h2 h1)) haa
      _ = 3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
            (|a m| * |a n| * (upInd w k m n + upInd w k n m)) := by ring
  have hvma0 (k : ℕ) : 0 ≤ vonMangoldtAtom k := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  have hsum_lag : |nonRatioForm (atomDilate transMetzlerProfile w) N a| ≤
      3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
        ∑ m ∈ Icc 1 N, a m ^ 2 * nonRatioRow w N m := by
    rw [hfin]
    have hstep1 : |∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
          vonMangoldtAtom k * nonRatioLag (atomDilate transMetzlerProfile w) N k a| ≤
        3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
          ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, |a m| * |a n| *
            (∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
              vonMangoldtAtom k * (upInd w k m n + upInd w k n m)) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
            |vonMangoldtAtom k * nonRatioLag (atomDilate transMetzlerProfile w) N k a|
          ≤ ∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
              vonMangoldtAtom k *
                (3 * (δ₀ + 2 / (N : ℝ)) * (∫ u, atomDilate transMetzlerProfile w u ^ 2) *
                  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
                    |a m| * |a n| * (upInd w k m n + upInd w k n m)) := by
            refine sum_le_sum fun k _ => ?_
            rcases Nat.eq_zero_or_pos k with rfl | hk
            · simp only [vonMangoldtAtom, show ¬(2 ≤ 0) by omega, ite_false, zero_mul, abs_zero,
                le_rfl]
            · rw [abs_mul, abs_of_nonneg (hvma0 k)]
              exact mul_le_mul_of_nonneg_left (hlag k hk) (hvma0 k)
        _ = _ := by
            simp only [mul_sum]
            rw [sum_comm]
            refine sum_congr rfl fun m _ => ?_
            rw [sum_comm]
            exact sum_congr rfl fun n _ => sum_congr rfl fun k _ => by ring
    have hschur := sum_abs_mul_le_schur N a
      (fun m n => ∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
        vonMangoldtAtom k * (upInd w k m n + upInd w k n m))
      (fun m n => sum_nonneg fun k _ =>
        mul_nonneg (hvma0 k) (add_nonneg (upInd_nonneg _ _ _ _) (upInd_nonneg _ _ _ _)))
      (fun m n => sum_congr rfl fun k _ => by ring)
    have hrow : ∀ m ∈ Icc 1 N,
        ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) *
          (∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
            vonMangoldtAtom k * (upInd w k m n + upInd w k n m)) ≤
          nonRatioRow w N m := by
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      have heq : ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) *
          (∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
            vonMangoldtAtom k * (upInd w k m n + upInd w k n m)) =
          (∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
            vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k m n) +
          ∑ k ∈ range (⌈(N : ℝ) * Real.exp w⌉₊ + 1),
            vonMangoldtAtom k * ∑ n ∈ Icc 1 N, Real.sqrt ((m : ℝ) / n) * upInd w k n m := by
        simp only [mul_sum, ← sum_add_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      rw [heq]
      exact add_le_add (up_row_le hw0.le hm1 _) (down_row_le hw0.le hm1 _)
    exact hstep1.trans ((mul_le_mul_of_nonneg_left hschur (by positivity)).trans
      (mul_le_mul_of_nonneg_left
        (sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _))
        (by positivity)))
  -- Bound `nonRatioRow w N m` numerically at ratio `K = 5 / 4`
  have he1 : Real.exp 1 < (272 : ℝ) / 100 := by linarith only [Real.exp_one_lt_d9]
  have hehalf : Real.exp (1 / 2 : ℝ) < (165 : ℝ) / 100 := by
    have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith only [he1, hsq, Real.exp_pos (1 / 2 : ℝ)]
  have he32 : Real.exp (3 / 2 : ℝ) < (9 : ℝ) / 2 := by
    have hsp : Real.exp (3 / 2 : ℝ) = Real.exp 1 * Real.exp (1 / 2 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsp]
    nlinarith only [he1, hehalf, Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 2 : ℝ)]
  have he52 : Real.exp (5 / 2 : ℝ) < 13 := by
    have hsp : Real.exp (5 / 2 : ℝ) = Real.exp 1 * Real.exp (3 / 2 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsp]
    nlinarith only [he1, he32, Real.exp_pos (1 : ℝ), Real.exp_pos (3 / 2 : ℝ)]
  have hlog4 : Real.log 4 < (7 : ℝ) / 5 := by
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
    linarith only [h4, Real.log_two_lt_d9]
  have hpsi_le : psiConstant ≤ 4 := by
    unfold psiConstant
    have he_gt2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hdiv : 4 / Real.exp 1 ≤ 2 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith only [he_gt2]
    linarith only [hlog4, hdiv]
  have hNR_sum : ∑ m ∈ Icc 1 N, a m ^ 2 * nonRatioRow w N m ≤
      350 * (poleDefect N a + ∑ m ∈ Icc 1 N, a m ^ 2) := by
    have hpt : ∀ m ∈ Icc 1 N,
        a m ^ 2 * nonRatioRow w N m ≤
          a m ^ 2 * (192 + (45 / 4) * ((m : ℝ) / N * Real.log m)) := by
      intro m hm
      have hm1 := (mem_Icc.mp hm).1
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hm).2
      have hm_div : (m : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hmN
      have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
      have hrow := nonRatioRow_le_of_ratio (N := N) (K := 5 / 4) (by omega) hw0.le hw1
        (by simpa only [div_div] using hw_54) hm1
      have hc1 : 2 * (Real.log 4 + 4) * Real.exp (5 / 2) * (5 / 4 : ℝ) ≤ 180 := by
        have hpos_l : 0 ≤ Real.log 4 + 4 := by
          have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith only [this]
        nlinarith only [hlog4, he52, hpos_l, Real.exp_pos (5 / 2 : ℝ)]
      have hc2 : 2 * Real.exp (3 / 2) * (5 / 4 : ℝ) * ((m : ℝ) / N) * (Real.log m + 1) ≤
          12 + (45 / 4) * ((m : ℝ) / N * Real.log m) := by
        have hm0 : 0 ≤ (m : ℝ) / N := by positivity
        have hprod_pos : 0 ≤ ((m : ℝ) / N) * (Real.log m + 1) := by positivity
        have hstep : 2 * Real.exp (3 / 2) * (5 / 4 : ℝ) * ((m : ℝ) / N) * (Real.log m + 1) ≤
            (45 / 4) * (((m : ℝ) / N) * (Real.log m + 1)) := by
          rw [show 2 * Real.exp (3 / 2) * (5 / 4 : ℝ) * ((m : ℝ) / N) * (Real.log m + 1) =
            (2 * Real.exp (3 / 2) * (5 / 4 : ℝ)) * (((m : ℝ) / N) * (Real.log m + 1)) by ring]
          exact mul_le_mul_of_nonneg_right (by linarith only [he32]) hprod_pos
        linarith only [hstep, hm_div]
      exact mul_le_mul_of_nonneg_left (by linarith only [hrow, hc1, hc2]) (sq_nonneg _)
    have hsum1 := sum_le_sum hpt
    have htop := sum_top_le_poleDefect_param N a zero_lt_one
    rw [div_one, show (1 : ℝ) + 1 = 2 by norm_num] at htop
    have hrew : ∑ m ∈ Icc 1 N, a m ^ 2 * (192 + (45 / 4) * ((m : ℝ) / N * Real.log m)) =
        192 * (∑ m ∈ Icc 1 N, a m ^ 2) +
          (45 / 4) * ∑ m ∈ Icc 1 N, (m : ℝ) / N * Real.log m * a m ^ 2 := by
      have hterm : ∀ m ∈ Icc 1 N, a m ^ 2 * (192 + (45 / 4) * ((m : ℝ) / N * Real.log m)) =
          192 * a m ^ 2 + (45 / 4) * ((m : ℝ) / N * Real.log m * a m ^ 2) := fun _ _ => by ring
      rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum]
    rw [hrew] at hsum1
    have hpd0 := poleDefect_nonneg N a
    have hsq0 : 0 ≤ ∑ m ∈ Icc 1 N, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    nlinarith only [hsum1, htop, hpsi_le, hpd0, hsq0]
  rw [div_le_iff₀ hG]
  have hfinal := mul_le_mul_of_nonneg_left hNR_sum
    (show 0 ≤ 3 * (δ₀ + 2 / (N : ℝ)) * ∫ u, atomDilate transMetzlerProfile w u ^ 2 by positivity)
  linarith only [hsum_lag, hfinal]

/-! ### Center width-drift, adjacent archimedean overlap, and full perturbation bound -/

/-- Two-sided bound on `fullWeilCenterMatrix 1 N` in terms of `poleDefect` and `‖x‖²`. -/
theorem abs_fullWeilCenterMatrix_one_inner_le {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) x, x⟫| ≤
      2 * poleDefect N (primeHorizonExtension x) + (2 * psiConstant + 15) * ‖x‖ ^ 2 := by
  have hlow := fullWeilCenterMatrix_inner_ge (α := 1) (lam := 1) zero_le_one zero_lt_one hN x
  simp only [div_one, one_mul, show (1 : ℝ) + 1 = 2 by norm_num] at hlow
  have hsym := Matrix.isSymmetric_toEuclideanLin_iff.mpr (fullWeilCenterMatrix_isHermitian 1 N)
  have hchange := abs_symmetricForm_sub_groundProjection_le
    (Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N)) hsym
    (normalizedHorizonPoleVector_norm hN)
    (norm_fullWeilCenterMatrix_normalizedPole_le zero_le_one hN) x
  change |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) x, x⟫ -
    ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) (horizonPoleProjection x),
      horizonPoleProjection x⟫| ≤ 3 * (4 * 1) * ‖x‖ ^ 2 at hchange
  have hharm := fullWeilCenterMatrix_inner_of_harmonicSum_zero 1
    (horizonPoleProjection x) (harmonicSum_horizonPoleProjection hN x)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hcollar_abs :
      |((∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension (horizonPoleProjection x) n *
          primeHorizonExtension (horizonPoleProjection x) j *
          archimedeanCenterKernel n j) / N)| ≤
        2 * poleDefect N (primeHorizonExtension x) + (2 * psiConstant + 3) * ‖x‖ ^ 2 := by
    rw [abs_div, abs_of_pos hN0]
    have htri : |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension (horizonPoleProjection x) n *
          primeHorizonExtension (horizonPoleProjection x) j *
          archimedeanCenterKernel n j| ≤
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          |primeHorizonExtension (horizonPoleProjection x) n| *
            |primeHorizonExtension (horizonPoleProjection x) j| *
            archimedeanCenterKernel n j := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (archimedeanCenterKernel_nonneg n j)]
    have hcol := (div_le_div_of_nonneg_right htri hN0.le).trans
      (collar_quadratic_div_horizon_le hN
        (fun n => |primeHorizonExtension (horizonPoleProjection x) n|))
    have htop := sum_top_le_poleDefect_param N
      (fun n => |primeHorizonExtension (horizonPoleProjection x) n|) zero_lt_one
    rw [div_one, show (1 : ℝ) + 1 = 2 by norm_num] at htop
    have hsq_eq : ∑ n ∈ Icc 1 N, |primeHorizonExtension (horizonPoleProjection x) n| ^ 2 =
        ‖horizonPoleProjection x‖ ^ 2 := by
      simp only [sq_abs, sum_primeHorizonExtension_sq]
    rw [hsq_eq] at hcol htop
    have hpd_le : poleDefect N (fun n => |primeHorizonExtension (horizonPoleProjection x) n|) ≤
        poleDefect N (primeHorizonExtension x) :=
      (poleDefect_abs_le N _).trans_eq (poleDefect_horizonPoleProjection hN x)
    have hnorm_le := horizonPoleProjection_norm_sq_le hN x
    have hpsi0 := psiConstant_pos.le
    nlinarith only [hcol, htop, hpd_le, hnorm_le, hpsi0]
  have hup_proj : ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) (horizonPoleProjection x),
      horizonPoleProjection x⟫ ≤
      2 * poleDefect N (primeHorizonExtension x) + (2 * psiConstant + 3) * ‖x‖ ^ 2 := by
    rw [hharm, neg_one_mul]
    exact (neg_le_abs _).trans hcollar_abs
  have hup_change := (abs_le.mp hchange).2
  rw [abs_le]
  exact ⟨by linarith only [hlow], by linarith only [hup_proj, hup_change]⟩

/-- Translation reduces `levyMixed (atom g n) (atom g j)` for distinct positive integers to
`levyMixed g (fun u => g (u - |Real.log j - Real.log n|))`. -/
theorem levyMixed_atom_eq_shift {g : ℝ → ℝ} {n j : ℕ}
    (hn : 1 ≤ n) (hj : 1 ≤ j) (hnj : n ≠ j) (y : ℝ) :
    levyMixed (atom g n) (atom g j) y =
      levyMixed g (fun u => g (u - |Real.log j - Real.log n|)) y := by
  rcases lt_or_gt_of_ne hnj with hlt | hgt
  · have hpos : 0 < Real.log (j : ℝ) - Real.log (n : ℝ) :=
      sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hn) (by exact_mod_cast hlt))
    rw [abs_of_pos hpos]
    unfold levyMixed atom
    congr 1
    rw [← integral_sub_right_eq_self
      (fun u => (g u - g (u + y)) *
        (g (u - (Real.log j - Real.log n)) -
          g (u + y - (Real.log j - Real.log n)))) (Real.log n)]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring_nf)
  · have hpos : 0 < Real.log (n : ℝ) - Real.log (j : ℝ) :=
      sub_pos.mpr (Real.log_lt_log (by exact_mod_cast hj) (by exact_mod_cast hgt))
    rw [abs_sub_comm, abs_of_pos hpos]
    unfold levyMixed atom
    congr 1
    rw [← integral_sub_right_eq_self
      (fun u => (g u - g (u + y)) *
        (g (u - (Real.log n - Real.log j)) -
          g (u + y - (Real.log n - Real.log j)))) (Real.log j)]
    refine (integral_congr_ae (Eventually.of_forall fun u => ?_)).symm
    have h1 : u - Real.log j - (Real.log n - Real.log j) = u - Real.log n := by ring
    have h2 : u - Real.log j + y - (Real.log n - Real.log j) = u + y - Real.log n := by ring
    have h3 : u - Real.log j + y = u + y - Real.log j := by ring
    rw [h1, h2, h3, mul_comm]

/-- For any strictly separated pair `w < |Real.log j - Real.log n|`, the mixed Lévy integral is
minus `atomCrossTerm g |Real.log j - Real.log n|`. -/
theorem integral_levyMixed_atom_of_lt_abs_log {g : ℝ → ℝ} {w : ℝ} {n j : ℕ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hw0 : 0 ≤ w) (hws : w < |Real.log j - Real.log n|) :
    (∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g j) y) =
      -atomCrossTerm g |Real.log j - Real.log n| := by
  have hnj : n ≠ j := by
    intro h; subst h; rw [sub_self, abs_zero] at hws; linarith only [hw0, hws]
  rw [atomCrossTerm, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [levyMixed_atom_eq_shift hn hj hnj y, levyMixed_atom_shift hsupp hws hy]

/-- Bilinear expansion of `levyEnergy (atomicTest N a g)` at arbitrary width. -/
theorem levyEnergy_atomicTest_eq_sum {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ) (a : ℕ → ℝ) :
    levyEnergy (atomicTest N a g) =
      ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        a n * a j * ∫ y in Set.Ioi 0, levyMixed (atom g n) (atom g j) y := by
  have hf : ContDiff ℝ 2 (atomicTest N a g) := contDiff_atomicTest hg N a
  have hfc : HasCompactSupport (atomicTest N a g) := hasCompactSupport_atomicTest hgsupp N a
  have hda (k : ℕ) : ContDiff ℝ 2 (atom g k) := contDiff_atom hg k
  have hdca (k : ℕ) : HasCompactSupport (atom g k) := hasCompactSupport_atom hgsupp k
  have hright (d : ℝ → ℝ) (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d) :
      (∫ y in Set.Ioi 0, levyMixed d (atomicTest N a g) y) =
        ∑ j ∈ Icc 1 N, a j * ∫ y in Set.Ioi 0, levyMixed d (atom g j) y := by
    have hpt (y : ℝ) : levyMixed d (atomicTest N a g) y =
        ∑ j ∈ Icc 1 N, a j * levyMixed d (atom g j) y := by
      rw [atomicTest_eq_sum_atom]
      unfold levyMixed
      have hint_eq : (∫ u, (d u - d (u + y)) *
          ((∑ j ∈ Icc 1 N, a j * atom g j u) -
            ∑ j ∈ Icc 1 N, a j * atom g j (u + y))) =
          ∑ j ∈ Icc 1 N, a j * ∫ u, (d u - d (u + y)) * (atom g j u - atom g j (u + y)) := by
        have hcongr : (∫ u, (d u - d (u + y)) *
            ((∑ j ∈ Icc 1 N, a j * atom g j u) -
              ∑ j ∈ Icc 1 N, a j * atom g j (u + y))) =
            ∫ u, ∑ j ∈ Icc 1 N,
              a j * ((d u - d (u + y)) * (atom g j u - atom g j (u + y))) := by
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← sum_sub_distrib, mul_sum]
          exact sum_congr rfl fun j _ => by ring
        rw [hcongr, integral_finsetSum _ fun j _ =>
          (integrable_sub_shift_mul hd.continuous hdc (hda j).continuous y).const_mul (a j)]
        exact sum_congr rfl fun j _ => integral_const_mul _ _
      rw [hint_eq, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ =>
      (integrableOn_levyMixed hd hdc (hda j) (hdca j)).const_mul (a j)]
    exact sum_congr rfl fun j _ => integral_const_mul _ _
  have hsym (f₁ f₂ : ℝ → ℝ) :
      (∫ y in Set.Ioi 0, levyMixed f₁ f₂ y) = ∫ y in Set.Ioi 0, levyMixed f₂ f₁ y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    unfold levyMixed
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun u => mul_comm _ _)
  have hself : levyEnergy (atomicTest N a g) =
      ∫ y in Set.Ioi 0, levyMixed (atomicTest N a g) (atomicTest N a g) y := by
    unfold levyEnergy levyMixed
    simp only [← sq]
  rw [hself, hright (atomicTest N a g) hf hfc]
  refine sum_congr rfl fun n _ => ?_
  rw [hsym (atomicTest N a g) (atom g n), hright (atom g n) (hda n) (hdca n), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [hsym (atom g n) (atom g j)]
  ring

/-- Bound on the mixed Lévy integral of an overlapping adjacent pair at width
`1 / (2 N) ≤ w ≤ (1 + δ₀) / N`, splitting short shifts `(0, 2w]` (bounded via Lipschitz
increments) from long shifts `(2w, ∞)` (carrying the overlap-length factor `3 * δ₀`). -/
theorem abs_integral_levyMixed_adjacent_le {N n j : ℕ} {w δ₀ : ℝ}
    (hN : 16 ≤ N) (hδ0 : 0 ≤ δ₀) (hδ4 : δ₀ ≤ 1 / 4)
    (hw_lo : 1 / (2 * (N : ℝ)) ≤ w) (hw_hi : w ≤ (1 + δ₀) / (N : ℝ))
    (hn : n ∈ Icc 1 N) (hj : j ∈ Icc 1 N) (hnj : n ≠ j)
    (hlog : |Real.log j - Real.log n| ≤ w) :
    |(∫ y in Set.Ioi 0,
        levyMixed (atom (atomDilate transMetzlerProfile w) n)
          (atom (atomDilate transMetzlerProfile w) j) y) /
      (∫ u, atomDilate transMetzlerProfile w u ^ 2)| ≤
      3 * δ₀ * Real.log N + 3 * δ₀ * (selfEnergyConstant + 32000) + 64000 := by
  have hN16 : (16 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN16]
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw_lo
  have hw_54 : w ≤ 5 / (4 * (N : ℝ)) := by
    refine hw_hi.trans ?_
    rw [div_le_div_iff₀ hN0 (by positivity)]
    nlinarith only [hδ4, hN0]
  have h2w1 : 2 * w ≤ 1 := by
    have : 2 * (5 / (4 * (N : ℝ))) ≤ 1 := by
      rw [mul_div_assoc', div_le_one (by positivity)]; linarith only [hN16]
    linarith only [hw_54, this]
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : ∫ u, atomDilate transMetzlerProfile w u ^ 2 = w * ∫ u, transMetzlerProfile u ^ 2 :=
    integral_atomDilate_sq hw0
  have hM_pos : 0 < ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [hM]; exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  have hM_half : w / 2 ≤ ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [hM]
    have hφ := integral_transMetzlerProfile_sq_ge
    nlinarith only [hφ, hw0]
  have hM_3N : 1 / (3 * (N : ℝ)) ≤ ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [hM]
    have hφ := integral_transMetzlerProfile_sq_ge
    have h1 := mul_le_mul hw_lo hφ (by norm_num) hw0.le
    have h2 : (1 : ℝ) / (3 * N) ≤ 1 / (2 * N) * (499 / 500) := by
      rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith only [hN0]
    exact h2.trans h1
  have hs_ge := (top_adjacent_of_log_gap_le hN hn hj hnj hw_54 hlog).2.2.2
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hj).1
  have hshift_eq : (∫ y in Set.Ioi 0,
      levyMixed (atom (atomDilate transMetzlerProfile w) n)
        (atom (atomDilate transMetzlerProfile w) j) y) =
      ∫ y in Set.Ioi 0,
        levyMixed (atomDilate transMetzlerProfile w)
          (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y :=
    setIntegral_congr_fun measurableSet_Ioi fun y _ => levyMixed_atom_eq_shift hn1 hj1 hnj y
  rw [hshift_eq, abs_div, abs_of_pos hM_pos]
  have hgs_cd : ContDiff ℝ 2
      (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) :=
    hg.comp (contDiff_id.sub contDiff_const)
  have hgs_cs : HasCompactSupport
      (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) :=
    hgc.comp_homeomorph (Homeomorph.subRight _)
  have hint_all : IntegrableOn
      (levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|))) (Set.Ioi 0) :=
    integrableOn_levyMixed hg hgc hgs_cd hgs_cs
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 (2 * w) ∪ Set.Ioi (2 * w) :=
    (Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 2 * w)).symm
  have hint_short : IntegrableOn
      (levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)))
      (Set.Ioc 0 (2 * w)) :=
    hint_all.mono_set fun y hy => hy.1
  have hint_long : IntegrableOn
      (levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)))
      (Set.Ioi (2 * w)) :=
    hint_all.mono_set fun y hy => lt_trans (by positivity : (0 : ℝ) < 2 * w) hy
  rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_short hint_long]
  -- Short shifts `(0, 2w]`: Cauchy-Schwarz + Lipschitz increments
  have hLip : ∀ u v, |atomDilate transMetzlerProfile w u - atomDilate transMetzlerProfile w v| ≤
      (8000 / w) * |u - v| := by
    intro u v
    have h := abs_transMetzlerProfile_sub_le (u / w) (v / w)
    rw [show u / w - v / w = (u - v) / w by ring, abs_div, abs_of_pos hw0] at h
    calc |atomDilate transMetzlerProfile w u - atomDilate transMetzlerProfile w v|
        ≤ 8000 * (|u - v| / w) := h
      _ = (8000 / w) * |u - v| := by ring
  have hshort_pt : ∀ y ∈ Set.Ioc 0 (2 * w),
      |levyMixed (atomDilate transMetzlerProfile w)
          (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y| ≤
        16000 := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hω0 : 0 ≤ archLevyDensity y := (archLevyDensity_pos hy0).le
    have hsq1 : Integrable fun u =>
        (atomDilate transMetzlerProfile w u - atomDilate transMetzlerProfile w (u + y)) ^ 2 :=
      WeilMarkovPole.integrable_sub_shift_sq hg.continuous hgc y
    have hsq2 : Integrable fun u =>
        (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
          atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) ^ 2 := by
      have h := hsq1.comp_sub_right |Real.log j - Real.log n|
      refine h.congr (Eventually.of_forall fun u => ?_)
      dsimp only [Function.comp_apply]
      rw [show u - |Real.log j - Real.log n| + y = u + y - |Real.log j - Real.log n| by ring]
    have hcs_u : |∫ u, (atomDilate transMetzlerProfile w u -
          atomDilate transMetzlerProfile w (u + y)) *
        (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
          atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|))| ≤
        ∫ u, (atomDilate transMetzlerProfile w u -
          atomDilate transMetzlerProfile w (u + y)) ^ 2 := by
      have hint_prod := integrable_sub_shift_mul hg.continuous hgc hgs_cd.continuous y
      calc |∫ u, _| ≤ ∫ u, |(atomDilate transMetzlerProfile w u -
              atomDilate transMetzlerProfile w (u + y)) *
            (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|))| :=
            abs_integral_le_integral_abs
        _ ≤ ∫ u, ((1 / 2 : ℝ) * (atomDilate transMetzlerProfile w u -
              atomDilate transMetzlerProfile w (u + y)) ^ 2 +
            (1 / 2 : ℝ) * (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) ^ 2) := by
          refine integral_mono hint_prod.abs ((hsq1.const_mul _).add (hsq2.const_mul _)) fun u => ?_
          rw [abs_mul]
          have hsq_sum := sq_nonneg (|atomDilate transMetzlerProfile w u -
              atomDilate transMetzlerProfile w (u + y)| -
            |atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)|)
          nlinarith only [hsq_sum, sq_abs (atomDilate transMetzlerProfile w u -
              atomDilate transMetzlerProfile w (u + y)),
            sq_abs (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|))]
        _ = ∫ u, (atomDilate transMetzlerProfile w u -
              atomDilate transMetzlerProfile w (u + y)) ^ 2 := by
          rw [integral_add (hsq1.const_mul _) (hsq2.const_mul _),
            integral_const_mul, integral_const_mul]
          have htr : (∫ u, (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) ^ 2) =
              ∫ u, (atomDilate transMetzlerProfile w u -
                atomDilate transMetzlerProfile w (u + y)) ^ 2 := by
            rw [← integral_sub_right_eq_self
              (fun u => (atomDilate transMetzlerProfile w u -
                atomDilate transMetzlerProfile w (u + y)) ^ 2) |Real.log j - Real.log n|]
            exact integral_congr_ae (Eventually.of_forall fun u => by
              simp only [show u - |Real.log j - Real.log n| + y =
                u + y - |Real.log j - Real.log n| by ring])
          rw [htr]; ring
    have hinc := integral_sub_shift_sq_le_lipschitz hg.continuous hgc hLip y
    rw [abs_of_pos hy0, integral_abs_atomDilate hw0] at hinc
    have hI1 : (∫ u, |transMetzlerProfile u|) ≤ 1 := integral_abs_plateau_le etaZero_pos
    have hd := archLevyDensity_le_sqrt_e_div hy0 (hy.2.trans h2w1)
    have he2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have he1 := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith only [he1, hsq, Real.exp_pos (1 / 2 : ℝ)]
    unfold levyMixed
    rw [abs_mul, abs_of_nonneg hω0]
    calc archLevyDensity y * |∫ u, _|
        ≤ (Real.exp (1 / 2) / (2 * y)) * (2 * (8000 / w) * y * (w * ∫ u, |transMetzlerProfile u|)) :=
          mul_le_mul hd (hcs_u.trans hinc) (abs_nonneg _) (by positivity)
      _ = Real.exp (1 / 2) * 8000 * ∫ u, |transMetzlerProfile u| := by
          field_simp [hy0.ne', hw0.ne']
      _ ≤ (2 * 8000) * 1 := by
          have hI0 : 0 ≤ ∫ u, |transMetzlerProfile u| := integral_nonneg fun _ => abs_nonneg _
          exact mul_le_mul (by linarith only [he2]) hI1 hI0 (by norm_num)
      _ = 16000 := by norm_num
  have hshort_int : |∫ y in Set.Ioc 0 (2 * w),
      levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y| ≤
      32000 * w := by
    calc |∫ y in Set.Ioc 0 (2 * w), _|
        ≤ ∫ y in Set.Ioc 0 (2 * w), |levyMixed (atomDilate transMetzlerProfile w)
            (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _ in Set.Ioc 0 (2 * w), (16000 : ℝ) :=
          setIntegral_mono_on hint_short.abs
            (integrableOn_const (by simp))
            measurableSet_Ioc hshort_pt
      _ = 32000 * w := by
          rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le (by positivity)]
          ring
  have hshort_div : |∫ y in Set.Ioc 0 (2 * w),
      levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y| /
      (∫ u, atomDilate transMetzlerProfile w u ^ 2) ≤ 64000 := by
    rw [div_le_iff₀ hM_pos]
    linarith only [hshort_int, hM_half]
  -- Long shifts `(2w, ∞)`: cross-shift products vanish, leaving `2 * archLevyDensity y * bumpCorr`
  have hlong_pt : ∀ y ∈ Set.Ioi (2 * w),
      levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y =
      2 * SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
        |Real.log j - Real.log n| * archLevyDensity y := by
    intro y hy
    have hy2w : 2 * w < y := hy
    have hint_g1 : Integrable fun u =>
        atomDilate transMetzlerProfile w u *
          atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) :=
      integrable_mul_shift hg.continuous hgc hgs_cd.continuous 0 |>.congr
        (Eventually.of_forall fun u => by simp only [add_zero])
    have hint_g2 : Integrable fun u =>
        atomDilate transMetzlerProfile w (u + y) *
          atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|) := by
      have h := hint_g1.comp_add_right y
      exact h.congr (Eventually.of_forall fun u => rfl)
    have hpt_u : ∀ u,
        (atomDilate transMetzlerProfile w u - atomDilate transMetzlerProfile w (u + y)) *
          (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
            atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) =
        atomDilate transMetzlerProfile w u *
            atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) +
          atomDilate transMetzlerProfile w (u + y) *
            atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|) := by
      intro u
      have hz1 : atomDilate transMetzlerProfile w u *
          atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|) = 0 := by
        by_cases hu : u ∈ Set.Icc 0 w
        · rw [hgsupp (u + y - |Real.log j - Real.log n|)
            (fun h => by linarith only [hu.1, h.2, hy2w, hlog]), mul_zero]
        · rw [hgsupp u hu, zero_mul]
      have hz2 : atomDilate transMetzlerProfile w (u + y) *
          atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) = 0 := by
        by_cases hu : u + y ∈ Set.Icc 0 w
        · rw [hgsupp (u - |Real.log j - Real.log n|)
            (fun h => by linarith only [hu.2, h.1, hy2w, hw0, abs_nonneg (Real.log j - Real.log n)]),
            mul_zero]
        · rw [hgsupp (u + y) hu, zero_mul]
      have hexp : (atomDilate transMetzlerProfile w u -
            atomDilate transMetzlerProfile w (u + y)) *
          (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
            atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) =
          atomDilate transMetzlerProfile w u *
              atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
            atomDilate transMetzlerProfile w u *
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|) -
            atomDilate transMetzlerProfile w (u + y) *
              atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) +
            atomDilate transMetzlerProfile w (u + y) *
              atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|) := by ring
      rw [hexp, hz1, hz2]; ring
    have hint_eq : (∫ u,
        (atomDilate transMetzlerProfile w u - atomDilate transMetzlerProfile w (u + y)) *
          (atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) -
            atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|))) =
        2 * SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
          |Real.log j - Real.log n| := by
      simp_rw [hpt_u]
      rw [integral_add hint_g1 hint_g2]
      have htr : (∫ u, atomDilate transMetzlerProfile w (u + y) *
          atomDilate transMetzlerProfile w (u + y - |Real.log j - Real.log n|)) =
          ∫ u, atomDilate transMetzlerProfile w u *
            atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|) :=
        integral_add_right_eq_self
          (fun u => atomDilate transMetzlerProfile w u *
            atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y
      have hcorr : (∫ u, atomDilate transMetzlerProfile w u *
          atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) =
          SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
            |Real.log j - Real.log n| := by
        rw [← bumpCorr_neg]
        unfold SpacingScaleHarmonicAnalysis.bumpCorr
        exact integral_congr_ae (Eventually.of_forall fun u => by
          simp only [sub_eq_add_neg])
      rw [htr, hcorr]; ring
    unfold levyMixed
    rw [hint_eq]; ring
  -- Bound `2 * ∫_{Ioi (2w)} archLevyDensity` via `levyEnergy_atom_le` on `atomDilate φ₀ (2w)`
  have h2w_pos : 0 < 2 * w := by positivity
  obtain ⟨hg2, hgsupp2, hgc2⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) h2w_pos
  have hM2_pos : 0 < ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2 := by
    rw [integral_atomDilate_sq h2w_pos]; exact mul_pos h2w_pos integral_transMetzlerProfile_sq_pos
  have hLip2 : ∀ u v,
      |atomDilate transMetzlerProfile (2 * w) u - atomDilate transMetzlerProfile (2 * w) v| ≤
        (8000 / (2 * w)) * |u - v| := by
    intro u v
    have h := abs_transMetzlerProfile_sub_le (u / (2 * w)) (v / (2 * w))
    rw [show u / (2 * w) - v / (2 * w) = (u - v) / (2 * w) by ring, abs_div,
      abs_of_pos h2w_pos] at h
    calc |atomDilate transMetzlerProfile (2 * w) u - atomDilate transMetzlerProfile (2 * w) v|
        ≤ 8000 * (|u - v| / (2 * w)) := h
      _ = (8000 / (2 * w)) * |u - v| := by ring
  have htail_density : 2 * (∫ y in Set.Ioi (2 * w), archLevyDensity y) ≤
      Real.log N + selfEnergyConstant + 32000 := by
    have hL2_int : IntegrableOn
        (fun y => archLevyDensity y *
          ∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2) (Set.Ioi 0) :=
      integrableOn_levyIntegrand hg2 hgc2
    have hL2_short : IntegrableOn
        (fun y => archLevyDensity y *
          ∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2) (Set.Ioc 0 (2 * w)) :=
      hL2_int.mono_set fun y hy => hy.1
    have hL2_long : IntegrableOn
        (fun y => archLevyDensity y *
          ∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2) (Set.Ioi (2 * w)) :=
      hL2_int.mono_set fun y hy => lt_trans h2w_pos hy
    have hfar2 : ∀ y ∈ Set.Ioi (2 * w),
        archLevyDensity y *
          (∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2) =
          (2 * ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2) * archLevyDensity y := by
      intro y hy
      rw [ArithmeticElectrostatics.integral_sq_sub_shift_of_disjoint hg2.continuous hgc2
        (bump_mul_shift_eq_zero hgsupp2 hy)]
      ring
    have hshort_nonneg : 0 ≤ ∫ y in Set.Ioc 0 (2 * w),
        archLevyDensity y *
          ∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun y hy =>
        mul_nonneg (archLevyDensity_pos hy.1).le (integral_sub_shift_sq_nonneg y)
    have hlong_eq : (∫ y in Set.Ioi (2 * w),
        archLevyDensity y *
          ∫ u, (atomDilate transMetzlerProfile (2 * w) u -
            atomDilate transMetzlerProfile (2 * w) (u + y)) ^ 2) =
        (2 * ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2) *
          ∫ y in Set.Ioi (2 * w), archLevyDensity y := by
      rw [setIntegral_congr_fun measurableSet_Ioi hfar2, integral_const_mul]
    have hlevy_ge : (2 * ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2) *
          (∫ y in Set.Ioi (2 * w), archLevyDensity y) ≤
        levyEnergy (atomDilate transMetzlerProfile (2 * w)) := by
      unfold levyEnergy
      rw [hsplit, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hL2_short hL2_long,
        hlong_eq]
      linarith only [hshort_nonneg]
    have hlevy_le := levyEnergy_atom_le hg2 hgc2 hgsupp2 h2w_pos h2w1 (by positivity) hLip2
    have hM2_ge : w ≤ ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2 := by
      rw [integral_atomDilate_sq h2w_pos]
      have hφ := integral_transMetzlerProfile_sq_ge
      nlinarith only [hφ, hw0]
    have hA2_le : (∫ u, |atomDilate transMetzlerProfile (2 * w) u|) ≤ 2 * w := by
      rw [integral_abs_atomDilate h2w_pos]
      have hI1 : (∫ u, |transMetzlerProfile u|) ≤ 1 := integral_abs_plateau_le etaZero_pos
      nlinarith only [hI1, hw0]
    have he2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have he1 := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith only [he1, hsq, Real.exp_pos (1 / 2 : ℝ)]
    have herr2 : Real.exp (1 / 2) * (8000 / (2 * w)) * (2 * w) *
        (∫ u, |atomDilate transMetzlerProfile (2 * w) u|) ≤
        32000 * ∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2 := by
      have hsimp : Real.exp (1 / 2) * (8000 / (2 * w)) * (2 * w) = Real.exp (1 / 2) * 8000 := by
        field_simp [h2w_pos.ne']
      rw [hsimp]
      have hA2_0 : 0 ≤ ∫ u, |atomDilate transMetzlerProfile (2 * w) u| :=
        integral_nonneg fun _ => abs_nonneg _
      nlinarith only [he2, hA2_le, hA2_0, hM2_ge, Real.exp_pos (1 / 2 : ℝ)]
    have hlog2w : Real.log (1 / (2 * w)) ≤ Real.log N := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ h2w_pos]
      have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mp hw_lo
      linarith only [h]
    have hcomb : (2 * (∫ y in Set.Ioi (2 * w), archLevyDensity y)) *
        (∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2) ≤
        (Real.log N + selfEnergyConstant + 32000) *
          (∫ u, atomDilate transMetzlerProfile (2 * w) u ^ 2) := by
      have hlog_mul := mul_le_mul_of_nonneg_right hlog2w hM2_pos.le
      nlinarith only [hlevy_ge, hlevy_le, herr2, hlog_mul]
    exact le_of_mul_le_mul_right hcomb hM2_pos
  have hlong_eq : (∫ y in Set.Ioi (2 * w),
      levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y) =
      SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
        |Real.log j - Real.log n| * (2 * ∫ y in Set.Ioi (2 * w), archLevyDensity y) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hlong_pt, integral_const_mul]
    ring
  have hcorr_le : |(SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
        |Real.log j - Real.log n|)| /
      (∫ u, atomDilate transMetzlerProfile w u ^ 2) ≤ 3 * δ₀ := by
    have hover : |(SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
        |Real.log j - Real.log n|)| ≤ w - |Real.log j - Real.log n| := by
      change |(bumpAutocorr (atomDilate transMetzlerProfile w) |Real.log j - Real.log n|)| ≤ _
      have hb := abs_bumpAutocorr_le_overlap_length hg.continuous hgsupp zero_le_one
        (fun u => by
          rw [atomDilate, abs_of_nonneg (transMetzlerProfile_nonneg _)]
          exact transMetzlerProfile_le_one _)
        (by rwa [abs_of_nonneg (abs_nonneg _)])
      rw [one_pow, one_mul, abs_of_nonneg (abs_nonneg _)] at hb
      exact hb
    have hw_sub : w - |Real.log j - Real.log n| ≤ δ₀ / (N : ℝ) := by
      have hsub := sub_le_sub hw_hi hs_ge
      have hring : (1 + δ₀) / (N : ℝ) - 1 / (N : ℝ) = δ₀ / (N : ℝ) := by ring
      rwa [hring] at hsub
    rw [div_le_iff₀ hM_pos]
    have h3 := mul_le_mul_of_nonneg_left hM_3N (show 0 ≤ 3 * δ₀ by positivity)
    have hsimp : 3 * δ₀ * (1 / (3 * (N : ℝ))) = δ₀ / (N : ℝ) := by field_simp [hN0.ne']
    rw [hsimp] at h3
    exact hover.trans (hw_sub.trans h3)
  have htail_nonneg : 0 ≤ 2 * ∫ y in Set.Ioi (2 * w), archLevyDensity y :=
    mul_nonneg (by norm_num)
      (setIntegral_nonneg measurableSet_Ioi fun y hy =>
        (archLevyDensity_pos (lt_trans h2w_pos hy)).le)
  have hlong_div : |(∫ y in Set.Ioi (2 * w),
      levyMixed (atomDilate transMetzlerProfile w)
        (fun u => atomDilate transMetzlerProfile w (u - |Real.log j - Real.log n|)) y)| /
      (∫ u, atomDilate transMetzlerProfile w u ^ 2) ≤
      3 * δ₀ * (Real.log N + selfEnergyConstant + 32000) := by
    rw [hlong_eq, abs_mul, abs_of_nonneg htail_nonneg, mul_div_right_comm]
    exact mul_le_mul hcorr_le htail_density htail_nonneg (by positivity)
  calc |(∫ y in Set.Ioc 0 (2 * w), _) + (∫ y in Set.Ioi (2 * w), _)| /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2)
      ≤ (|∫ y in Set.Ioc 0 (2 * w), _| + |∫ y in Set.Ioi (2 * w), _|) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) :=
        div_le_div_of_nonneg_right (abs_add_le _ _) hM_pos.le
    _ = |∫ y in Set.Ioc 0 (2 * w), _| / (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
          |∫ y in Set.Ioi (2 * w), _| / (∫ u, atomDilate transMetzlerProfile w u ^ 2) :=
        add_div _ _ _
    _ ≤ 64000 + 3 * δ₀ * (Real.log N + selfEnergyConstant + 32000) :=
        add_le_add hshort_div hlong_div
    _ = _ := by ring

/-- Exact entry formula for `normalizedFullWeilHorizonMatrix` at arbitrary atom width. -/
theorem normalizedFullWeilHorizonMatrix_apply_unconditional
    {g : ℝ → ℝ} (_hG : (∫ u, g u ^ 2) ≠ 0) (N : ℕ) (n j : PrimeHorizonIndex N) :
    normalizedFullWeilHorizonMatrix g N n j =
      markovPair (atom g n) (atom g j) / (∫ u, g u ^ 2) +
      ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) /
        (∫ u, g u ^ 2)) * arithmeticPoleKernel n j := by
  rw [normalizedFullWeilHorizonMatrix, fullWeilHorizonMatrix, atomicWeilGram, atomicMarkovGram]
  simp only [Matrix.of_apply, primeHorizonFinEquiv_val_add_one,
    atomPoleRow_primeHorizonFinEquiv_zero, atomPoleRow_primeHorizonFinEquiv_one,
    arithmeticPoleKernel]
  ring

/-- Complete quadratic-form perturbation bound between `normalizedFullWeilHorizonMatrix` and
`transMetzlerMainMatrix` past the touching ratio: every error is controlled by
`(2000 * δ₀ + C_short / log(N / 3)) * (poleDefect N a + ‖x‖²)`. -/
theorem exists_perturbation_bound_transMetzler :
    ∃ C_short : ℝ, 0 ≤ C_short ∧
      ∀ {N : ℕ} (_hN : 27 ≤ N) {w cStar δ₀ : ℝ}
        (_hδ0 : 0 ≤ δ₀) (_hδ4 : δ₀ ≤ 1 / 4) (_hcStar : 1 / 2 ≤ cStar)
        (_hw_lo : 1 / (2 * (N : ℝ)) ≤ w) (_hw_hi : w ≤ (1 + δ₀) / (N : ℝ))
        (_hdrift : |w * (N : ℝ) - cStar| ≤ 2 / (N : ℝ))
        (x : EuclideanSpace ℝ (PrimeHorizonIndex N)),
        |⟪Matrix.toEuclideanLin
            (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N) x, x⟫ -
          ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix w cStar N) x, x⟫| ≤
          (2000 * δ₀ + C_short / Real.log ((N : ℝ) / 3)) *
            (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
  have hsec_nonneg : 0 ≤ selfEnergyConstant := by
    unfold selfEnergyConstant
    have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hden : 0 < 1 - Real.exp (-2 : ℝ) := by linarith only [h2]
    positivity
  refine ⟨2156 + 96 * |gammaHardyPhaseRate 0| + 48 * (selfEnergyConstant + 96001),
    by positivity, ?_⟩
  intro N hN w cStar δ₀ hδ0 hδ4 hcStar hw_lo hw_hi hdrift x
  have hN16 : 16 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hN27 : (27 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith only [hN27]
  have hN3_gt : 1 < (N : ℝ) / 3 := by linarith only [hN27]
  have hlogN3_pos : 0 < Real.log ((N : ℝ) / 3) := Real.log_pos hN3_gt
  have hlogN3_le_N : Real.log ((N : ℝ) / 3) ≤ N :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith only [hN27])
  have hinvN_le_log : 1 / (N : ℝ) ≤ 1 / Real.log ((N : ℝ) / 3) :=
    one_div_le_one_div_of_le hlogN3_pos hlogN3_le_N
  have hlogN_le_two : Real.log (N : ℝ) ≤ 2 * Real.log ((N : ℝ) / 3) := by
    have hsq : (N : ℝ) ≤ ((N : ℝ) / 3) ^ (2 : ℕ) := by nlinarith only [hN27]
    have hl := Real.log_le_log hN0 hsq
    rw [Real.log_pow] at hl
    norm_num at hl
    exact hl
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw_lo
  have hw_54 : w ≤ 5 / (4 * (N : ℝ)) := by
    refine hw_hi.trans ?_
    rw [div_le_div_iff₀ hN0 (by positivity)]
    nlinarith only [hδ4, hN0]
  have hw1 : w ≤ 1 := by
    refine hw_54.trans ?_
    rw [div_le_one (by positivity)]; linarith only [hN27]
  obtain ⟨hg, hgsupp, hgc⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw0
  have hM : ∫ u, atomDilate transMetzlerProfile w u ^ 2 = w * ∫ u, transMetzlerProfile u ^ 2 :=
    integral_atomDilate_sq hw0
  have hM_pos : 0 < ∫ u, atomDilate transMetzlerProfile w u ^ 2 := by
    rw [hM]; exact mul_pos hw0 integral_transMetzlerProfile_sq_pos
  have hcharge_w : (∫ u, atomDilate transMetzlerProfile w u) ^ 2 /
      (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
      w * completeWeilPoleShift transMetzlerProfile 1 := by
    have hint : (∫ u, atomDilate transMetzlerProfile w u) = w * ∫ u, transMetzlerProfile u := by
      simpa only [atomDilate, smul_eq_mul, abs_of_pos hw0] using
        MeasureTheory.Measure.integral_comp_div transMetzlerProfile w
    rw [hint, hM, completeWeilPoleShift]
    field_simp [hw0.ne', integral_transMetzlerProfile_sq_pos.ne']
  -- Step 1: Expand `<W_N x, x>` into Markov + pole forms
  have hW_mat : normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N =
      horizonKernelMatrix (fun n j =>
        markovPair (atom (atomDilate transMetzlerProfile w) n)
          (atom (atomDilate transMetzlerProfile w) j) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
        ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
          (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2)) * arithmeticPoleKernel n j) N := by
    ext n j
    exact normalizedFullWeilHorizonMatrix_apply_unconditional hM_pos.ne' N n j
  have hW_inner : ⟪Matrix.toEuclideanLin
      (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N) x, x⟫ =
      (2 * gammaHardyPhaseRate 0 *
          (∫ u, atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w) u ^ 2) +
        levyEnergy (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w)) -
        primeSum (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w))) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
      ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
        (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension x n * primeHorizonExtension x j * arithmeticPoleKernel n j := by
    rw [hW_mat, horizonKernelMatrix_inner]
    have hdist (n j : ℕ) :
        primeHorizonExtension x n * primeHorizonExtension x j *
          (markovPair (atom (atomDilate transMetzlerProfile w) n)
            (atom (atomDilate transMetzlerProfile w) j) /
              (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
          ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
            (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2)) * arithmeticPoleKernel n j) =
        (primeHorizonExtension x n * primeHorizonExtension x j *
          markovPair (atom (atomDilate transMetzlerProfile w) n)
            (atom (atomDilate transMetzlerProfile w) j)) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
        ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
          (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
          (primeHorizonExtension x n * primeHorizonExtension x j * arithmeticPoleKernel n j) := by
      ring
    simp only [hdist, sum_add_distrib, ← sum_div, ← mul_sum]
    rw [← levyMarkovForm_atomicTest_eq hg hgsupp hw0.le N (primeHorizonExtension x)]
    rfl
  -- Step 2: Expand each Markov piece into diagonal + separated + overlapping parts
  have hgram_split :
      (∫ u, atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w) u ^ 2) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
        ‖x‖ ^ 2 +
          ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
            primeHorizonExtension x n * primeHorizonExtension x j *
              (if n = j then 0
                else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
                  (-(Real.log j - Real.log n)) /
                    (∫ u, atomDilate transMetzlerProfile w u ^ 2)) := by
    rw [integral_atomicTest_sq_eq_gram hg.continuous hgc N (primeHorizonExtension x), sum_div]
    have hdiag (n : ℕ) (hn : n ∈ Icc 1 N) :
        (∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
          SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
            (-(Real.log j - Real.log n))) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
          primeHorizonExtension x n ^ 2 +
            ∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
              (if n = j then 0
                else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
                  (-(Real.log j - Real.log n)) /
                    (∫ u, atomDilate transMetzlerProfile w u ^ 2)) := by
      rw [sum_eq_diag_add hn, sub_self, neg_zero, bumpCorr_zero]
      have h1 : primeHorizonExtension x n * primeHorizonExtension x n *
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
          primeHorizonExtension x n ^ 2 * (∫ u, atomDilate transMetzlerProfile w u ^ 2) := by ring
      rw [h1, add_div, mul_div_cancel_right₀ _ hM_pos.ne', sum_div]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    rw [sum_congr rfl hdiag, sum_add_distrib, sum_primeHorizonExtension_sq]
  have hlevy_split :
      levyEnergy (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
        (levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2)) * ‖x‖ ^ 2 -
          ⟪Matrix.toEuclideanLin
            (horizonKernelMatrix
              (separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w) N) x, x⟫ -
          (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
            primeHorizonExtension x n * primeHorizonExtension x j *
              (w * completeWeilPoleShift transMetzlerProfile 1 * archimedeanCenterKernel n j)) +
          ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
            primeHorizonExtension x n * primeHorizonExtension x j *
              (if n = j ∨ w < |Real.log j - Real.log n| then 0
                else (∫ y in Set.Ioi 0,
                  levyMixed (atom (atomDilate transMetzlerProfile w) n)
                    (atom (atomDilate transMetzlerProfile w) j) y) /
                  (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
                  w * completeWeilPoleShift transMetzlerProfile 1 *
                    archimedeanCenterKernel n j) := by
    rw [levyEnergy_atomicTest_eq_sum hg hgsupp N (primeHorizonExtension x),
      horizonKernelMatrix_inner, sum_div]
    have hrow (n : ℕ) (hn : n ∈ Icc 1 N) :
        (∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
          ∫ y in Set.Ioi 0, levyMixed (atom (atomDilate transMetzlerProfile w) n)
            (atom (atomDilate transMetzlerProfile w) j) y) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
        (levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2)) * primeHorizonExtension x n ^ 2 -
          (∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
            separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w n j) -
          (∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
            (w * completeWeilPoleShift transMetzlerProfile 1 * archimedeanCenterKernel n j)) +
          ∑ j ∈ Icc 1 N, primeHorizonExtension x n * primeHorizonExtension x j *
            (if n = j ∨ w < |Real.log j - Real.log n| then 0
              else (∫ y in Set.Ioi 0,
                levyMixed (atom (atomDilate transMetzlerProfile w) n)
                  (atom (atomDilate transMetzlerProfile w) j) y) /
                (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
                w * completeWeilPoleShift transMetzlerProfile 1 *
                  archimedeanCenterKernel n j) := by
      rw [sum_div]
      have hterm (j : ℕ) (hj : j ∈ Icc 1 N) :
          (primeHorizonExtension x n * primeHorizonExtension x j *
              ∫ y in Set.Ioi 0, levyMixed (atom (atomDilate transMetzlerProfile w) n)
                (atom (atomDilate transMetzlerProfile w) j) y) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
          (if n = j then (levyEnergy (atomDilate transMetzlerProfile w) /
              (∫ u, atomDilate transMetzlerProfile w u ^ 2)) * primeHorizonExtension x n ^ 2 else 0) -
            primeHorizonExtension x n * primeHorizonExtension x j *
              separatedCrossErrorKernel (atomDilate transMetzlerProfile w) w n j -
            primeHorizonExtension x n * primeHorizonExtension x j *
              (w * completeWeilPoleShift transMetzlerProfile 1 * archimedeanCenterKernel n j) +
            primeHorizonExtension x n * primeHorizonExtension x j *
              (if n = j ∨ w < |Real.log j - Real.log n| then 0
                else (∫ y in Set.Ioi 0,
                  levyMixed (atom (atomDilate transMetzlerProfile w) n)
                    (atom (atomDilate transMetzlerProfile w) j) y) /
                  (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
                  w * completeWeilPoleShift transMetzlerProfile 1 *
                    archimedeanCenterKernel n j) := by
        by_cases hnj : n = j
        · subst j
          have hself : (∫ y in Set.Ioi 0,
              levyMixed (atom (atomDilate transMetzlerProfile w) n)
                (atom (atomDilate transMetzlerProfile w) n) y) =
              levyEnergy (atomDilate transMetzlerProfile w) := by
            simp only [levyMixed, ← sq]
            exact levyEnergy_translate (Real.log n)
          have hnw : ¬(w < |Real.log (n : ℝ) - Real.log n|) := by
            rw [sub_self, abs_zero]; exact not_lt.mpr hw0.le
          rw [hself, if_pos rfl, if_pos (Or.inl rfl), separatedCrossErrorKernel, if_neg hnw,
            archimedeanCenterKernel_self]
          ring
        · rw [if_neg hnj]
          by_cases hws : w < |Real.log j - Real.log n|
          · rw [if_pos (Or.inr hws), separatedCrossErrorKernel, if_pos hws,
              integral_levyMixed_atom_of_lt_abs_log hgsupp (mem_Icc.mp hn).1 (mem_Icc.mp hj).1
                hw0.le hws, atomCrossErrorKernel, if_neg hnj, hcharge_w]
            ring
          · rw [if_neg (fun h => h.elim hnj hws), separatedCrossErrorKernel, if_neg hws]
            ring
      rw [sum_congr rfl hterm, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
        sum_ite_eq, if_pos hn]
    rw [sum_congr rfl hrow, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
      ← mul_sum, sum_primeHorizonExtension_sq]
  have hprime_split :
      primeSum (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) =
        ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫ +
          nonRatioForm (atomDilate transMetzlerProfile w) N (primeHorizonExtension x) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) := by
    rw [primeSum_atomicTest_eq_ratio_add hg.continuous hgc hgsupp hw0.le N
        (primeHorizonExtension x),
      add_div, mul_div_cancel_left₀ _ hM_pos.ne', atomicWeilForm_primeHorizonExtension]
  have hpole_split :
      ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
        (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
        (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension x n * primeHorizonExtension x j * arithmeticPoleKernel n j) -
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension x n * primeHorizonExtension x j *
          (w * completeWeilPoleShift transMetzlerProfile 1 * archimedeanCenterKernel n j)) =
      ⟪Matrix.toEuclideanLin (poleMomentErrorMatrix transMetzlerProfile w N) x, x⟫ +
        ⟪Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift transMetzlerProfile cStar) N) x, x⟫ +
        ((w * N - cStar) * completeWeilPoleShift transMetzlerProfile 1) *
          ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) x, x⟫ := by
    have hexp_neg : atomExponentialMoment (atomDilate transMetzlerProfile w) (-(1 / 2)) =
        ∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2)) := by
      unfold atomExponentialMoment; congr 1; funext u; congr 2; ring
    have hexp_pos : atomExponentialMoment (atomDilate transMetzlerProfile w) (1 / 2) =
        ∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2) := by
      unfold atomExponentialMoment; congr 1; funext u; congr 2; ring
    have hcoeff : ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
        (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2)) =
        poleMomentErrorCoeff transMetzlerProfile w +
          w * completeWeilPoleShift transMetzlerProfile 1 := by
      unfold poleMomentErrorCoeff; rw [hexp_neg, hexp_pos]; ring
    have hshift_cStar : completeWeilPoleShift transMetzlerProfile cStar =
        cStar * completeWeilPoleShift transMetzlerProfile 1 := by
      unfold completeWeilPoleShift; ring
    change _ =
      ⟪Matrix.toEuclideanLin (horizonKernelMatrix
        (fun n j => poleMomentErrorCoeff transMetzlerProfile w * arithmeticPoleKernel n j) N) x, x⟫ +
      ⟪Matrix.toEuclideanLin (horizonKernelMatrix
        (fun n j => (completeWeilPoleShift transMetzlerProfile cStar / N) *
          (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N) x, x⟫ +
      ((w * N - cStar) * completeWeilPoleShift transMetzlerProfile 1) *
        ⟪Matrix.toEuclideanLin (horizonKernelMatrix
          (fun n j => (1 / (N : ℝ)) *
            (arithmeticPoleKernel n j - archimedeanCenterKernel n j)) N) x, x⟫
    rw [hcoeff, hshift_cStar, horizonKernelMatrix_inner, horizonKernelMatrix_inner,
      horizonKernelMatrix_inner]
    simp only [mul_sum]
    rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [← sum_sub_distrib, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    field_simp [hN0.ne']
    ring
  -- Step 3: Exact difference `<W_N x, x> - <H_N^main x, x>`
  have hdiff_eq :
      ⟪Matrix.toEuclideanLin
          (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N) x, x⟫ -
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix w cStar N) x, x⟫ =
      (2 * gammaHardyPhaseRate 0 +
          levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
          Real.log N -
          (completeWeilSelfFinitePart transMetzlerProfile cStar -
            Real.eulerMascheroniConstant)) * ‖x‖ ^ 2 +
      2 * gammaHardyPhaseRate 0 *
        (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          primeHorizonExtension x n * primeHorizonExtension x j *
            (if n = j then 0
              else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
                (-(Real.log j - Real.log n)) /
                  (∫ u, atomDilate transMetzlerProfile w u ^ 2))) +
      ((w * N - cStar) * completeWeilPoleShift transMetzlerProfile 1) *
        ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) x, x⟫ -
      nonRatioForm (atomDilate transMetzlerProfile w) N (primeHorizonExtension x) /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension x n * primeHorizonExtension x j *
          (if n = j ∨ w < |Real.log j - Real.log n| then 0
            else (∫ y in Set.Ioi 0,
              levyMixed (atom (atomDilate transMetzlerProfile w) n)
                (atom (atomDilate transMetzlerProfile w) j) y) /
              (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
              w * completeWeilPoleShift transMetzlerProfile 1 *
                archimedeanCenterKernel n j)) := by
    have hW2 : ⟪Matrix.toEuclideanLin
        (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N) x, x⟫ =
        2 * gammaHardyPhaseRate 0 *
          ((∫ u, atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w) u ^ 2) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2)) +
        levyEnergy (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
        primeSum (atomicTest N (primeHorizonExtension x) (atomDilate transMetzlerProfile w)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
        ((∫ u, atomDilate transMetzlerProfile w u * Real.exp (-(u / 2))) *
          (∫ u, atomDilate transMetzlerProfile w u * Real.exp (u / 2)) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2)) *
          ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
            primeHorizonExtension x n * primeHorizonExtension x j * arithmeticPoleKernel n j := by
      rw [hW_inner]; ring
    rw [hW2, hgram_split, hlevy_split, hprime_split, transMetzlerMainMatrix_inner_eq]
    unfold renormalizedPrimeEnergy
    linarith only [hpole_split]
  -- Step 4: Bound each of the five perturbation pieces
  have hpsi_le : psiConstant ≤ 4 := by
    unfold psiConstant
    have hlog4 : Real.log 4 < (7 : ℝ) / 5 := by
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      linarith only [h4, Real.log_two_lt_d9]
    have he_gt2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have hdiv : 4 / Real.exp 1 ≤ 2 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]; linarith only [he_gt2]
    linarith only [hlog4, hdiv]
  have hpd0 : 0 ≤ poleDefect N (primeHorizonExtension x) := poleDefect_nonneg _ _
  have hnorm0 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hsum0 : 0 ≤ poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2 := add_nonneg hpd0 hnorm0
  -- Piece 1: Diagonal self-energy + `log(cStar / (w * N))` scalar drift
  have hpiece1 : |(2 * gammaHardyPhaseRate 0 +
        levyEnergy (atomDilate transMetzlerProfile w) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
        Real.log N -
        (completeWeilSelfFinitePart transMetzlerProfile cStar -
          Real.eulerMascheroniConstant)) * ‖x‖ ^ 2| ≤
      (6 / Real.log ((N : ℝ) / 3)) * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    have hself := abs_levyEnergy_atomDilate_sub_le contDiff_transMetzlerProfile
      (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
      hw0 hw1 abs_transMetzlerProfile_sub_le
    have hself_div : |levyEnergy (atomDilate transMetzlerProfile w) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
          (Real.log (1 / w) + profileRobin transMetzlerProfile)| ≤
        Real.exp (1 / 2) / 2 * w := by
      have heq : levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
            (Real.log (1 / w) + profileRobin transMetzlerProfile) =
          (levyEnergy (atomDilate transMetzlerProfile w) -
            (Real.log (1 / w) + profileRobin transMetzlerProfile) *
              ∫ u, atomDilate transMetzlerProfile w u ^ 2) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) := by
        field_simp [hM_pos.ne']
      rw [heq, abs_div, abs_of_pos hM_pos, div_le_iff₀ hM_pos]
      exact hself
    have hfp := finitePart_profileRobin_eq transMetzlerProfile
    have hwN_pos : 0 < w * N := mul_pos hw0 hN0
    have hwN_half : 1 / 2 ≤ w * N := by
      have h2N : (0 : ℝ) < 2 * N := by positivity
      have h := (div_le_iff₀ h2N).mp hw_lo
      linarith only [h]
    have hlog_id : Real.log (1 / w) - Real.log N = -Real.log (w * N) := by
      rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne']; ring
    have hcfp : completeWeilSelfFinitePart transMetzlerProfile cStar =
        -Real.log (2 * Real.pi) - Real.log cStar +
          bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) := by
      have hc0 : 0 < cStar := by linarith only [hcStar]
      rw [completeWeilSelfFinitePart, one_div, Real.log_inv,
        Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) hc0.ne']
      ring
    have hlog_drift : |Real.log cStar - Real.log (w * N)| ≤ 4 / (N : ℝ) := by
      have hc0 : 0 < cStar := by linarith only [hcStar]
      have h4N : (4 : ℝ) / N = 2 * (2 / N) := by ring
      rw [h4N]
      rcases le_total cStar (w * N) with hle | hle
      · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hc0 hle)), neg_sub]
        have h1 : Real.log (w * N) - Real.log cStar ≤ (w * N - cStar) / cStar := by
          rw [← Real.log_div hwN_pos.ne' hc0.ne']
          refine (Real.log_le_sub_one_of_pos (div_pos hwN_pos hc0)).trans_eq ?_
          field_simp [hc0.ne']
        have h2 : (w * N - cStar) / cStar ≤ 2 * (w * N - cStar) := by
          rw [div_le_iff₀ hc0]
          have hsub0 : 0 ≤ w * N - cStar := sub_nonneg.mpr hle
          nlinarith only [hcStar, hsub0]
        have h3 := (abs_le.mp hdrift).2
        linarith only [h1, h2, h3]
      · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hwN_pos hle))]
        have h1 : Real.log cStar - Real.log (w * N) ≤ (cStar - w * N) / (w * N) := by
          rw [← Real.log_div hc0.ne' hwN_pos.ne']
          refine (Real.log_le_sub_one_of_pos (div_pos hc0 hwN_pos)).trans_eq ?_
          field_simp [hwN_pos.ne']
        have h2 : (cStar - w * N) / (w * N) ≤ 2 * (cStar - w * N) := by
          rw [div_le_iff₀ hwN_pos]
          have hsub0 : 0 ≤ cStar - w * N := sub_nonneg.mpr hle
          nlinarith only [hwN_half, hsub0]
        have h3 := (abs_le.mp hdrift).1
        linarith only [h1, h2, h3]
    have he2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have he1 := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith only [he1, hsq, Real.exp_pos (1 / 2 : ℝ)]
    have hw_bound : Real.exp (1 / 2) / 2 * w ≤ 2 / (N : ℝ) := by
      have hw_2 : w ≤ 2 / (N : ℝ) := hw_54.trans (by
        rw [div_le_div_iff₀ (by positivity) hN0]; linarith only [hN0])
      nlinarith only [he2, hw0, hw_2, Real.exp_pos (1 / 2 : ℝ)]
    have hscal_eq : 2 * gammaHardyPhaseRate 0 +
          levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
          Real.log N -
          (completeWeilSelfFinitePart transMetzlerProfile cStar -
            Real.eulerMascheroniConstant) =
        (levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
          (Real.log (1 / w) + profileRobin transMetzlerProfile)) +
        (Real.log cStar - Real.log (w * N)) := by
      rw [hcfp]; linarith only [hfp, hlog_id]
    have hscal_le : |2 * gammaHardyPhaseRate 0 +
          levyEnergy (atomDilate transMetzlerProfile w) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) -
          Real.log N -
          (completeWeilSelfFinitePart transMetzlerProfile cStar -
            Real.eulerMascheroniConstant)| ≤ 6 / Real.log ((N : ℝ) / 3) := by
      rw [hscal_eq]
      have htri := (abs_add_le _ _).trans (add_le_add (hself_div.trans hw_bound) hlog_drift)
      have h6N : (2 : ℝ) / N + 4 / N = 6 * (1 / N) := by ring
      have h6log : 6 * (1 / (N : ℝ)) ≤ 6 / Real.log ((N : ℝ) / 3) := by
        rw [show 6 / Real.log ((N : ℝ) / 3) = 6 * (1 / Real.log ((N : ℝ) / 3)) by ring]
        exact mul_le_mul_of_nonneg_left hinvN_le_log (by norm_num)
      exact htri.trans (by rw [h6N]; exact h6log)
    rw [abs_mul, abs_of_nonneg hnorm0]
    have hmul := mul_le_mul_of_nonneg_left (show ‖x‖ ^ 2 ≤
      poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2 by linarith only [hpd0])
      (by positivity : 0 ≤ 6 / Real.log ((N : ℝ) / 3))
    exact (mul_le_mul_of_nonneg_right hscal_le hnorm0).trans hmul
  -- Piece 2: Off-diagonal `L²` overlap
  have htop_sum := sum_sq_top_third_le hN16 (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at htop_sum
  have htop_sum4 : (∑ n ∈ Icc 1 N, if N < 3 * n then primeHorizonExtension x n ^ 2 else 0) ≤
      (24 / Real.log ((N : ℝ) / 3)) * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    have hcoef_pos : 0 ≤ 6 / Real.log ((N : ℝ) / 3) := by positivity
    have h1 : poleDefect N (primeHorizonExtension x) + psiConstant * ‖x‖ ^ 2 ≤
        4 * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
      nlinarith only [hpsi_le, hpd0, hnorm0]
    have h2 := mul_le_mul_of_nonneg_left h1 hcoef_pos
    calc _ ≤ _ := htop_sum
      _ ≤ 6 / Real.log ((N : ℝ) / 3) * (4 * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2)) := h2
      _ = _ := by ring
  have hpiece2 : |2 * gammaHardyPhaseRate 0 *
      (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        primeHorizonExtension x n * primeHorizonExtension x j *
          (if n = j then 0
            else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
              (-(Real.log j - Real.log n)) /
                (∫ u, atomDilate transMetzlerProfile w u ^ 2)))| ≤
      (96 * |gammaHardyPhaseRate 0| / Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    have hover_gram := abs_sum_overlapping_pairs_le hN16 hw_54 zero_le_one
      (fun n j => if n = j then 0
        else SpacingScaleHarmonicAnalysis.bumpCorr (atomDilate transMetzlerProfile w)
          (-(Real.log j - Real.log n)) / (∫ u, atomDilate transMetzlerProfile w u ^ 2))
      (fun n _ j _ h => by
        rcases h with rfl | hws
        · simp only [ite_true]
        · split_ifs with hnj
          · rfl
          · rw [bumpCorr_neg, bumpCorr_eq_zero hgsupp hws, zero_div])
      (fun n _ j _ hnj _ => by
        rw [if_neg hnj, abs_div, abs_of_pos hM_pos, div_le_one hM_pos]
        exact abs_bumpCorr_le hg.continuous hgc _)
      (primeHorizonExtension x)
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 := mul_le_mul_of_nonneg_left hover_gram
      (by positivity : 0 ≤ 2 * |gammaHardyPhaseRate 0|)
    have h2 := mul_le_mul_of_nonneg_left htop_sum4
      (by positivity : 0 ≤ 4 * |gammaHardyPhaseRate 0|)
    calc _ ≤ 2 * |gammaHardyPhaseRate 0| *
          (2 * 1 * ∑ n ∈ Icc 1 N, if N < 3 * n then primeHorizonExtension x n ^ 2 else 0) := h1
      _ = 4 * |gammaHardyPhaseRate 0| *
          ∑ n ∈ Icc 1 N, if N < 3 * n then primeHorizonExtension x n ^ 2 else 0 := by ring
      _ ≤ 4 * |gammaHardyPhaseRate 0| *
          ((24 / Real.log ((N : ℝ) / 3)) * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2)) := h2
      _ = _ := by ring
  -- Piece 3: Center width-drift
  have hpiece3 : |((w * N - cStar) * completeWeilPoleShift transMetzlerProfile 1) *
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) x, x⟫| ≤
      (50 / Real.log ((N : ℝ) / 3)) * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    have hq0_le : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 := by
      simpa only [one_mul] using completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
        (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos zero_le_one
    have hq0_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile 1 :=
      completeWeilPoleShift_nonneg transMetzlerProfile zero_le_one
    have hcoef_le : |(w * N - cStar) * completeWeilPoleShift transMetzlerProfile 1| ≤
        2 / Real.log ((N : ℝ) / 3) := by
      rw [abs_mul, abs_of_nonneg hq0_nonneg]
      have h1 : |w * N - cStar| * completeWeilPoleShift transMetzlerProfile 1 ≤ 2 / (N : ℝ) := by
        nlinarith only [hdrift, hq0_le, abs_nonneg (w * N - cStar)]
      exact h1.trans (by
        rw [show 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring,
          show 2 / Real.log ((N : ℝ) / 3) = 2 * (1 / Real.log ((N : ℝ) / 3)) by ring]
        exact mul_le_mul_of_nonneg_left hinvN_le_log (by norm_num))
    have hc1_le := (abs_fullWeilCenterMatrix_one_inner_le hN1 x).trans (by
      show 2 * poleDefect N (primeHorizonExtension x) + (2 * psiConstant + 15) * ‖x‖ ^ 2 ≤
        25 * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2)
      nlinarith only [hpsi_le, hpd0, hnorm0])
    rw [abs_mul]
    calc _ ≤ (2 / Real.log ((N : ℝ) / 3)) *
          (25 * (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2)) :=
        mul_le_mul hcoef_le hc1_le (abs_nonneg _) (by positivity)
      _ = _ := by ring
  -- Piece 4: Non-ratio prime form
  have hpiece4 : |nonRatioForm (atomDilate transMetzlerProfile w) N (primeHorizonExtension x) /
        (∫ u, atomDilate transMetzlerProfile w u ^ 2)| ≤
      (1050 * δ₀ + 2100 / Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    rw [abs_div, abs_of_pos hM_pos]
    have hnr := abs_nonRatioForm_transMetzler_le hN16 hδ0 hδ4 hw_lo hw_hi (primeHorizonExtension x)
    rw [sum_primeHorizonExtension_sq] at hnr
    refine hnr.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hsum0
    have h2log : 2 / (N : ℝ) ≤ 2 / Real.log ((N : ℝ) / 3) := by
      rw [show 2 / (N : ℝ) = 2 * (1 / (N : ℝ)) by ring,
        show 2 / Real.log ((N : ℝ) / 3) = 2 * (1 / Real.log ((N : ℝ) / 3)) by ring]
      exact mul_le_mul_of_nonneg_left hinvN_le_log (by norm_num)
    rw [show 1050 * δ₀ + 2100 / Real.log ((N : ℝ) / 3) =
      1050 * (δ₀ + 2 / Real.log ((N : ℝ) / 3)) by ring]
    linarith only [h2log]
  -- Piece 5: Overlapping adjacent `levyMixed` + center collar
  have hpiece5 : |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      primeHorizonExtension x n * primeHorizonExtension x j *
        (if n = j ∨ w < |Real.log j - Real.log n| then 0
          else (∫ y in Set.Ioi 0,
            levyMixed (atom (atomDilate transMetzlerProfile w) n)
              (atom (atomDilate transMetzlerProfile w) j) y) /
            (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
            w * completeWeilPoleShift transMetzlerProfile 1 *
              archimedeanCenterKernel n j)| ≤
      (288 * δ₀ + 48 * (selfEnergyConstant + 96001) / Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    have hsec0 : 0 ≤ selfEnergyConstant := by
      unfold selfEnergyConstant
      have h2 : Real.exp (-2 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
      have hden : 0 < 1 - Real.exp (-2 : ℝ) := by linarith only [h2]
      positivity
    have hB_pos : 0 ≤ 3 * δ₀ * Real.log N + 3 * δ₀ * (selfEnergyConstant + 32000) + 64001 := by
      have hl0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
      positivity
    have hover_levy := abs_sum_overlapping_pairs_le hN16 hw_54 hB_pos
      (fun n j => if n = j ∨ w < |Real.log j - Real.log n| then 0
        else (∫ y in Set.Ioi 0,
          levyMixed (atom (atomDilate transMetzlerProfile w) n)
            (atom (atomDilate transMetzlerProfile w) j) y) /
          (∫ u, atomDilate transMetzlerProfile w u ^ 2) +
          w * completeWeilPoleShift transMetzlerProfile 1 * archimedeanCenterKernel n j)
      (fun n _ j _ h => if_pos h)
      (fun n hn j hj hnj hlog => by
        rw [if_neg (fun h => h.elim hnj (not_lt.mpr hlog))]
        have hlm := abs_integral_levyMixed_adjacent_le hN16 hδ0 hδ4 hw_lo hw_hi hn hj hnj hlog
        have hs_ge := (top_adjacent_of_log_gap_le hN16 hn hj hnj hw_54 hlog).2.2.2
        have hs_pos : 0 < |Real.log j - Real.log n| := lt_of_lt_of_le (by positivity) hs_ge
        have hnz : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
        have hjz : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
        have hq0_le : completeWeilPoleShift transMetzlerProfile 1 ≤ 1 := by
          simpa only [one_mul] using completeWeilPoleShift_le contDiff_transMetzlerProfile.continuous
            (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
            zero_le_one
        have hq0_nonneg : 0 ≤ completeWeilPoleShift transMetzlerProfile 1 :=
          completeWeilPoleShift_nonneg transMetzlerProfile zero_le_one
        have hck_le : w * completeWeilPoleShift transMetzlerProfile 1 *
            archimedeanCenterKernel n j ≤ 1 := by
          rw [archimedeanCenterKernel, if_neg (by simp only [hnj, hnz, hjz, or_self, not_false_eq_true])]
          have hd := ArithmeticIncidencePositivity.archLevyDensity_le_inv hs_pos
          have hinv_s : 1 / (2 * |Real.log j - Real.log n|) ≤ (N : ℝ) / 2 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            have h := (div_le_iff₀ hN0).mp hs_ge
            linarith only [h]
          have hω_le : archLevyDensity |Real.log j - Real.log n| ≤ (N : ℝ) / 2 + 1 / 4 :=
            hd.trans (by linarith only [hinv_s])
          have hwq_le : w * completeWeilPoleShift transMetzlerProfile 1 ≤ 5 / (4 * (N : ℝ)) := by
            have := mul_le_mul_of_nonneg_left hq0_le hw0.le
            linarith only [this, hw_54]
          calc w * completeWeilPoleShift transMetzlerProfile 1 *
                archLevyDensity |Real.log j - Real.log n|
              ≤ (5 / (4 * (N : ℝ))) * ((N : ℝ) / 2 + 1 / 4) :=
                mul_le_mul hwq_le hω_le (archLevyDensity_pos hs_pos).le (by positivity)
            _ = 5 / 8 + 5 / (16 * (N : ℝ)) := by field_simp [hN0.ne']; ring
            _ ≤ 1 := by
                have : 5 / (16 * (N : ℝ)) ≤ 3 / 8 := by
                  rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hN27]
                linarith only [this]
        have hck0 : 0 ≤ w * completeWeilPoleShift transMetzlerProfile 1 *
            archimedeanCenterKernel n j :=
          mul_nonneg (mul_nonneg hw0.le hq0_nonneg) (archimedeanCenterKernel_nonneg n j)
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg hck0]
        linarith only [hlm, hck_le])
      (primeHorizonExtension x)
    have hmul_top := hover_levy.trans (mul_le_mul_of_nonneg_left htop_sum4 (by positivity))
    rw [← mul_assoc] at hmul_top
    refine hmul_top.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hsum0
    have hlhs_eq :
        2 * (3 * δ₀ * Real.log N + 3 * δ₀ * (selfEnergyConstant + 32000) + 64001) *
          (24 / Real.log ((N : ℝ) / 3)) =
        (144 * δ₀) * (Real.log N / Real.log ((N : ℝ) / 3)) +
          (3 * δ₀ * (selfEnergyConstant + 32000) + 64001) * (48 / Real.log ((N : ℝ) / 3)) := by ring
    have hrhs_eq :
        288 * δ₀ + 48 * (selfEnergyConstant + 96001) / Real.log ((N : ℝ) / 3) =
        288 * δ₀ + (selfEnergyConstant + 96001) * (48 / Real.log ((N : ℝ) / 3)) := by ring
    rw [hlhs_eq, hrhs_eq]
    have hcoef_log : (144 * δ₀) * (Real.log N / Real.log ((N : ℝ) / 3)) ≤ 288 * δ₀ := by
      have h1 : Real.log (N : ℝ) / Real.log ((N : ℝ) / 3) ≤ 2 :=
        (div_le_iff₀ hlogN3_pos).mpr hlogN_le_two
      have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 144 * δ₀ by positivity)
      linarith only [h2]
    have hδ_c : 3 * δ₀ * (selfEnergyConstant + 32000) + 64001 ≤ selfEnergyConstant + 96001 := by
      nlinarith only [hδ4, hsec0]
    have hcoef_const : (3 * δ₀ * (selfEnergyConstant + 32000) + 64001) *
        (48 / Real.log ((N : ℝ) / 3)) ≤
        (selfEnergyConstant + 96001) * (48 / Real.log ((N : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_right hδ_c (by positivity)
    linarith only [hcoef_log, hcoef_const]
  -- Combine all 5 perturbation bounds
  have hsum5 : |⟪Matrix.toEuclideanLin
          (normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile w) N) x, x⟫ -
        ⟪Matrix.toEuclideanLin (transMetzlerMainMatrix w cStar N) x, x⟫| ≤
      (1338 * δ₀ +
        (2156 + 96 * |gammaHardyPhaseRate 0| + 48 * (selfEnergyConstant + 96001)) /
          Real.log ((N : ℝ) / 3)) *
        (poleDefect N (primeHorizonExtension x) + ‖x‖ ^ 2) := by
    rw [hdiff_eq]
    have htri5 : ∀ a b c d e : ℝ,
        |a + b + c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := fun a b c d e => by
      have h1 := abs_add_le (a + b + c - d) e
      have h2 : |a + b + c - d| ≤ |a + b + c| + |d| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg])
      have h3 := abs_add_le (a + b) c
      have h4 := abs_add_le a b
      linarith only [h1, h2, h3, h4]
    have htri := (htri5 _ _ _ _ _).trans
      (add_le_add (add_le_add (add_le_add (add_le_add hpiece1 hpiece2) hpiece3) hpiece4) hpiece5)
    have hcoeff_eq :
        (6 / Real.log ((N : ℝ) / 3)) +
        (96 * |gammaHardyPhaseRate 0| / Real.log ((N : ℝ) / 3)) +
        (50 / Real.log ((N : ℝ) / 3)) +
        (1050 * δ₀ + 2100 / Real.log ((N : ℝ) / 3)) +
        (288 * δ₀ + 48 * (selfEnergyConstant + 96001) / Real.log ((N : ℝ) / 3)) =
        1338 * δ₀ +
          (2156 + 96 * |gammaHardyPhaseRate 0| + 48 * (selfEnergyConstant + 96001)) /
            Real.log ((N : ℝ) / 3) := by ring
    refine htri.trans_eq ?_
    rw [← hcoeff_eq]
    ring
  refine hsum5.trans (mul_le_mul_of_nonneg_right ?_ hsum0)
  linarith only [hδ0]

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.top_adjacent_of_log_gap_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_transMetzlerMainMatrix_ramanujan_residual_norm
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.abs_nonRatioForm_transMetzler_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.exists_perturbation_bound_transMetzler
