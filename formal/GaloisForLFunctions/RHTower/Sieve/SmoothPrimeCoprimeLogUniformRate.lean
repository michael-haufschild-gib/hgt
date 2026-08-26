import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeCoprimeLogHeadRate
import GaloisForLFunctions.RHTower.Sieve.SmoothPrimeReciprocalTail
import GaloisForLFunctions.RHTower.Sieve.LogSumFromCount

/-!
# Uniform smooth-prime approximation of the coprime logarithmic Möbius kernel
-/

namespace RHTower.Sieve

open ArithmeticFunction Finset Set
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

theorem sum_primeSupportedReciprocal_add_Ioi_tsum
    {r D : ℕ} (hr : 0 < r) :
    (∑ d ∈ Finset.Icc 1 D, primeSupportedReciprocal r d) +
        (∑' d : ℕ, (Set.Ioi D).indicator
          (fun n : ℕ => primeSupportedReciprocal r n) d) =
      ∑' d : ℕ, primeSupportedReciprocal r d := by
  classical
  let head : ℕ → ℝ := ((Finset.Icc 1 D : Finset ℕ) : Set ℕ).indicator
    (fun n : ℕ => primeSupportedReciprocal r n)
  let tail : ℕ → ℝ := (Set.Ioi D).indicator
    (fun n : ℕ => primeSupportedReciprocal r n)
  have hhead : Summable head := summable_of_ne_finset_zero (s := Finset.Icc 1 D) (by
    intro n hn
    have hnset : n ∉ ((Finset.Icc 1 D : Finset ℕ) : Set ℕ) := by omega
    simp only [head, Set.indicator]
    rw [if_neg hnset])
  have htail : Summable tail := summable_primeSupportedReciprocal_Ioi hr D
  have hdecomp : (fun n : ℕ => primeSupportedReciprocal r n) =
      fun n => head n + tail n := by
    funext d
    rcases d.eq_zero_or_pos with rfl | hd
    · simp only [head, tail, Set.indicator]
      simp
    · by_cases hdD : d ≤ D
      · have hdIcc : d ∈ Finset.Icc 1 D := Finset.mem_Icc.mpr ⟨hd, hdD⟩
        have hdIccSet : d ∈ ((Finset.Icc 1 D : Finset ℕ) : Set ℕ) := hdIcc
        have hdIoi : d ∉ Set.Ioi D := by simp [hdD]
        simp only [head, tail, Set.indicator]
        rw [if_pos hdIccSet, if_neg hdIoi, add_zero]
      · have hdIcc : d ∉ Finset.Icc 1 D := by simp [hdD]
        have hdIccSet : d ∉ ((Finset.Icc 1 D : Finset ℕ) : Set ℕ) := hdIcc
        have hdIoi : d ∈ Set.Ioi D := by simpa using (Nat.lt_of_not_ge hdD)
        simp only [head, tail, Set.indicator]
        rw [if_neg hdIccSet, if_pos hdIoi, zero_add]
  have hheadTsum : (∑' n : ℕ, head n) =
      ∑ n ∈ Finset.Icc 1 D, primeSupportedReciprocal r n := by
    rw [tsum_eq_sum (s := Finset.Icc 1 D)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hnset : n ∈ ((Finset.Icc 1 D : Finset ℕ) : Set ℕ) := by omega
      simp only [head, Set.indicator]
      rw [if_pos hnset]
    · intro n hn
      have hnset : n ∉ ((Finset.Icc 1 D : Finset ℕ) : Set ℕ) := by omega
      simp only [head, Set.indicator]
      rw [if_neg hnset]
  change (∑ d ∈ Finset.Icc 1 D, primeSupportedReciprocal r d) +
      (∑' d : ℕ, tail d) = _
  rw [← hheadTsum, ← hhead.tsum_add htail, ← hdecomp]

theorem sum_primeSupportedReciprocal_Icc_tail_le_Ioi_tsum
    {r D N : ℕ} (hr : 0 < r) :
    (∑ d ∈ Finset.Icc (D + 1) N, primeSupportedReciprocal r d) ≤
      ∑' d : ℕ, (Set.Ioi D).indicator
        (fun n : ℕ => primeSupportedReciprocal r n) d := by
  classical
  have heq :
      (∑ d ∈ Finset.Icc (D + 1) N, primeSupportedReciprocal r d) =
      ∑ d ∈ Finset.Icc (D + 1) N,
        (Set.Ioi D).indicator (fun n : ℕ => primeSupportedReciprocal r n) d := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Set.indicator_of_mem]
    exact (Finset.mem_Icc.mp hd).1
  rw [heq]
  exact (summable_primeSupportedReciprocal_Ioi hr D).sum_le_tsum
    (Finset.Icc (D + 1) N) (fun d _ => by
      by_cases h : d ∈ Set.Ioi D
      · simp [Set.indicator, h, primeSupportedReciprocal_nonneg]
      · simp [Set.indicator, h])

theorem sum_primeSupportedReciprocal_mul_kernel_sub_sum_eq_smoothHead
    (r D : ℕ) (Y : ℝ) :
    (∑ d ∈ Finset.Icc 1 D,
        primeSupportedReciprocal r d * coprimeLogMoebius 1 (Y / (d : ℝ))) -
      ∑ d ∈ Finset.Icc 1 D, primeSupportedReciprocal r d =
      ∑ d ∈ primeSupportedIcc r D,
        (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1) := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [primeSupportedIcc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd).1)
  by_cases hs : primeSupportedOn r d
  · rw [if_pos hs, primeSupportedReciprocal_apply_of_supported hs,
      reciprocalNatArithmetic_apply hd0]
    ring
  · rw [if_neg hs, primeSupportedReciprocal_apply_of_not_supported hs]
    ring

/-- Exact smooth expansion plus a finite head and one reciprocal tail. -/
theorem abs_coprimeLogMoebius_sub_totientRatio_le_smoothHead_add_tail
    {r : ℕ} (hr : Squarefree r) {Y : ℝ} {D : ℕ}
    (hDN : D ≤ ⌊Y⌋₊) :
    |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
      |∑ d ∈ primeSupportedIcc r D,
          (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| +
        (7 + |Real.eulerMascheroniConstant|) *
          (∑' d : ℕ, (Set.Ioi D).indicator
            (fun n : ℕ => primeSupportedReciprocal r n) d) := by
  classical
  let N := ⌊Y⌋₊
  let A := ∑ d ∈ Finset.Icc 1 D,
    primeSupportedReciprocal r d * coprimeLogMoebius 1 (Y / (d : ℝ))
  let B := ∑ d ∈ Finset.Icc (D + 1) N,
    primeSupportedReciprocal r d * coprimeLogMoebius 1 (Y / (d : ℝ))
  let H := ∑ d ∈ Finset.Icc 1 D, primeSupportedReciprocal r d
  let T := ∑' d : ℕ, (Set.Ioi D).indicator
    (fun n : ℕ => primeSupportedReciprocal r n) d
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr.ne_zero
  have hexpansion : coprimeLogMoebius r Y = A + B := by
    rw [coprimeLogMoebius_eq_sum_primeSupportedReciprocal]
    exact sum_Icc_one_split hDN _
  have hmass : (r : ℝ) / (Nat.totient r : ℝ) = H + T := by
    rw [← tsum_primeSupportedReciprocal_eq_totientRatio hr]
    exact (sum_primeSupportedReciprocal_add_Ioi_tsum hrpos).symm
  have hhead : A - H = ∑ d ∈ primeSupportedIcc r D,
      (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1) :=
    sum_primeSupportedReciprocal_mul_kernel_sub_sum_eq_smoothHead r D Y
  have hB : |B| ≤ (6 + |Real.eulerMascheroniConstant|) * T := by
    calc
      |B| ≤ ∑ d ∈ Finset.Icc (D + 1) N,
          |primeSupportedReciprocal r d *
            coprimeLogMoebius 1 (Y / (d : ℝ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Finset.Icc (D + 1) N,
          (6 + |Real.eulerMascheroniConstant|) * primeSupportedReciprocal r d := by
        apply Finset.sum_le_sum
        intro d hd
        rw [abs_mul, abs_of_nonneg (primeSupportedReciprocal_nonneg r d)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right
          (abs_coprimeLogMoebius_one_le (Y / (d : ℝ)))
          (primeSupportedReciprocal_nonneg r d)
      _ = (6 + |Real.eulerMascheroniConstant|) *
          ∑ d ∈ Finset.Icc (D + 1) N, primeSupportedReciprocal r d := by
        rw [Finset.mul_sum]
      _ ≤ (6 + |Real.eulerMascheroniConstant|) * T := by
        apply mul_le_mul_of_nonneg_left
          (sum_primeSupportedReciprocal_Icc_tail_le_Ioi_tsum hrpos)
        positivity
  have hT : 0 ≤ T := tsum_nonneg (fun d => by
    by_cases h : d ∈ Set.Ioi D
    · simp [Set.indicator, h, primeSupportedReciprocal_nonneg]
    · simp [Set.indicator, h])
  rw [hexpansion, hmass]
  calc
    |A + B - (H + T)| = |(A - H) + (B - T)| := by ring_nf
    _ ≤ |A - H| + |B - T| := abs_add_le _ _
    _ ≤ |A - H| + (|B| + T) := by
      gcongr
      calc
        |B - T| ≤ |B| + |T| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le B (-T)
        _ = |B| + T := by rw [abs_of_nonneg hT]
    _ ≤ |A - H| + ((6 + |Real.eulerMascheroniConstant|) * T + T) := by
      gcongr
    _ = |∑ d ∈ primeSupportedIcc r D,
          (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| +
        (7 + |Real.eulerMascheroniConstant|) * T := by
      rw [hhead]
      ring

/-- Quantitative finite-head plus fractional-moment tail estimate. -/
theorem exists_abs_coprimeLogMoebius_sub_totientRatio_smoothBound
    {r : ℕ} (hr : Squarefree r) :
    ∃ C K : ℝ, 0 ≤ C ∧ Real.exp 1 ≤ K ∧
      ∀ (Y : ℝ) (D : ℕ), 1 ≤ D → D ≤ ⌊Y⌋₊ → K ≤ Y / (D : ℝ) →
        |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
          C * ((r : ℝ) / (Nat.totient r : ℝ)) /
              (Real.log (Y / (D : ℝ))) ^ 2 +
            (7 + |Real.eulerMascheroniConstant|) *
              ((D : ℝ) ^ (-(1 / 4 : ℝ)) * smoothPrimeThreeQuarterMass r) := by
  obtain ⟨C, K, hC, hK, hhead⟩ :=
    exists_abs_smoothPrimeCoprimeLogHead_log_sq_rate hr
  refine ⟨C, K, hC, hK, ?_⟩
  intro Y D hD hDN hscale
  calc
    |coprimeLogMoebius r Y - (r : ℝ) / (Nat.totient r : ℝ)| ≤
        |∑ d ∈ primeSupportedIcc r D,
          (1 / (d : ℝ)) * (coprimeLogMoebius 1 (Y / (d : ℝ)) - 1)| +
        (7 + |Real.eulerMascheroniConstant|) *
          (∑' d : ℕ, (Set.Ioi D).indicator
            (fun n : ℕ => primeSupportedReciprocal r n) d) :=
      abs_coprimeLogMoebius_sub_totientRatio_le_smoothHead_add_tail hr hDN
    _ ≤ C * ((r : ℝ) / (Nat.totient r : ℝ)) /
          (Real.log (Y / (D : ℝ))) ^ 2 +
        (7 + |Real.eulerMascheroniConstant|) *
          ((D : ℝ) ^ (-(1 / 4 : ℝ)) * smoothPrimeThreeQuarterMass r) := by
      gcongr
      · exact hhead Y D hD hscale
      · exact tsum_primeSupportedReciprocal_Ioi_le_threeQuarterMass
          (Nat.pos_of_ne_zero hr.ne_zero) hD

end

end RHTower.Sieve

