import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheConductorResidualsAreSmallOnTheDeepRows
import GaloisForLFunctions.HTGeometry.SharpHardySchur
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum

/-!
# Uniform tails of the separated Gamma pairing

The reciprocal-square cross-entry estimate retains an integrable tail on
the whole arithmetic horizon. Comparable indices give `O(c/T)` by summing
integer gaps; distant indices give `O(c²/N)` by reciprocal-square-root sums.
The bound is uniform before the horizon limit and preserves bounded signed
arithmetic weights.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis

private theorem sum_Icc_reciprocal_sqrt_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, 1 / Real.sqrt n) ≤ 2 * Real.sqrt N := by
  rw [← sum_range_succ_eq_sum_Icc]
  simpa only [Nat.cast_add, Nat.cast_one] using sum_inv_sqrt_succ_le N

/-- A positive real gap cutoff gives an inverse-square tail without a rounding loss. -/
theorem sum_inv_sq_above_real_le {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (∑ h ∈ Icc 1 N, if x < (h : ℝ) then 1 / (h : ℝ) ^ 2 else 0) ≤ 2 / x := by
  let a : ℕ := ⌊x⌋₊ + 1
  have ha : 1 ≤ a := by dsimp only [a]; omega
  have hxa : x < (a : ℝ) := by
    dsimp only [a]
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one x
  have heq : (Icc 1 N).filter (fun h : ℕ => x < (h : ℝ)) = Icc a N := by
    ext h
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hh1, hhN⟩, hxh⟩
      have hhf : (⌊x⌋₊ : ℝ) < h := (Nat.floor_le hx.le).trans_lt hxh
      have hfh : ⌊x⌋₊ < h := by exact_mod_cast hhf
      exact ⟨by dsimp only [a]; omega, hhN⟩
    · rintro ⟨hah, hhN⟩
      have hah' : (a : ℝ) ≤ h := by exact_mod_cast hah
      exact ⟨⟨ha.trans hah, hhN⟩, hxa.trans_le hah'⟩
  rw [← sum_filter, heq]
  exact (sum_Icc_inv_sq_from_le_deep ha).trans
    (div_le_div_of_nonneg_left zero_le_two hx hxa.le)

private theorem weighted_gap_comparable_le {n j : ℕ}
    (hn : 1 ≤ n) (hnj : n < j) (hjn : j ≤ 2 * n) :
    (j : ℝ) ^ 2 / (((j : ℝ) - n) ^ 2 * (Real.sqrt n * Real.sqrt j)) ≤
      4 * n / ((j : ℝ) - n) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnj' : (n : ℝ) < j := by exact_mod_cast hnj
  have hjn' : (j : ℝ) ≤ 2 * n := by exact_mod_cast hjn
  have hj0 : (0 : ℝ) < j := hn0.trans hnj'
  have hsprod : (n : ℝ) ≤ Real.sqrt n * Real.sqrt j := by
    calc
      _ = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnj'.le) (Real.sqrt_nonneg _)
  have hgap : 0 < ((j : ℝ) - n) ^ 2 := sq_pos_of_pos (sub_pos.mpr hnj')
  rw [div_le_div_iff₀ (mul_pos hgap (by positivity)) hgap]
  have hsq : (j : ℝ) ^ 2 ≤ 4 * n ^ 2 := by
    have h := pow_le_pow_left₀ hj0.le hjn' 2
    norm_num [mul_pow] at h
    exact h
  have hprod := mul_le_mul_of_nonneg_left hsprod (by positivity : (0 : ℝ) ≤ 4 * n)
  have hjprod : (j : ℝ) ^ 2 ≤ 4 * n * (Real.sqrt n * Real.sqrt j) := by
    nlinarith only [hsq, hprod]
  nlinarith only [mul_le_mul_of_nonneg_right hjprod hgap.le]

private theorem weighted_gap_distant_le {n j : ℕ}
    (hn : 1 ≤ n) (hjn : 2 * n < j) :
    (j : ℝ) ^ 2 / (((j : ℝ) - n) ^ 2 * (Real.sqrt n * Real.sqrt j)) ≤
      4 / (Real.sqrt n * Real.sqrt j) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hjn' : (2 * n : ℝ) < j := by exact_mod_cast hjn
  have hj0 : (0 : ℝ) < j := by linarith
  have hgap : 0 < ((j : ℝ) - n) ^ 2 := sq_pos_of_pos (by linarith)
  have hs : 0 < Real.sqrt n * Real.sqrt j := by positivity
  rw [div_le_div_iff₀ (mul_pos hgap hs) hs]
  have hsq : (j : ℝ) ^ 2 ≤ 4 * ((j : ℝ) - n) ^ 2 := by
    nlinarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ j - 2 * n)
      (by linarith : (0 : ℝ) ≤ 3 * j - 2 * n)]
  nlinarith only [mul_le_mul_of_nonneg_right hsq hs.le]

private theorem sum_upper_gap_inv_sq_le {q : ℝ} (hq : 0 < q) {n : ℕ}
    (hn : 1 ≤ n) (N : ℕ) :
    (∑ j ∈ Icc 1 N, if n < j ∧ q * n < (j : ℝ) - n then
      4 * n / ((j : ℝ) - n) ^ 2 else 0) ≤ 8 / q := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : (∑ j ∈ Icc 1 N, if n < j ∧ q * n < (j : ℝ) - n then
      4 * n / ((j : ℝ) - n) ^ 2 else 0) =
      4 * (n : ℝ) * ∑ h ∈ Icc 1 (N - n), if q * n < (h : ℝ) then 1 / (h : ℝ) ^ 2 else 0 := by
    simp_rw [ite_and]
    rw [sum_Icc_ite_lt_eq]
    simp only [Nat.cast_add, add_sub_cancel_left]
    rw [mul_sum]
    apply sum_congr rfl
    intro h hh
    split_ifs <;> ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left (sum_inv_sq_above_real_le (mul_pos hq hn0) (N - n))
    (by positivity : (0 : ℝ) ≤ 4 * n)).trans_eq (by field_simp [hq.ne', hn0.ne']; ring)

private theorem sum_pair_reciprocal_sqrt_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 4 / (Real.sqrt n * Real.sqrt j)) ≤ 16 * N := by
  let S : ℝ := ∑ n ∈ Icc 1 N, 1 / Real.sqrt n
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hbound : S ≤ 2 * Real.sqrt N := sum_Icc_reciprocal_sqrt_le N
  have hsq := pow_le_pow_left₀ hS hbound 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at hsq
  have heq : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 4 / (Real.sqrt n * Real.sqrt j)) =
      4 * S ^ 2 := by
    dsimp only [S]
    rw [pow_two, sum_mul_sum, mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [heq]
  nlinarith only [hsq]

/-- The upper-triangle reciprocal-square kernel has a uniform scaled-gap tail. -/
theorem sum_upper_gap_majorant_le {q : ℝ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      if n < j ∧ q * n < (j : ℝ) - n then
        (j : ℝ) ^ 2 / (((j : ℝ) - n) ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) ≤
      8 * N / q + 16 * N := by
  have hpt : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      (if n < j ∧ q * n < (j : ℝ) - n then
        (j : ℝ) ^ 2 / (((j : ℝ) - n) ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) ≤
      (if n < j ∧ q * n < (j : ℝ) - n then 4 * n / ((j : ℝ) - n) ^ 2 else 0) +
        4 / (Real.sqrt n * Real.sqrt j) := by
    intro n hn j hj
    by_cases h : n < j ∧ q * n < (j : ℝ) - n
    · rw [if_pos h, if_pos h]
      by_cases hjn : j ≤ 2 * n
      · exact (weighted_gap_comparable_le (mem_Icc.mp hn).1 h.1 hjn).trans
          (le_add_of_nonneg_right (by positivity))
      · exact (weighted_gap_distant_le (mem_Icc.mp hn).1 (by omega)).trans
          (le_add_of_nonneg_left (by positivity))
    · rw [if_neg h, if_neg h, zero_add]
      positivity
  calc
    _ ≤ (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        if n < j ∧ q * n < (j : ℝ) - n then 4 * n / ((j : ℝ) - n) ^ 2 else 0) +
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, 4 / (Real.sqrt n * Real.sqrt j) := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro n hn
      rw [← sum_add_distrib]
      exact sum_le_sum fun j hj => hpt n hn j hj
    _ ≤ (∑ _n ∈ Icc 1 N, (8 / q)) + 16 * N :=
      add_le_add (sum_le_sum fun n hn => sum_upper_gap_inv_sq_le hq (mem_Icc.mp hn).1 N)
        (sum_pair_reciprocal_sqrt_le N)
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]; norm_num; ring

private theorem mul_lt_gap_of_lt_log_gap {n j : ℕ} (hn : 1 ≤ n) (hnj : n < j)
    {q : ℝ} (hq : q < |Real.log j - Real.log n|) : q * n < (j : ℝ) - n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnj' : (n : ℝ) < j := by exact_mod_cast hnj
  have hj0 := hn0.trans hnj'
  have hlog : 0 < Real.log j - Real.log n := sub_pos.mpr (Real.log_lt_log hn0 hnj')
  rw [abs_of_pos hlog] at hq
  have hl := Real.log_le_sub_one_of_pos (div_pos hj0 hn0)
  rw [Real.log_div hj0.ne' hn0.ne'] at hl
  have h := hq.trans_le hl
  have heq : (j : ℝ) / n - 1 = ((j : ℝ) - n) / n := by field_simp [hn0.ne']
  rw [heq, lt_div_iff₀ hn0] at h
  exact h

/-- Reciprocal-square log gaps retain an integrable tail on the whole arithmetic horizon. -/
theorem sum_log_gap_majorant_le {q : ℝ} (hq : 0 < q) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      if q < |Real.log j - Real.log n| then
        (max (n : ℝ) j) ^ 2 / (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) ≤
      16 * N / q + 32 * N := by
  let F : ℕ → ℕ → ℝ := fun n j => if n < j ∧ q * n < (j : ℝ) - n then
    (j : ℝ) ^ 2 / (((j : ℝ) - n) ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0
  have hF : ∀ n j, 0 ≤ F n j := by
    intro n j
    dsimp only [F]
    split_ifs <;> positivity
  have hpt : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      (if q < |Real.log j - Real.log n| then
        (max (n : ℝ) j) ^ 2 / (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) ≤
      F n j + F j n := by
    intro n hn j hj
    by_cases hqgap : q < |Real.log j - Real.log n|
    · rw [if_pos hqgap]
      have hne : n ≠ j := by
        rintro rfl
        simp only [sub_self, abs_zero] at hqgap
        exact (not_lt_of_ge hq.le) hqgap
      rcases lt_or_gt_of_ne hne with hnj | hjn
      · have hnj' : (n : ℝ) < j := by exact_mod_cast hnj
        have hgap := mul_lt_gap_of_lt_log_gap (mem_Icc.mp hn).1 hnj hqgap
        have heq : (max (n : ℝ) j) ^ 2 /
            (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) = F n j := by
          dsimp only [F]
          rw [if_pos ⟨hnj, hgap⟩, max_eq_right hnj'.le, abs_of_neg (sub_neg.mpr hnj'), neg_sub]
        rw [heq]
        exact le_add_of_nonneg_right (hF j n)
      · have hjn' : (j : ℝ) < n := by exact_mod_cast hjn
        have hqgap' : q < |Real.log n - Real.log j| := by simpa only [abs_sub_comm] using hqgap
        have hgap := mul_lt_gap_of_lt_log_gap (mem_Icc.mp hj).1 hjn hqgap'
        have heq : (max (n : ℝ) j) ^ 2 /
            (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) = F j n := by
          dsimp only [F]
          rw [if_pos ⟨hjn, hgap⟩, max_eq_left hjn'.le, abs_of_pos (sub_pos.mpr hjn')]
          rw [mul_comm (Real.sqrt n)]
        rw [heq]
        exact le_add_of_nonneg_left (hF n j)
    · rw [if_neg hqgap]
      exact add_nonneg (hF n j) (hF j n)
  have hb : (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, F n j) ≤ 8 * N / q + 16 * N :=
    sum_upper_gap_majorant_le hq N
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, (F n j + F j n) :=
      sum_le_sum fun n hn => sum_le_sum fun j hj => hpt n hn j hj
    _ = 2 * (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, F n j) := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun n j => F j n)]
      ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hb zero_le_two).trans_eq (by ring)

/-- Actual separated cross entries have a tail uniform before the horizon limit. -/
theorem abs_farCross_pair_tail_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c T : ℝ} (hc : 0 < c) (hT : 2 ≤ T)
    {N : ℕ} (hN : 1 ≤ N) {u v : ℕ → ℝ} {B : ℝ}
    (hu : ∀ n, |u n| ≤ B) (hv : ∀ n, |v n| ≤ B) :
    |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
      if T * (c / N) < |Real.log j - Real.log n| then
        u n * v j * atomCrossErrorKernel (atomDilate φ (c / N)) n j /
          (Real.sqrt n * Real.sqrt j) else 0| ≤
      B ^ 2 * (152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)) *
        (16 * c / T + 32 * c ^ 2 / N) := by
  let C : ℝ := 152 * (∫ u, |φ u|) ^ 2 / (∫ u, φ u ^ 2)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hB : 0 ≤ B := (abs_nonneg _).trans (hu 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hT0 : 0 < T := by linarith
  have hq : 0 < T * (c / N) := mul_pos hT0 hw
  have hpt : ∀ n ∈ Icc 1 N, ∀ j ∈ Icc 1 N,
      |if T * (c / N) < |Real.log j - Real.log n| then
        u n * v j * atomCrossErrorKernel (atomDilate φ (c / N)) n j /
          (Real.sqrt n * Real.sqrt j) else 0| ≤
      (B ^ 2 * C * (c / N) ^ 2) *
        (if T * (c / N) < |Real.log j - Real.log n| then
          (max (n : ℝ) j) ^ 2 /
            (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) := by
    intro n hn j hj
    by_cases hgap : T * (c / N) < |Real.log j - Real.log n|
    · rw [if_pos hgap, if_pos hgap]
      have hs : 2 * (c / N) < |Real.log j - Real.log n| :=
        (mul_le_mul_of_nonneg_right hT hw.le).trans_lt hgap
      have hb := abs_separatedCrossError_le hφ hsupp hM hc hN hn hj
      rw [if_pos hs] at hb
      have hcoeff : |u n * v j| ≤ B ^ 2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (hu n) (hv j) (abs_nonneg _) hB
      have hprod := mul_le_mul hcoeff hb (abs_nonneg _) (sq_nonneg B)
      have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hn).1)
      have hsj : 0 < Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast (mem_Icc.mp hj).1)
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hsn hsj)]
      exact (div_le_div_of_nonneg_right hprod (mul_pos hsn hsj).le).trans_eq (by dsimp only [C]; ring)
    · simp only [if_neg hgap, abs_zero, mul_zero, le_refl]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
        |if T * (c / N) < |Real.log j - Real.log n| then
          u n * v j * atomCrossErrorKernel (atomDilate φ (c / N)) n j /
            (Real.sqrt n * Real.sqrt j) else 0| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => abs_sum_le_sum_abs _ _)
    _ ≤ (B ^ 2 * C * (c / N) ^ 2) *
        (∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N,
          if T * (c / N) < |Real.log j - Real.log n| then
            (max (n : ℝ) j) ^ 2 /
              (|(n : ℝ) - j| ^ 2 * (Real.sqrt n * Real.sqrt j)) else 0) := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      rw [mul_sum]
      exact sum_le_sum fun j hj => hpt n hn j hj
    _ ≤ (B ^ 2 * C * (c / N) ^ 2) * (16 * N / (T * (c / N)) + 32 * N) :=
      mul_le_mul_of_nonneg_left (sum_log_gap_majorant_le hq N) (by positivity)
    _ = _ := by dsimp only [C]; field_simp [hN0.ne', hc.ne', hT0.ne']

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sum_inv_sq_above_real_le

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.sum_upper_gap_majorant_le

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.abs_farCross_pair_tail_le
