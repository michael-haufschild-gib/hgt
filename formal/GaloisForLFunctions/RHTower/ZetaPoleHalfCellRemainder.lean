import GaloisForLFunctions.HTGeometry.PoleHalfKernelCellOscillation
import GaloisForLFunctions.RHTower.ZetaPoleHalfCausalSource
import Mathlib.Analysis.PSeries

/-!
# Summable cell remainder of the actual zeta-half source

On each logarithmic integer cell, retain the old atoms' right-endpoint value as
an explicit baseline. The remaining absolute mass has a uniform weighted prefix
bound, hence is summable at every exponent greater than one half.
The argument uses the actual zeta-half coefficients. It does not bound the baseline
or assert analytic continuation of a root.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def zetaPoleHalfCellWidth (N : ℕ) : ℝ := Real.log (N + 1 : ℕ) - Real.log N

def zetaPoleHalfCellBaseline (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N, (zetaBinomialHalf n).re *
    poleClearedHalfKernel (Real.log (N + 1 : ℕ) - Real.log n)

private theorem erase_cell_last (N : ℕ) :
    (Finset.Icc 1 N).erase N = Finset.Ico 1 N := by
  ext n
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
  omega

theorem zetaPoleHalfCellWidth_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < zetaPoleHalfCellWidth N := by
  apply sub_pos.mpr
  exact Real.log_lt_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
    (by exact_mod_cast Nat.lt_succ_self N)

theorem zetaPoleHalfCellWidth_le_inv {N : ℕ} (hN : 1 ≤ N) :
    zetaPoleHalfCellWidth N ≤ (N : ℝ)⁻¹ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hn1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn1 hn)
  rw [Real.log_div hn1.ne' hn.ne'] at h
  change Real.log (N + 1 : ℕ) - Real.log N ≤ _
  convert h using 1
  push_cast
  field_simp
  ring

theorem zetaPoleHalfCellWidth_le_one {N : ℕ} (hN : 1 ≤ N) :
    zetaPoleHalfCellWidth N ≤ 1 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (zetaPoleHalfCellWidth_le_inv hN).trans (inv_le_one_of_one_le₀ hn)

theorem zetaPoleHalfCausalSource_cell_decomposition {N : ℕ} (hN : 1 ≤ N)
    {x : ℝ} (hx : x ∈ Ioo 0 (zetaPoleHalfCellWidth N)) :
    zetaPoleHalfCausalSource (Real.log N + x) =
      zetaPoleHalfCellBaseline N + (zetaBinomialHalf N).re * poleClearedHalfKernel x +
        ∑ n ∈ Finset.Ico 1 N, (zetaBinomialHalf n).re *
          (poleClearedHalfKernel (x + (Real.log N - Real.log n)) -
            poleClearedHalfKernel (Real.log (N + 1 : ℕ) - Real.log n)) := by
  rw [zetaPoleHalfCausalSource_eq_prefix hN hx]
  unfold zetaPoleHalfCausalPrefix zetaPoleHalfCellBaseline
  rw [← Finset.sum_erase_add _ _ (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩),
    erase_cell_last]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [sub_self, add_zero]
  ring

theorem zetaPoleHalfCausalSource_cell_remainder_mass_upper {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (0 : ℝ)..(zetaPoleHalfCellWidth N),
      |zetaPoleHalfCausalSource (Real.log N + x) - zetaPoleHalfCellBaseline N|) ≤
      6 * (zetaBinomialHalf N).re * Real.exp (zetaPoleHalfCellWidth N) *
        (zetaPoleHalfCellWidth N) ^ ((1 : ℝ) / 2) +
      zetaPoleHalfCellWidth N * ∑ n ∈ Finset.Ico 1 N,
        (zetaBinomialHalf n).re * Real.exp (Real.log (N + 1 : ℕ) - Real.log n) *
          ((Real.log N - Real.log n) ^ (-(1 : ℝ) / 2) -
            (Real.log (N + 1 : ℕ) - Real.log n) ^ (-(1 : ℝ) / 2)) := by
  have hd := zetaPoleHalfCellWidth_pos hN
  have h := poleClearedHalfPacket_remainder_mass_upper (Finset.Icc 1 N)
    (fun n : ℕ => Real.log N - Real.log n) (fun n : ℕ => (zetaBinomialHalf n).re)
    (j := N) (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩)
    (fun n hn => by
      rw [erase_cell_last] at hn
      have hn' := Finset.mem_Ico.mp hn
      apply sub_pos.mpr
      exact Real.log_lt_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn'.1))
        (by exact_mod_cast hn'.2))
    (fun n _ => zetaBinomialHalf_apply_nonneg n) (sub_self _)
    hd (zetaPoleHalfCellWidth_le_one hN)
  rw [erase_cell_last] at h
  have heq : ∀ n : ℕ, zetaPoleHalfCellWidth N + (Real.log N - Real.log n) =
      Real.log (N + 1 : ℕ) - Real.log n := fun n => by
    unfold zetaPoleHalfCellWidth
    ring
  simp_rw [heq] at h
  have hint : (∫ x in (0 : ℝ)..(zetaPoleHalfCellWidth N),
      |zetaPoleHalfCausalSource (Real.log N + x) - zetaPoleHalfCellBaseline N|) =
    ∫ x in (0 : ℝ)..(zetaPoleHalfCellWidth N),
      |(∑ n ∈ Finset.Icc 1 N, (zetaBinomialHalf n).re *
        poleClearedHalfKernel (x + (Real.log N - Real.log n))) -
        zetaPoleHalfCellBaseline N| := by
    rw [intervalIntegral.integral_of_le hd.le, intervalIntegral.integral_of_le hd.le,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp only
    rw [zetaPoleHalfCausalSource_eq_prefix hN hx]
    rfl
  rw [hint]
  exact h

theorem zetaPoleHalfCellWidth_inv_lower {N : ℕ} (hN : 1 ≤ N) :
    ((N + 1 : ℕ) : ℝ)⁻¹ ≤ zetaPoleHalfCellWidth N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hn1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1 hn)
  rw [Real.log_div hn1.ne' hn.ne'] at h
  change _ ≤ Real.log (N + 1 : ℕ) - Real.log N
  convert h using 1
  push_cast
  field_simp
  ring

theorem exp_zetaPoleHalfCellWidth_le_two {N : ℕ} (hN : 1 ≤ N) :
    Real.exp (zetaPoleHalfCellWidth N) ≤ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hn1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [zetaPoleHalfCellWidth, Real.exp_sub, Real.exp_log hn1, Real.exp_log hn]
  apply (div_le_iff₀ hn).mpr
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  linarith

theorem zetaPoleHalfCellWidth_mul_succ_le_two {N : ℕ} (hN : 1 ≤ N) :
    zetaPoleHalfCellWidth N * (N + 1 : ℕ) ≤ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hn1 : (0 : ℝ) ≤ (N + 1 : ℕ) := by positivity
  have hi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hN)
  calc
    _ ≤ (N : ℝ)⁻¹ * (N + 1 : ℕ) :=
      mul_le_mul_of_nonneg_right (zetaPoleHalfCellWidth_le_inv hN) hn1
    _ = 1 + (N : ℝ)⁻¹ := by push_cast; field_simp
    _ ≤ 2 := by linarith

def zetaPoleHalfCellIncrement (n N : ℕ) : ℝ :=
  (Real.log N - Real.log n) ^ (-(1 : ℝ) / 2) -
    (Real.log (N + 1 : ℕ) - Real.log n) ^ (-(1 : ℝ) / 2)

theorem zetaPoleHalfCellIncrement_nonneg {n N : ℕ} (hn : 1 ≤ n) (hnN : n < N) :
    0 ≤ zetaPoleHalfCellIncrement n N := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hn.trans hnN.le))
  apply sub_nonneg.mpr
  apply Real.rpow_le_rpow_of_nonpos
    (sub_pos.mpr (Real.log_lt_log hnp (by exact_mod_cast hnN)))
  · exact sub_le_sub_right
      (Real.log_le_log hNp (by exact_mod_cast Nat.le_succ N)) _
  · norm_num

theorem zetaPoleHalfCausalSource_cell_remainder_mass_le {N : ℕ} (hN : 1 ≤ N) :
    (∫ x in (0 : ℝ)..(zetaPoleHalfCellWidth N),
      |zetaPoleHalfCausalSource (Real.log N + x) - zetaPoleHalfCellBaseline N|) ≤
      12 * (zetaBinomialHalf N).re * (zetaPoleHalfCellWidth N) ^ ((1 : ℝ) / 2) +
        2 * ∑ n ∈ Finset.Ico 1 N, (zetaBinomialHalf n).re / n *
          zetaPoleHalfCellIncrement n N := by
  apply (zetaPoleHalfCausalSource_cell_remainder_mass_upper hN).trans
  apply add_le_add
  · have h := mul_le_mul_of_nonneg_right (exp_zetaPoleHalfCellWidth_le_two hN)
      (show 0 ≤ 6 * (zetaBinomialHalf N).re *
        (zetaPoleHalfCellWidth N) ^ ((1 : ℝ) / 2) from
        mul_nonneg (mul_nonneg (by norm_num) (zetaBinomialHalf_apply_nonneg N))
          (Real.rpow_nonneg (zetaPoleHalfCellWidth_pos hN).le _))
    nlinarith
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn'.1)
    have hNp1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hf : zetaPoleHalfCellWidth N *
        Real.exp (Real.log (N + 1 : ℕ) - Real.log n) ≤ 2 / n := by
      rw [Real.exp_sub, Real.exp_log hNp1, Real.exp_log hnp, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (zetaPoleHalfCellWidth_mul_succ_le_two hN) hnp.le
    have h := mul_le_mul_of_nonneg_right hf
      (mul_nonneg (zetaBinomialHalf_apply_nonneg n)
        (zetaPoleHalfCellIncrement_nonneg hn'.1 hn'.2))
    dsimp only [zetaPoleHalfCellIncrement] at h ⊢
    convert h using 1 <;> ring

theorem zetaPoleHalfCellIncrement_sum_le {n M : ℕ} (hn : 1 ≤ n) (hnM : n < M) :
    (∑ N ∈ Finset.Ico (n + 1) M, zetaPoleHalfCellIncrement n N) ≤
      (zetaPoleHalfCellWidth n) ^ (-(1 : ℝ) / 2) := by
  let q : ℕ → ℝ := fun N => (Real.log N - Real.log n) ^ (-(1 : ℝ) / 2)
  have ht : (∑ N ∈ Finset.Ico (n + 1) M, (q N - q (N + 1))) =
      q (n + 1) - q M := by
    have h := Finset.sum_Ico_eq_sub (fun N => (-q (N + 1)) - (-q N)) hnM
    rw [Finset.sum_range_sub (fun N => -q N), Finset.sum_range_sub (fun N => -q N)] at h
    simp only [neg_sub_neg] at h
    linarith
  change (∑ N ∈ Finset.Ico (n + 1) M, (q N - q (N + 1))) ≤ q (n + 1)
  rw [ht]
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hq : 0 ≤ q M := Real.rpow_nonneg
    (sub_nonneg.mpr (Real.log_le_log hnp (by exact_mod_cast hnM.le))) _
  linarith

theorem zetaPoleHalfCellWidth_sqrt_upper {N : ℕ} (hN : 1 ≤ N) :
    (zetaPoleHalfCellWidth N) ^ ((1 : ℝ) / 2) ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hn : (0 : ℝ) ≤ N := by positivity
  have h := Real.rpow_le_rpow (zetaPoleHalfCellWidth_pos hN).le
    (zetaPoleHalfCellWidth_le_inv hN) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.inv_rpow hn, ← Real.rpow_neg hn] at h
  simpa only [neg_div] using h

theorem zetaPoleHalfCellWidth_invSqrt_upper {N : ℕ} (hN : 1 ≤ N) :
    (zetaPoleHalfCellWidth N) ^ (-(1 : ℝ) / 2) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
  have hn : (0 : ℝ) ≤ N := by positivity
  have hn1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have h := Real.rpow_le_rpow_of_nonpos (inv_pos.mpr hn1)
    (zetaPoleHalfCellWidth_inv_lower hN) (by norm_num : -(1 : ℝ) / 2 ≤ 0)
  rw [Real.inv_rpow hn1.le, ← Real.rpow_neg hn1.le] at h
  norm_num only [neg_div, neg_neg] at h
  simp only [neg_div]
  apply h.trans
  have hnr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : ((N + 1 : ℕ) : ℝ) ≤ 4 * N := by push_cast; linarith
  have hp := Real.rpow_le_rpow hn1.le hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [Real.mul_rpow (by norm_num) hn] at hp
  have hfour : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
  rwa [hfour] at hp

theorem zetaPoleHalfCellIncrement_weighted_sum_le {n M : ℕ} (hn : 1 ≤ n)
    (hnM : n < M) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ N ∈ Finset.Ico (n + 1) M, (N : ℝ) ^ (-σ) *
      ((zetaBinomialHalf n).re / n * zetaPoleHalfCellIncrement n N)) ≤
        2 * (zetaBinomialHalf n).re * (n : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hc : 0 ≤ (n : ℝ) ^ (-σ) * ((zetaBinomialHalf n).re / n) :=
    mul_nonneg (Real.rpow_nonneg hnp.le _) (div_nonneg (zetaBinomialHalf_apply_nonneg n) hnp.le)
  calc
    _ ≤ ∑ N ∈ Finset.Ico (n + 1) M, (n : ℝ) ^ (-σ) *
        ((zetaBinomialHalf n).re / n * zetaPoleHalfCellIncrement n N) := by
      apply Finset.sum_le_sum
      intro N hN
      have hnN : n < N := (Finset.mem_Ico.mp hN).1
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hnp (by exact_mod_cast hnN.le) (neg_nonpos.mpr hσ))
        (mul_nonneg (div_nonneg (zetaBinomialHalf_apply_nonneg n) hnp.le)
          (zetaPoleHalfCellIncrement_nonneg hn hnN))
    _ = ((n : ℝ) ^ (-σ) * ((zetaBinomialHalf n).re / n)) *
        ∑ N ∈ Finset.Ico (n + 1) M, zetaPoleHalfCellIncrement n N := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      ring
    _ ≤ ((n : ℝ) ^ (-σ) * ((zetaBinomialHalf n).re / n)) *
        (2 * (n : ℝ) ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left
        ((zetaPoleHalfCellIncrement_sum_le hn hnM).trans (zetaPoleHalfCellWidth_invSqrt_upper hn)) hc
    _ = _ := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        _ = (2 * (zetaBinomialHalf n).re) *
          (((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-1 : ℝ)) * (n : ℝ) ^ ((1 : ℝ) / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add hnp, ← Real.rpow_add hnp]
          congr 2
          ring

def zetaPoleHalfCellRemainderMass (N : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..(zetaPoleHalfCellWidth N),
    |zetaPoleHalfCausalSource (Real.log N + x) - zetaPoleHalfCellBaseline N|

theorem zetaPoleHalfCellRemainderMass_weighted_prefix_le (M : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    (∑ N ∈ Finset.Ico 1 M, (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N) ≤
      16 * ∑ N ∈ Finset.Ico 1 M,
        (zetaBinomialHalf N).re * (N : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
  have hcell : ∀ N ∈ Finset.Ico 1 M,
      (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N ≤
        12 * ((zetaBinomialHalf N).re * (N : ℝ) ^ (-σ - (1 : ℝ) / 2)) +
        2 * ∑ n ∈ Finset.Ico 1 N, (N : ℝ) ^ (-σ) *
          ((zetaBinomialHalf n).re / n * zetaPoleHalfCellIncrement n N) := by
    intro N hN
    have hN1 := (Finset.mem_Ico.mp hN).1
    have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
    have h := mul_le_mul_of_nonneg_left (zetaPoleHalfCausalSource_cell_remainder_mass_le hN1)
      (Real.rpow_nonneg hNp.le (-σ))
    have hnew := mul_le_mul_of_nonneg_left (zetaPoleHalfCellWidth_sqrt_upper hN1)
      (mul_nonneg (Real.rpow_nonneg hNp.le (-σ))
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) (zetaBinomialHalf_apply_nonneg N)))
    have hprod : (N : ℝ) ^ (-σ) * (N : ℝ) ^ (-(1 : ℝ) / 2) =
        (N : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
      rw [← Real.rpow_add hNp]
      congr 1
      ring
    have hnew' : (N : ℝ) ^ (-σ) *
        (12 * (zetaBinomialHalf N).re * (zetaPoleHalfCellWidth N) ^ ((1 : ℝ) / 2)) ≤
        12 * ((zetaBinomialHalf N).re * (N : ℝ) ^ (-σ - (1 : ℝ) / 2)) := by
      rw [← hprod]
      nlinarith
    have heq : (N : ℝ) ^ (-σ) * (2 * ∑ n ∈ Finset.Ico 1 N,
        (zetaBinomialHalf n).re / n * zetaPoleHalfCellIncrement n N) =
      2 * ∑ n ∈ Finset.Ico 1 N, (N : ℝ) ^ (-σ) *
        ((zetaBinomialHalf n).re / n * zetaPoleHalfCellIncrement n N) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [mul_add, heq] at h
    exact h.trans (add_le_add hnew' le_rfl)
  have h := Finset.sum_le_sum hcell
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_Ico_Ico_comm' 1 M] at h
  have hold := Finset.sum_le_sum (fun n (hn : n ∈ Finset.Ico 1 M) =>
    zetaPoleHalfCellIncrement_weighted_sum_le (Finset.mem_Ico.mp hn).1
      (Finset.mem_Ico.mp hn).2 hσ)
  have heq : (∑ n ∈ Finset.Ico 1 M,
      2 * (zetaBinomialHalf n).re * (n : ℝ) ^ (-σ - (1 : ℝ) / 2)) =
    2 * ∑ n ∈ Finset.Ico 1 M, (zetaBinomialHalf n).re * (n : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [heq] at hold
  linarith

theorem zetaPoleHalfCellRemainderMass_nonneg (N : ℕ) :
    0 ≤ zetaPoleHalfCellRemainderMass N := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [zetaPoleHalfCellRemainderMass, zetaPoleHalfCellWidth]
  · exact intervalIntegral.integral_nonneg_of_forall
      (zetaPoleHalfCellWidth_pos (Nat.one_le_iff_ne_zero.mpr hN)).le (fun x => abs_nonneg _)

theorem zetaPoleHalfCellRemainderMass_weighted_summable {σ : ℝ} (hσ : (1 : ℝ) / 2 < σ) :
    Summable (fun N : ℕ => (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N) ∧
      (∑' N : ℕ, (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N) ≤
        16 * ∑' N : ℕ, (N : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
  have hσ0 : 0 ≤ σ := by linarith
  have hs : Summable (fun N : ℕ => (N : ℝ) ^ (-σ - (1 : ℝ) / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hb : ∀ M : ℕ,
      (∑ N ∈ Finset.Ico 1 M, (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N) ≤
        16 * ∑' N : ℕ, (N : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
    intro M
    apply (zetaPoleHalfCellRemainderMass_weighted_prefix_le M hσ0).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply (Finset.sum_le_sum (fun N (_ : N ∈ Finset.Ico 1 M) => ?_)).trans
      (hs.sum_le_tsum (Finset.Ico 1 M) (fun N _ => Real.rpow_nonneg (Nat.cast_nonneg N) _))
    calc
      (zetaBinomialHalf N).re * (N : ℝ) ^ (-σ - (1 : ℝ) / 2) ≤
          1 * (N : ℝ) ^ (-σ - (1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right
          ((Complex.re_le_norm _).trans (norm_zetaBinomialHalf_le_one N))
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ = _ := one_mul _
  have hn : ∀ N : ℕ, 0 ≤ (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N :=
    fun N => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (zetaPoleHalfCellRemainderMass_nonneg N)
  have hzero : (0 : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass 0 = 0 := by
    simp [zetaPoleHalfCellRemainderMass, zetaPoleHalfCellWidth]
  have hr : ∀ M : ℕ,
      (∑ N ∈ Finset.range M, (N : ℝ) ^ (-σ) * zetaPoleHalfCellRemainderMass N) ≤
        16 * ∑' N : ℕ, (N : ℝ) ^ (-σ - (1 : ℝ) / 2) := by
    intro M
    rcases eq_or_ne M 0 with rfl | hM
    · simpa using hb 0
    · rw [Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hM), Nat.cast_zero, hzero, zero_add]
      exact hb M
  exact ⟨summable_of_sum_range_le hn hr, Real.tsum_le_of_sum_range_le hn hr⟩

end RHTower

