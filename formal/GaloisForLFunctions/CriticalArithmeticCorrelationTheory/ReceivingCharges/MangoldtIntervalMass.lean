import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeightedAffinePrimeWindowsAreUniform

/-!
# Reciprocal Mangoldt mass on the literal multiplier interval

A bounded supported kernel costs only its amplitude and logarithmic
interval width. Summing an offset family adds its exact strip cardinality.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The left endpoint costs at most one additional reciprocal Mangoldt unit. -/
theorem sum_Icc_vonMangoldt_div_le {H X : ℕ} (hH : 1 ≤ H) (hHX : H ≤ X) :
    (∑ k ∈ Icc H X, vonMangoldt k / (k : ℝ)) ≤
      Real.log X - Real.log H + mertensWindowConstant + 1 := by
  have hset : Icc H X = insert H (Ioc H X) := by
    ext k
    simp only [mem_Icc, mem_insert, mem_Ioc]
    omega
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hend : vonMangoldt H / (H : ℝ) ≤ 1 := by
    apply (div_le_one hH0).mpr
    have hlog := Real.log_le_sub_one_of_pos hH0
    exact vonMangoldt_le_log.trans (by linarith only [hlog])
  rw [hset, sum_insert (by simp only [mem_Ioc, lt_self_iff_false, false_and, not_false_eq_true])]
  exact (add_le_add hend (sum_Ioc_vonMangoldt_div_le hH hHX)).trans_eq (by ring)

/-- Restricting a bounded kernel to its true multiplier interval retains only logarithmic mass. -/
theorem weighted_mangoldt_interval_mass {H X Y : ℕ} (hH : 1 ≤ H) (hHX : H ≤ X)
    (f : ℕ → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hf : ∀ k ∈ Icc 1 Y, |f k| ≤ U)
    (hsupp : ∀ k ∈ Icc 1 Y, f k ≠ 0 → k ∈ Icc H X) :
    (∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * |f k|) ≤
      U * (Real.log X - Real.log H + mertensWindowConstant + 1) := by
  have hterm (k : ℕ) (hk : k ∈ Icc 1 Y) :
      (vonMangoldt k / (k : ℝ)) * |f k| ≤
        if k ∈ Icc H X then U * (vonMangoldt k / (k : ℝ)) else 0 := by
    by_cases hmem : k ∈ Icc H X
    · rw [if_pos hmem]
      exact (mul_le_mul_of_nonneg_left (hf k hk)
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans_eq (mul_comm _ _)
    · have hz : f k = 0 := by by_contra hn; exact hmem (hsupp k hk hn)
      simp only [hz, abs_zero, mul_zero, if_neg hmem, le_refl]
  calc
    _ ≤ ∑ k ∈ Icc 1 Y, if k ∈ Icc H X then U * (vonMangoldt k / (k : ℝ)) else 0 :=
      sum_le_sum hterm
    _ = ∑ k ∈ (Icc 1 Y).filter (fun k => k ∈ Icc H X), U * (vonMangoldt k / (k : ℝ)) := by
      rw [sum_filter]
    _ ≤ ∑ k ∈ Icc H X, U * (vonMangoldt k / (k : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg (fun k hk => (mem_filter.mp hk).2)
      intro k _ _
      exact mul_nonneg hU (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
    _ = U * ∑ k ∈ Icc H X, vonMangoldt k / (k : ℝ) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_Icc_vonMangoldt_div_le hH hHX) hU

/-- A supported finite offset family costs its strip cardinality and logarithmic multiplier width. -/
theorem double_mangoldt_supported_sum_le {H X Y B : ℕ} (hH : 1 ≤ H)
    (f : ℕ → ℕ → ℝ) {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hf : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U)
    (hsupp : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, f k h ≠ 0 → k ∈ Icc H X)
    (hwidth : H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W) :
    |∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * ∑ h ∈ Icc 1 B, f k h| ≤
      (B : ℝ) * U * W := by
  have hexpand :
      (∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * ∑ h ∈ Icc 1 B, f k h) =
        ∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * f k h := by
    simp only [mul_sum]
    rw [sum_comm]
  rw [hexpand]
  by_cases hHX : H ≤ X
  · have hterm (h : ℕ) (hh : h ∈ Icc 1 B) :
        |∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * f k h| ≤ U * W := by
      calc
        _ ≤ ∑ k ∈ Icc 1 Y, |(vonMangoldt k / (k : ℝ)) * f k h| := abs_sum_le_sum_abs _ _
        _ = ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * |f k h| := by
          apply sum_congr rfl
          intro k _
          rw [abs_mul, abs_of_nonneg (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))]
        _ ≤ U * (Real.log X - Real.log H + mertensWindowConstant + 1) :=
          weighted_mangoldt_interval_mass hH hHX (fun k => f k h) hU
            (fun k hk => hf k hk h hh) (fun k hk => hsupp k hk h hh)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hwidth hHX) hU
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans_eq ?_)
    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  · have hz (h : ℕ) (hh : h ∈ Icc 1 B) (k : ℕ) (hk : k ∈ Icc 1 Y) : f k h = 0 := by
      by_contra hne
      have hm := mem_Icc.mp (hsupp k hk h hh hne)
      exact hHX (hm.1.trans hm.2)
    have hsum : (∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * f k h) = 0 := by
      apply sum_eq_zero
      intro h hh
      apply sum_eq_zero
      intro k hk
      rw [hz h hh k hk, mul_zero]
    rw [hsum, abs_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg B) hU) hW

#print axioms double_mangoldt_supported_sum_le

#print axioms sum_Icc_vonMangoldt_div_le
#print axioms weighted_mangoldt_interval_mass

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
