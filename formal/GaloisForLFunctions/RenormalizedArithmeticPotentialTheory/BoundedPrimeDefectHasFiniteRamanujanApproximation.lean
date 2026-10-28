import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSmoothRoughMeanApproximatesBoundedDefect
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimeValuationBoxesCaptureBoundedDefect

/-!
# Uniform finite Ramanujan approximation at bounded prime defect

First suppress variation along rough fibres by increasing the prime threshold.
Then discard large retained valuations. The remaining conditional mean is a
gcd profile for a fixed modulus, hence lies in a fixed finite Ramanujan span.
Both choices are independent of the integer horizon and of the vector.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Uniform arithmetic compactness: bounded mass and defect admit approximation
by one fixed finite set of Ramanujan pole profiles at every horizon. -/
theorem exists_finite_ramanujan_approximation_of_poleDefect_le
    (K : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ N : ℕ, ∀ x : ℕ → ℝ,
        (∑ n ∈ Icc 1 N, x n ^ 2) ≤ 1 → poleDefect N x ≤ K →
        ∃ a : ℕ → ℝ,
          (∑ n ∈ Icc 1 N,
            (x n - ∑ m ∈ S, a m * ramanujanPoleProfile m n) ^ 2) ≤ η := by
  obtain ⟨C, hC, hmean⟩ := exists_smoothRoughPoleProjection_error_le
  obtain ⟨P, hP⟩ := exists_nat_gt (max 2 (Real.exp (2 * C * (K + 1) / η)))
  have hP2 : 2 ≤ P := by
    have h := (le_max_left (2 : ℝ) (Real.exp (2 * C * (K + 1) / η))).trans_lt hP
    exact_mod_cast h.le
  have hlog : 0 < Real.log P :=
    Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hlargeP : 2 * C * (K + 1) / η < Real.log P := by
    calc
      _ = Real.log (Real.exp (2 * C * (K + 1) / η)) := (Real.log_exp _).symm
      _ < Real.log P := Real.log_lt_log (Real.exp_pos _)
        ((le_max_right (2 : ℝ) _).trans_lt hP)
  have hPbound : C / Real.log P * K ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog]
    have h := (div_lt_iff₀ hη).mp hlargeP
    nlinarith only [h, hC]
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (2 * primeValuationTailConstant P * (K + 1) / η))
  have hL0 : 0 < L := by
    have h := (le_max_left (1 : ℝ) (2 * primeValuationTailConstant P * (K + 1) / η)).trans_lt hL
    exact_mod_cast (lt_trans zero_lt_one h)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
  have hLbound : primeValuationTailConstant P / (L : ℝ) * (K + 1) ≤ η / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hLR]
    have h := (div_lt_iff₀ hη).mp
      ((le_max_right (1 : ℝ) (2 * primeValuationTailConstant P * (K + 1) / η)).trans_lt hL)
    nlinarith only [h]
  let S := (primeValuationBoxModulus P L).divisors
  refine ⟨S, fun m hm => Nat.pos_of_mem_divisors hm, fun N x hmass hdef => ?_⟩
  obtain ⟨a, ha⟩ := exists_truncated_smoothProfile_normalizedRamanujan_expansion P L
    (smoothRoughMean P N x)
  refine ⟨a, ?_⟩
  have hprofile : ∀ n : ℕ, 0 < n →
      (if primeValuationBox P L n then smoothRoughPoleProjection P N x n else 0) =
        ∑ m ∈ S, a m * ramanujanPoleProfile m n := by
    intro n hn
    calc
      _ = (if primeValuationBox P L n then
          smoothRoughMean P N x (RHTower.Sieve.smoothPart (P - 1) n) else 0) / Real.sqrt n := by
        by_cases hbox : primeValuationBox P L n
        · rw [if_pos hbox, if_pos hbox]; rfl
        · rw [if_neg hbox, if_neg hbox, zero_div]
      _ = (∑ m ∈ S, a m * normalizedRamanujanMode m n) / Real.sqrt n := by rw [ha n hn]
      _ = _ := by
        rw [sum_div]
        exact sum_congr rfl fun m _ => by rw [ramanujanPoleProfile]; ring
  have herr : (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) ≤ η / 2 :=
    (hmean P hP2 N x).trans ((mul_le_mul_of_nonneg_left hdef
      (div_nonneg hC.le hlog.le)).trans hPbound)
  have htail : (∑ n ∈ Icc 1 N, if primeValuationBox P L n then 0 else x n ^ 2) ≤ η / 2 :=
    (sum_outside_primeValuationBox_le P N hL0 x).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hdef hmass)
        (div_nonneg (primeValuationTailConstant_nonneg P) hLR.le)).trans hLbound)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ((x n - smoothRoughPoleProjection P N x n) ^ 2 +
        if primeValuationBox P L n then 0 else x n ^ 2) := by
      refine sum_le_sum fun n hn => ?_
      rw [← hprofile n (mem_Icc.mp hn).1]
      by_cases hbox : primeValuationBox P L n
      · rw [if_pos hbox, if_pos hbox, add_zero]
      · rw [if_neg hbox, if_neg hbox, sub_zero]
        exact le_add_of_nonneg_left (sq_nonneg _)
    _ = (∑ n ∈ Icc 1 N, (x n - smoothRoughPoleProjection P N x n) ^ 2) +
        (∑ n ∈ Icc 1 N, if primeValuationBox P L n then 0 else x n ^ 2) := sum_add_distrib
    _ ≤ η / 2 + η / 2 := add_le_add herr htail
    _ = η := by ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
