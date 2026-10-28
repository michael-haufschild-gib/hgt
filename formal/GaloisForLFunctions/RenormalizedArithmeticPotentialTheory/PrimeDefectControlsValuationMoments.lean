import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimePowerMangoldtReindex

/-!
# Prime defect controls valuation moments

Each integer is the top of exactly its prime valuation many prime-power edges.
The elementary square inequality bounds its weighted mass by edge defects and
the summable geometric mass at the bottoms of those edges.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- A prime valuation cannot carry large squared mass at bounded pole defect. -/
theorem log_mul_primeValuationMoment_le {p : ℕ} (hp : p.Prime)
    (N : ℕ) (x : ℕ → ℝ) :
    Real.log p * (∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * x n ^ 2) ≤
      2 * poleDefect N x +
        2 * (Real.log p / ((p : ℝ) - 1)) * (∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hcount :
      (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m),
        if p ∣ t then x (m * t) ^ 2 * Λ t else 0) =
      Real.log p * (∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * x n ^ 2) := by
    rw [sum_edges_eq_sum_divisors N (fun n t => if p ∣ t then x n ^ 2 * Λ t else 0),
      mul_sum]
    refine sum_congr rfl fun n hn => ?_
    rw [sum_divisors_primePower_mangoldt hp
      (Nat.one_le_iff_ne_zero.mp (mem_Icc.mp hn).1) (fun _ => x n ^ 2)]
    simp only [sum_const, card_range, nsmul_eq_mul]
    ring
  have hbottom : ∀ m,
      (∑ t ∈ Icc 1 (N / m), if p ∣ t then (x m / Real.sqrt t) ^ 2 * Λ t else 0) ≤
        (Real.log p / ((p : ℝ) - 1)) * x m ^ 2 := by
    intro m
    have heq :
        (∑ t ∈ Icc 1 (N / m), if p ∣ t then (x m / Real.sqrt t) ^ 2 * Λ t else 0) =
          x m ^ 2 * (∑ t ∈ Icc 1 (N / m), if p ∣ t then Λ t / (t : ℝ) else 0) := by
      rw [mul_sum]
      refine sum_congr rfl fun t _ => ?_
      by_cases hpt : p ∣ t
      · rw [if_pos hpt, if_pos hpt, div_pow, Real.sq_sqrt (Nat.cast_nonneg t)]
        ring
      · rw [if_neg hpt, if_neg hpt, mul_zero]
    rw [heq, mul_comm (Real.log p / ((p : ℝ) - 1))]
    exact mul_le_mul_of_nonneg_left (sum_dvd_vonMangoldt_div_le hp _) (sq_nonneg _)
  have hedge (m t : ℕ) :
      (if p ∣ t then x (m * t) ^ 2 * Λ t else 0) ≤
        2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          2 * (if p ∣ t then (x m / Real.sqrt t) ^ 2 * Λ t else 0) := by
    by_cases hpt : p ∣ t
    · rw [if_pos hpt, if_pos hpt]
      have hs : x (m * t) ^ 2 ≤
          2 * (x (m * t) - x m / Real.sqrt t) ^ 2 +
            2 * (x m / Real.sqrt t) ^ 2 := by
        nlinarith only [sq_nonneg (x (m * t) - 2 * (x m / Real.sqrt t))]
      calc x (m * t) ^ 2 * Λ t ≤
          (2 * (x (m * t) - x m / Real.sqrt t) ^ 2 +
            2 * (x m / Real.sqrt t) ^ 2) * Λ t :=
            mul_le_mul_of_nonneg_right hs vonMangoldt_nonneg
        _ = _ := by ring
    · rw [if_neg hpt, if_neg hpt, mul_zero, add_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg vonMangoldt_nonneg (sq_nonneg _))
  rw [← hcount, poleDefect, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun m _ => ?_
  calc (∑ t ∈ Icc 1 (N / m), if p ∣ t then x (m * t) ^ 2 * Λ t else 0) ≤
      ∑ t ∈ Icc 1 (N / m),
        (2 * (Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
          2 * (if p ∣ t then (x m / Real.sqrt t) ^ 2 * Λ t else 0)) :=
        sum_le_sum fun t _ => hedge m t
    _ = 2 * (∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2) +
        2 * (∑ t ∈ Icc 1 (N / m),
          if p ∣ t then (x m / Real.sqrt t) ^ 2 * Λ t else 0) := by
      rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (hbottom m) (show (0 : ℝ) ≤ 2 by norm_num)
      linarith only [h]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

