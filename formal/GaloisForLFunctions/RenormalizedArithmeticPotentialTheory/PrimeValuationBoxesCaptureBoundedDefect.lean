import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimeDefectControlsValuationMoments
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ValuationBoxesAreFiniteRamanujanSpans

/-!
# Valuation boxes capture bounded-defect mass

Outside a valuation box at least one retained prime has valuation at least
the cutoff. Summing the exact prime-valuation moment bound therefore controls
the discarded squared mass by a finite constant divided by that cutoff.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The finite coefficient controlling all prime valuations below `P`. -/
def primeValuationTailConstant (P : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow P, (2 / Real.log p + 2 / ((p : ℝ) - 1))

theorem primeValuationTailConstant_nonneg (P : ℕ) : 0 ≤ primeValuationTailConstant P := by
  refine sum_nonneg fun p hp => ?_
  have hprime := (Nat.mem_primesBelow.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  exact add_nonneg (div_nonneg (by norm_num) (Real.log_pos hp1).le)
    (div_nonneg (by norm_num) (sub_pos.mpr hp1).le)

/-- A failed box condition exposes one large valuation. -/
theorem mul_sum_outside_primeValuationBox_le (P L N : ℕ) (x : ℕ → ℝ) :
    (L : ℝ) * (∑ n ∈ Icc 1 N, if primeValuationBox P L n then 0 else x n ^ 2) ≤
      ∑ p ∈ Nat.primesBelow P, ∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * x n ^ 2 := by
  rw [mul_sum, Finset.sum_comm]
  refine sum_le_sum fun n _ => ?_
  by_cases hbox : primeValuationBox P L n
  · rw [if_pos hbox, mul_zero]
    exact sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  · rw [if_neg hbox]
    simp only [primeValuationBox, not_forall, not_lt] at hbox
    obtain ⟨p, hp, hv⟩ := hbox
    calc (L : ℝ) * x n ^ 2 ≤ (n.factorization p : ℝ) * x n ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hv) (sq_nonneg _)
      _ ≤ ∑ q ∈ Nat.primesBelow P, (n.factorization q : ℝ) * x n ^ 2 :=
          single_le_sum (fun q _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hp

/-- The finite retained valuation moment is bounded by the actual prime defect and mass. -/
theorem sum_primeValuationMoment_le (P N : ℕ) (x : ℕ → ℝ) :
    (∑ p ∈ Nat.primesBelow P, ∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * x n ^ 2) ≤
      primeValuationTailConstant P * (poleDefect N x + ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hD : 0 ≤ poleDefect N x := poleDefect_nonneg N x
  have hX : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg _
  rw [primeValuationTailConstant, sum_mul]
  refine sum_le_sum fun p hp => ?_
  have hprime := (Nat.mem_primesBelow.mp hp).2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp1
  have hden : 0 < (p : ℝ) - 1 := sub_pos.mpr hp1
  have hm := log_mul_primeValuationMoment_le hprime N x
  have hm' : (∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * x n ^ 2) ≤
      2 / Real.log p * poleDefect N x +
        2 / ((p : ℝ) - 1) * (∑ n ∈ Icc 1 N, x n ^ 2) := by
    calc
      _ ≤ (2 * poleDefect N x +
          2 * (Real.log p / ((p : ℝ) - 1)) * (∑ n ∈ Icc 1 N, x n ^ 2)) / Real.log p :=
            (le_div_iff₀ hlog).mpr (by simpa only [mul_comm] using hm)
      _ = _ := by field_simp [hlog.ne', hden.ne']
  have h1 : 0 ≤ 2 / Real.log p := div_nonneg (by norm_num) hlog.le
  have h2 : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg (by norm_num) hden.le
  nlinarith only [hm', mul_nonneg h1 hX, mul_nonneg h2 hD]

/-- The discarded valuation-box mass tends to zero as the exponent cutoff grows. -/
theorem sum_outside_primeValuationBox_le (P N : ℕ) {L : ℕ} (hL : 0 < L) (x : ℕ → ℝ) :
    (∑ n ∈ Icc 1 N, if primeValuationBox P L n then 0 else x n ^ 2) ≤
      primeValuationTailConstant P / (L : ℝ) *
        (poleDefect N x + ∑ n ∈ Icc 1 N, x n ^ 2) := by
  have h := (mul_sum_outside_primeValuationBox_le P L N x).trans
    (sum_primeValuationMoment_le P N x)
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  rw [div_mul_eq_mul_div, le_div_iff₀ hLR]
  simpa only [mul_comm] using h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
