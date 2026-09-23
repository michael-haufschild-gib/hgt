import GaloisForLFunctions.RHTower.Sieve.SquarefreeDyadicDensity

/-!
# The squarefree count up to `m`

The window estimate is uniform in the starting point, so taking the starting point to be `0` and the
truncation parameter to be `⌊√m⌋ + 1` — the least `R` with `m ≤ R²` — gives

    | #{n ≤ m : n squarefree} − m·D |  ≤  2√m + 1,      D = 6/π².

The two halves of the error balance exactly: `R ≤ √m + 1` and `m/R ≤ √m`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The counting range from `1`. -/
theorem Ioc_zero_eq_Icc_one (m : ℕ) : Finset.Ioc 0 m = Finset.Icc 1 m := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- **The squarefree count up to `m`, with square-root error.** -/
theorem abs_sum_moebius_sq_Icc_sub_le (m : ℕ) :
    |∑ n ∈ Finset.Icc 1 m, ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) - (m : ℝ) * squarefreeDensity|
      ≤ 2 * Real.sqrt m + 1 := by
  have hR1 : 1 ≤ Nat.sqrt m + 1 := by omega
  have hRM : 0 + m ≤ (Nat.sqrt m + 1) ^ (2 : ℕ) := by
    have h := Nat.lt_succ_sqrt' m
    rw [zero_add]
    have hs : Nat.sqrt m + 1 = Nat.succ (Nat.sqrt m) := rfl
    rw [hs]
    exact le_of_lt h
  have hbase := abs_window_squarefree_sub_le (t := 0) (L := m) (R := Nat.sqrt m + 1) hR1 hRM
  rw [zero_add, Ioc_zero_eq_Icc_one] at hbase
  refine le_trans hbase ?_
  have hs0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hRle : ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ Real.sqrt m + 1 := by
    have := natSqrt_le_sqrt m
    push_cast
    linarith
  have hRgt : Real.sqrt m < ((Nat.sqrt m + 1 : ℕ) : ℝ) := sqrt_lt_natSqrt_succ m
  have hRpos : (0 : ℝ) < ((Nat.sqrt m + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) := by exact_mod_cast hR1
    linarith
  have hquot : (m : ℝ) / ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ Real.sqrt m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hspos : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hm0
      rw [div_le_iff₀ hRpos]
      have hsq : Real.sqrt m * Real.sqrt m = (m : ℝ) := Real.mul_self_sqrt (le_of_lt hm0)
      nlinarith
  linarith

end RHTower.Sieve
