import GaloisForLFunctions.RHTower.Sieve.SquarefreeTruncationDefect
import GaloisForLFunctions.RHTower.Sieve.SquarefreeCount

/-!
# The squarefree count of a window, with no truncation defect

Truncating `μ²(n) = ∑_{d² ∣ n} μ(d)` at `R` costs nothing once `R² ≥ t + L`: a divisor `d > R` has
`d² > R² ≥ n`, and `d² ∣ n` with `n ≥ 1` forces `d² ≤ n`.  So the truncated estimate is an estimate
for the squarefree count itself:

    | #{n ∈ (t, t+L] : n squarefree} - L·D | ≤ R + L/R,   D = 6/π²,

uniformly in the starting point `t`, for any `R` with `1 ≤ R` and `t + L ≤ R²`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Above the square root of the range there are no square divisors. -/
theorem filter_sq_dvd_high_eq_empty {t L R d : ℕ} (hd : R + 1 ≤ d) (hR : t + L ≤ R ^ (2 : ℕ)) :
    ((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 ?_
  intro n hn hdvd
  rw [Finset.mem_Ioc] at hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le t) hn.1
  have hle : d ^ (2 : ℕ) ≤ n := Nat.le_of_dvd hn0 hdvd
  have hRd : R ^ (2 : ℕ) < d ^ (2 : ℕ) := by
    have : R < d := by omega
    exact Nat.pow_lt_pow_left this (by norm_num)
  omega

/-- **The squarefree window count.**  With `R² ≥ t + L` the truncation is exact. -/
theorem abs_window_squarefree_sub_le {t L R : ℕ} (hR : 1 ≤ R) (hRM : t + L ≤ R ^ (2 : ℕ)) :
    |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ) - (L : ℝ) * squarefreeDensity|
      ≤ (R : ℝ) + (L : ℝ) / (R : ℝ) := by
  classical
  have hdefect := abs_window_squarefree_sub_trunc_le t L R (t + L) (le_refl _)
  have hzero : ∑ d ∈ Finset.Icc (R + 1) (t + L),
      ((((Finset.Ioc t (t + L)).filter (fun n => d ^ (2 : ℕ) ∣ n)).card : ℕ) : ℝ) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [filter_sq_dvd_high_eq_empty hd.1 hRM]
    simp
  rw [hzero] at hdefect
  have htrunc := abs_truncated_squarefree_sub_le t L R hR
  have hsplit : |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
        - (L : ℝ) * squarefreeDensity|
      ≤ |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)
          - ∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ)|
        + |∑ n ∈ Finset.Ioc t (t + L),
              ∑ d ∈ (Finset.Icc 1 R).filter (fun d => d ^ (2 : ℕ) ∣ n), ((moebius d : ℤ) : ℝ)
            - (L : ℝ) * squarefreeDensity| :=
    abs_sub_le _ _ _
  linarith

end RHTower.Sieve
