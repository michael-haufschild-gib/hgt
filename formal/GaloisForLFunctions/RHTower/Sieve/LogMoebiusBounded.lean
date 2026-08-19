import GaloisForLFunctions.RHTower.Sieve.HarmonicFloorDefect
import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange

/-!
# The logarithmic Möbius sum is bounded

Assembling the exact identity of `sum_moebius_log_div_eq_one_sub_error` with the pointwise defect
bound and the tree's `|∑_{d ≤ N} μ(d)/d| ≤ 1` gives an explicit `O(1)` bound for
`∑_{d ≤ N} μ(d) log(N/d)/d`.  This is Graham's step six.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **Graham step six.**  The logarithmic Möbius sum is bounded by an absolute constant. -/
theorem abs_sum_moebius_log_div_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) * Real.log ((N : ℝ) / (d : ℝ))|
      ≤ 5 + |Real.eulerMascheroniConstant| := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hbase := sum_moebius_log_div_eq_one_sub_error N hN
  have hsplit : (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))))
      = Real.eulerMascheroniConstant *
          (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ))
        + ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
            - Real.eulerMascheroniConstant) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hgamma : |Real.eulerMascheroniConstant *
      (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ))|
      ≤ |Real.eulerMascheroniConstant| := by
    rw [abs_mul]
    have := RHTower.abs_sum_moebius_div_le_one N hN
    exact mul_le_of_le_one_right (abs_nonneg _) this
  have hrem : |∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
      (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
        - Real.eulerMascheroniConstant)| ≤ 4 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ d ∈ Finset.Icc 1 N,
        |((μ d : ℤ) : ℝ) / (d : ℝ) *
          (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
            - Real.eulerMascheroniConstant)| ≤ 4 / (N : ℝ) := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hm : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
      have hmR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hm
      have hdefect := abs_harmonic_floor_defect_le hd1 hdN
      have hchain : (2 : ℝ) / ((N / d : ℕ) : ℝ) ≤ 4 * (d : ℝ) / (N : ℝ) := by
        rw [div_le_div_iff₀ hmR hNR]
        have hnat : N ≤ 2 * (N / d) * d := two_mul_natDiv_mul_ge hd1 hdN
        have hcast : (N : ℝ) ≤ 2 * ((N / d : ℕ) : ℝ) * (d : ℝ) := by
          exact_mod_cast hnat
        nlinarith [hcast, hmR, hdR]
      have hmu : |((μ d : ℤ) : ℝ) / (d : ℝ)| ≤ 1 / (d : ℝ) := by
        rw [abs_div, abs_of_pos hdR]
        exact div_le_div_of_nonneg_right (abs_moebius_le_one d) hdR.le
      rw [abs_mul]
      calc |((μ d : ℤ) : ℝ) / (d : ℝ)| *
            |((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
              - Real.eulerMascheroniConstant|
          ≤ (1 / (d : ℝ)) * (2 / ((N / d : ℕ) : ℝ)) := by
            exact mul_le_mul hmu hdefect (abs_nonneg _) (by positivity)
        _ ≤ (1 / (d : ℝ)) * (4 * (d : ℝ) / (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hchain (by positivity)
        _ = 4 / (N : ℝ) := by field_simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by
      norm_num
    rw [hcard, show (N : ℝ) * (4 / (N : ℝ)) = 4 from by field_simp]
  rw [hbase]
  calc |1 - ∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ)))|
      ≤ 1 + |∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
        (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ)))| := by
        have := abs_sub (1 : ℝ) (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
          (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))))
        simpa using this
    _ ≤ 5 + |Real.eulerMascheroniConstant| := by
        rw [hsplit]
        have hadd := abs_add_le (Real.eulerMascheroniConstant *
            (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ)))
          (∑ d ∈ Finset.Icc 1 N, ((μ d : ℤ) : ℝ) / (d : ℝ) *
            (((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
              - Real.eulerMascheroniConstant))
        linarith [hgamma, hrem, hadd]

end RHTower.Sieve
