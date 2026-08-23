import GaloisForLFunctions.RHTower.Sieve.AbelIcoWeight
import GaloisForLFunctions.RHTower.Sieve.TypeIBound

/-!
# The type-I inner sum with a logarithmic weight

The `log ∗ μ_V` piece of Vaughan's identity carries the weight `log k` on the inner range.  The
weight is nonnegative and nondecreasing, so Abel's inequality removes it at the cost of a factor
`2 log(B−1)`; every prefix of the inner sum obeys the same near-diagonal block estimate, whose
right-hand side is increasing in the right endpoint.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

/-- The block bound is increasing in the right endpoint. -/
theorem ndBlockBound_mono {T r : ℝ} {A : ℕ} {J B : ℕ} (hJB : J ≤ B) :
    2500 * Real.sqrt (T * r / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((J : ℝ)) ^ 3)
      ≤ 2500 * Real.sqrt (T * r / (36 * Real.pi * A))
        + 22 * Real.sqrt (36 * Real.pi / (T * r)) * Real.sqrt (((B : ℝ)) ^ 3) := by
  have hJ : ((J : ℝ)) ^ 3 ≤ ((B : ℝ)) ^ 3 := by
    have hcast : (J : ℝ) ≤ (B : ℝ) := by exact_mod_cast hJB
    exact pow_le_pow_left₀ (Nat.cast_nonneg J) hcast 3
  have hmono : Real.sqrt (((J : ℝ)) ^ 3) ≤ Real.sqrt (((B : ℝ)) ^ 3) := Real.sqrt_le_sqrt hJ
  have hcoef : (0 : ℝ) ≤ 22 * Real.sqrt (36 * Real.pi / (T * r)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hcoef]

/-- **The type-I inner sum with the logarithmic weight.** -/
theorem norm_sum_log_ndExp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) {d : ℕ} (hd : 1 ≤ d)
    {A B : ℕ} (hAB : A < B) (hA : 1 ≤ A) (hrA : r / d ≤ (A : ℝ))
    (hlam : nearDiagonalLambda T (r / d) (A : ℝ) ≤ 1) :
    ‖∑ k ∈ Finset.Ico A B, ((Real.log k : ℝ) : ℂ) * ndExp T r k d‖
      ≤ 2 * (2500 * Real.sqrt (T * (r / d) / (36 * Real.pi * A))
              + 22 * Real.sqrt (36 * Real.pi / (T * (r / d))) * Real.sqrt (((B : ℝ)) ^ 3))
          * Real.log ((B - 1 : ℕ) : ℝ) := by
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  refine norm_sum_Ico_mul_le_of_bounded_partial_mono hAB (fun k => Real.log k)
    (fun k => ndExp T r k d) (Real.log_nonneg hA1) ?_ ?_
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by
      have : (1 : ℕ) ≤ i := le_trans hA hi
      exact_mod_cast this
    refine Real.log_le_log (by linarith) ?_
    push_cast
    linarith
  · intro k hk
    have hle : A + k ≤ B := by omega
    refine le_trans (norm_sum_ndExp_le hT hr hd A (A + k) hA hrA hlam) ?_
    exact ndBlockBound_mono hle

end

end RHTower.Sieve
