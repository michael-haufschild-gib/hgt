import GaloisForLFunctions.RHTower.Sieve.LogMoebiusBounded

/-!
# The totient weight of the Selberg diagonal

The diagonalised quadratic form carries the weight `φ(e)/e²` over squarefree `e ≤ X`.  Since
`φ(e) ≤ e`, that weight is dominated by the harmonic weight `1/e`, so the whole diagonal is
`O(log X)` as soon as the inner sums are uniformly bounded.  This is the second of the two inputs
of Graham's evaluation.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

/-- **The totient weight is dominated by the harmonic weight.** -/
theorem sum_totient_div_sq_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) / (e : ℝ) ^ (2 : ℕ)
      ≤ ∑ e ∈ Finset.Icc 1 N, 1 / (e : ℝ) := by
  refine Finset.sum_le_sum fun e he => ?_
  obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have htot : (Nat.totient e : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast Nat.totient_le e
  rw [div_le_div_iff₀ (by positivity) heR]
  nlinarith [htot, heR]

/-- The diagonal weight is bounded by the harmonic weight, term by term, against any nonnegative
uniform bound on the inner sums. -/
theorem sum_totient_diagonal_le {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (T : ℕ → ℝ)
    (hT : ∀ e ∈ Finset.Icc 1 N, |T e| ≤ C) :
    ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) / (e : ℝ) ^ (2 : ℕ) * (T e) ^ (2 : ℕ)
      ≤ C ^ (2 : ℕ) * ∑ e ∈ Finset.Icc 1 N, 1 / (e : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  obtain ⟨he1, -⟩ := Finset.mem_Icc.mp he
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (by omega : 0 < e)
  have htot : (Nat.totient e : ℝ) ≤ (e : ℝ) := by
    exact_mod_cast Nat.totient_le e
  have htot0 : (0 : ℝ) ≤ (Nat.totient e : ℝ) := by positivity
  have hTe : (T e) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) := by
    have h := hT e he
    nlinarith [abs_nonneg (T e), sq_abs (T e), h, hC]
  have hweight : (Nat.totient e : ℝ) / (e : ℝ) ^ (2 : ℕ) ≤ 1 / (e : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) heR]
    nlinarith [htot, heR]
  calc (Nat.totient e : ℝ) / (e : ℝ) ^ (2 : ℕ) * (T e) ^ (2 : ℕ)
      ≤ (Nat.totient e : ℝ) / (e : ℝ) ^ (2 : ℕ) * C ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hTe (by positivity)
    _ ≤ (1 / (e : ℝ)) * C ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = C ^ (2 : ℕ) * (1 / (e : ℝ)) := by ring

end RHTower.Sieve
