import GaloisForLFunctions.RHTower.MertensSecondTheorem

/-!
# The Chebyshev square-weight sum

The mollified coefficient on the short range is `Λ(k)/log X`, so the coefficient estimate needs
`∑_{k ≤ X} Λ(k)²/k ≪ (log X)²`.  Since `Λ(k) ≤ log k ≤ log X` on the range, the square sum is
dominated by `log X` times the Mertens sum, and Mertens' second theorem — already owned by this
tree — bounds that by `log X + O(1)`.
-/

open Finset ArithmeticFunction Filter Topology

namespace RHTower

/-- **Termwise reduction of the square weight to the Mertens weight.** -/
theorem sum_vonMangoldt_sq_div_le_log_mul_sum (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (vonMangoldt k) ^ 2 / (k : ℝ)
      ≤ Real.log (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, (vonMangoldt k) / (k : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hlogk : Real.log (k : ℝ) ≤ Real.log (N : ℝ) := by
    have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
    exact Real.log_le_log hk0 hkNR
  have hΛ : vonMangoldt k ≤ Real.log (N : ℝ) := le_trans vonMangoldt_le_log hlogk
  have hΛ0 : (0 : ℝ) ≤ vonMangoldt k := vonMangoldt_nonneg
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  nlinarith [hΛ, hΛ0]

/-- **The Chebyshev square-weight bound.**  There is an absolute constant with
`∑_{k ≤ N} Λ(k)²/k ≤ log N · (log N + C)` for every `N`. -/
theorem exists_sum_vonMangoldt_sq_div_le :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Finset.Icc 1 N, (vonMangoldt k) ^ 2 / (k : ℝ)
        ≤ Real.log (N : ℝ) * (Real.log (N : ℝ) + C) := by
  have hconv := tendsto_sum_vonMangoldt_div_sub_log
  obtain ⟨C, hC⟩ := hconv.bddAbove_range
  refine ⟨C, fun N hN => ?_⟩
  have hmem : (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / (n : ℝ)) - Real.log (N : ℝ) ≤ C :=
    hC (Set.mem_range_self N)
  have hlog0 : (0 : ℝ) ≤ Real.log (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact Real.log_nonneg this
  refine le_trans (sum_vonMangoldt_sq_div_le_log_mul_sum N) ?_
  refine mul_le_mul_of_nonneg_left ?_ hlog0
  linarith

end RHTower
