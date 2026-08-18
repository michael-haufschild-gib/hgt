import GaloisForLFunctions.RHTower.Sieve.DivisorSumMeanSquare

/-!
# Removing the floor from the lcm quadratic form

Replacing `⌊N/[m₁,m₂]⌋` by `N/[m₁,m₂]` costs at most one unit per pair, so the divisor-sum mean
square equals the smooth quadratic form up to the `ℓ¹`-square of the coefficients.  This is step two
of Graham's theorem; what is left after it is the evaluation of the smooth form itself.
-/

open Finset

namespace RHTower.Sieve

theorem abs_natDiv_sub_div_le {N d : ℕ} (hd : 0 < d) :
    |((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hlt : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
    have hnat : N < (N / d + 1) * d := by
      have hmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
      have hlt' : N % d < d := Nat.mod_lt _ hd
      calc N = d * (N / d) + N % d := hmod.symm
        _ < d * (N / d) + d := by omega
        _ = (N / d + 1) * d := by ring
    have hcast : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
      have := (Nat.cast_lt (α := ℝ)).mpr hnat
      push_cast at this
      linarith
    rw [div_lt_iff₀ hdR]
    exact hcast
  rw [abs_le]
  constructor <;> linarith

/-- **Step two of Graham's theorem.**  The divisor-sum mean square agrees with the smooth lcm
quadratic form up to the `ℓ¹`-square of the coefficients. -/
theorem abs_sum_sq_divisorSum_sub_lcm_main_le (N : ℕ) (a : ℕ → ℝ) :
    |(∑ k ∈ Finset.Icc 1 N, (∑ m ∈ k.divisors, a m) ^ 2)
        - ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
            a p.1 * a p.2 * ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ))|
      ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), |a p.1| * |a p.2| := by
  rw [sum_sq_divisorSum_eq_lcm_quadratic N a, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hp11, -⟩ := Finset.mem_Icc.mp hp1
  obtain ⟨hp21, -⟩ := Finset.mem_Icc.mp hp2
  have hlcmpos : 0 < Nat.lcm p.1 p.2 := Nat.pos_of_ne_zero (by
    intro h
    rcases Nat.lcm_eq_zero_iff.mp h with h1 | h1 <;> omega)
  have hdiff : a p.1 * a p.2 * ((N / Nat.lcm p.1 p.2 : ℕ) : ℝ)
      - a p.1 * a p.2 * ((N : ℝ) / (Nat.lcm p.1 p.2 : ℝ))
      = (a p.1 * a p.2) *
        (((N / Nat.lcm p.1 p.2 : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm p.1 p.2 : ℝ)) := by
    ring
  rw [hdiff, abs_mul, abs_mul]
  refine mul_le_of_le_one_right (by positivity) (abs_natDiv_sub_div_le hlcmpos)

end RHTower.Sieve
