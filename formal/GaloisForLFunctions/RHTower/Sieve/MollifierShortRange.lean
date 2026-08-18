import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion

/-!
# The truncated Möbius mollifier annihilates the short range

The coefficients of the product of a Dirichlet polynomial with the truncated Möbius mollifier of
length `X` are divisor sums `∑_{m ∣ k, m ≤ X} μ(m) v(k/m)`.  Below the truncation the divisor
condition `m ≤ X` is vacuous, so with a weight that is constant on the divisors of `k` the whole sum
collapses to the complete Möbius divisor sum, which vanishes for `k > 1`.

This is the mechanism that makes a mollified second moment `O(T)` rather than `O(T log T)`: the
short range contributes only the single term `k = 1`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- Below the truncation every divisor survives the length condition. -/
theorem filter_le_divisors_eq {k X : ℕ} (hk : 0 < k) (hkX : k ≤ X) :
    k.divisors.filter (fun m => m ≤ X) = k.divisors := by
  refine Finset.filter_true_of_mem fun m hm => ?_
  exact le_trans (Nat.le_of_dvd hk (Nat.dvd_of_mem_divisors hm)) hkX

/-- **The truncated Möbius mollifier annihilates the short range.**  For `1 < k ≤ X` and a weight
that is constant along the divisors of `k`, the mollified coefficient vanishes. -/
theorem sum_moebius_filter_mul_const_eq_zero {k X : ℕ} (hk : 1 < k) (hkX : k ≤ X) (v : ℝ) :
    ∑ m ∈ k.divisors.filter (fun m => m ≤ X), (μ m : ℝ) * v = 0 := by
  rw [filter_le_divisors_eq (lt_trans Nat.zero_lt_one hk) hkX, ← Finset.sum_mul,
    sum_divisors_moebius_real, if_neg (Nat.ne_of_gt hk)]
  ring

/-- The unweighted form. -/
theorem sum_moebius_filter_eq_zero {k X : ℕ} (hk : 1 < k) (hkX : k ≤ X) :
    ∑ m ∈ k.divisors.filter (fun m => m ≤ X), (μ m : ℝ) = 0 := by
  have h := sum_moebius_filter_mul_const_eq_zero hk hkX 1
  simpa using h

/-- **The mollified coefficient at `k = 1`.**  Only the term `m = 1` survives. -/
theorem sum_moebius_filter_one {X : ℕ} (hX : 1 ≤ X) (v : ℕ → ℝ) :
    ∑ m ∈ (1 : ℕ).divisors.filter (fun m => m ≤ X), (μ m : ℝ) * v (1 / m) = v 1 := by
  rw [filter_le_divisors_eq Nat.one_pos hX]
  simp


/-! ## The short-range coefficient with a varying weight -/

theorem abs_moebius_le_one (m : ℕ) : |(μ m : ℝ)| ≤ 1 := by
  by_cases h : Squarefree m
  · have hval : (μ m : ℝ) = (-1 : ℝ) ^ (ArithmeticFunction.cardFactors m) := by
      rw [moebius_apply_of_squarefree h]
      push_cast
      ring
    rw [hval, abs_pow, abs_neg, abs_one, one_pow]
  · rw [moebius_eq_zero_of_not_squarefree h]
    norm_num

theorem norm_moebius_complex_le_one (m : ℕ) : ‖((μ m : ℤ) : ℂ)‖ ≤ 1 := by
  have h := abs_moebius_le_one m
  have hcast : ‖((μ m : ℤ) : ℂ)‖ = |(μ m : ℝ)| := by
    rw [show (((μ m : ℤ) : ℂ)) = (((μ m : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast]
  exact h

theorem sum_moebius_divisors_complex (k : ℕ) :
    (∑ m ∈ k.divisors, ((μ m : ℤ) : ℂ)) = if k = 1 then 1 else 0 := by
  have h := sum_divisors_moebius_real k
  have hcast : (∑ m ∈ k.divisors, ((μ m : ℤ) : ℂ))
      = (((∑ m ∈ k.divisors, (μ m : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, h]
  split_ifs <;> norm_num

/-- **The short-range mollified coefficient is the unit indicator up to the cutoff defect.**
Below the truncation the mollified coefficient of a weighted Dirichlet polynomial differs from the
unit indicator by at most the total deviation of the weight from `1` along the divisors of `k`. -/
theorem norm_sum_moebius_filter_sub_indicator_le {k X : ℕ} (hk : 0 < k) (hkX : k ≤ X)
    (v : ℕ → ℂ) :
    ‖(∑ m ∈ k.divisors.filter (fun m => m ≤ X), ((μ m : ℤ) : ℂ) * v (k / m))
        - (if k = 1 then 1 else 0)‖
      ≤ ∑ m ∈ k.divisors, ‖v (k / m) - 1‖ := by
  rw [filter_le_divisors_eq hk hkX, ← sum_moebius_divisors_complex k]
  have hid : (∑ m ∈ k.divisors, ((μ m : ℤ) : ℂ) * v (k / m))
        - ∑ m ∈ k.divisors, ((μ m : ℤ) : ℂ)
      = ∑ m ∈ k.divisors, ((μ m : ℤ) : ℂ) * (v (k / m) - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hid]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun m _ => ?_
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_moebius_complex_le_one m)

end RHTower.Sieve
