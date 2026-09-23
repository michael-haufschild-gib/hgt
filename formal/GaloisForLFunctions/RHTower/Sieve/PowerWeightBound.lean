import Mathlib

/-!
# Two weight bounds for prime-power tails

The tail of a prime-power sum carries the weight `k` from `log(p^k) = k log p`, so the geometric
series needed is `∑_k k x^k` rather than `∑_k x^k`.  Written with the shift `k = j + 2` it is

`∑_{j < M} (j+2) (1/2)^j = 6 - 2(M+3)/2^M ≤ 6`,

whence `∑_{j < M} (j+2) x^{j+2} ≤ 6x²` for `0 ≤ x ≤ 1/2`: the proper prime powers of `p` contribute
at most `6(log p)²/p²` to a `Λ·log/id` sum.

The second bound converts that into something summable against `1/p`: for `x ≥ 1`,
`log x ≤ 2√x`, so `(log x)² ≤ 4x`.
-/

namespace RHTower.Sieve

open Finset

/-- The exact shifted geometric-with-linear-weight sum at `1/2`. -/
theorem sum_range_add_two_mul_half_pow (M : ℕ) :
    ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j
      = 6 - 2 * ((M : ℝ) + 3) / 2 ^ M := by
  induction M with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      have hhalf : (1 / 2 : ℝ) ^ m = 1 / 2 ^ m := by rw [div_pow, one_pow]
      rw [hhalf, pow_succ]
      push_cast
      field_simp
      ring

/-- The same sum at any `x ≤ 1/2` is at most `6`. -/
theorem sum_range_add_two_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * x ^ j ≤ 6 := by
  have hstep : ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * x ^ j
      ≤ ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * (1 / 2 : ℝ) ^ j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hpow : x ^ j ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ hx0 hx j
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    exact mul_le_mul_of_nonneg_left hpow hj
  have hexact := sum_range_add_two_mul_half_pow M
  have hpos : (0 : ℝ) < 2 ^ M := by positivity
  have hsub : 0 ≤ 2 * ((M : ℝ) + 3) / 2 ^ M := by positivity
  linarith

/-- **The prime-power tail weight.**  `∑_{k ≥ 2} k x^k ≤ 6x²` on `0 ≤ x ≤ 1/2`. -/
theorem sum_range_shift_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * x ^ (j + 2) ≤ 6 * x ^ (2 : ℕ) := by
  have hrw : ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * x ^ (j + 2)
      = x ^ (2 : ℕ) * ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * x ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_add]; ring
  rw [hrw]
  have hbase := sum_range_add_two_mul_pow_le hx0 hx M
  have hx2 : (0 : ℝ) ≤ x ^ (2 : ℕ) := sq_nonneg x
  nlinarith

/-- **`(log x)² ≤ 4x` for `x ≥ 1`**, from `log x ≤ 2√x`. -/
theorem log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ (2 : ℕ) ≤ 4 * x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hsqrtpos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hsqrtpos
  have h2 : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (le_of_lt hx0)
  rw [h2] at h1
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hle : Real.log x ≤ 2 * Real.sqrt x := by linarith
  have hsq : Real.sqrt x ^ (2 : ℕ) = x := Real.sq_sqrt (le_of_lt hx0)
  have := pow_le_pow_left₀ hlog0 hle 2
  calc Real.log x ^ (2 : ℕ) ≤ (2 * Real.sqrt x) ^ (2 : ℕ) := this
    _ = 4 * x := by rw [mul_pow, hsq]; norm_num

end RHTower.Sieve
