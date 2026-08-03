import GaloisForLFunctions.RHTower.Sieve.PowerWeightBound
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# The proper prime powers contribute `O(log b)`

Indexing proper prime powers as `p^{j+2}` with `p ≤ b` and `j < M`, the `Λ·log/id` weight is
`(j+2)(log p)²/p^{j+2}`.  Summing over `j` uses `∑_{k ≥ 2} k x^k ≤ 6x²` at `x = 1/p ≤ 1/2`, and
`(log p)² ≤ 4p` turns the result into `24/p`:

`∑_{p ≤ b} ∑_{j < M} (j+2)(log p)²/p^{j+2} ≤ 24 ∑_{p ≤ b} 1/p ≤ 24(1 + log b)`.

So against the `½ log²N` main term of the `Λ·log/id` summatory the proper prime powers are a lower
order correction, uniformly in the number of exponents allowed.
-/

namespace RHTower.Sieve

open Finset

/-- The inner sum over exponents at a single prime. -/
theorem sum_range_primePower_weight_le {p : ℕ} (hp : 2 ≤ p) (M : ℕ) :
    ∑ j ∈ Finset.range M, (((j : ℝ) + 2) * Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ (j + 2)))
      ≤ 24 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hx : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hrw : ∑ j ∈ Finset.range M, (((j : ℝ) + 2) * Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ (j + 2)))
      = Real.log (p : ℝ) ^ 2 * ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * (1 / (p : ℝ)) ^ (j + 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, one_pow]
    field_simp
  rw [hrw]
  have hgeom := sum_range_shift_pow_le hx0 hx M
  have hlogsq : Real.log (p : ℝ) ^ 2 ≤ 4 * (p : ℝ) := log_sq_le_four_mul hp1
  have hlog0 : (0 : ℝ) ≤ Real.log (p : ℝ) ^ 2 := sq_nonneg _
  have hstep : Real.log (p : ℝ) ^ 2 * ∑ j ∈ Finset.range M, ((j : ℝ) + 2) * (1 / (p : ℝ)) ^ (j + 2)
      ≤ Real.log (p : ℝ) ^ 2 * (6 * (1 / (p : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hgeom hlog0
  refine le_trans hstep ?_
  calc Real.log (p : ℝ) ^ 2 * (6 * (1 / (p : ℝ)) ^ 2)
      = 6 * Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
        rw [div_pow, one_pow]; ring
    _ ≤ 6 * (4 * (p : ℝ)) / (p : ℝ) ^ 2 := by gcongr
    _ = 24 / (p : ℝ) := by
        rw [pow_two]
        field_simp
        ring

/-- **The proper prime powers contribute `O(log b)`.** -/
theorem sum_primePower_weight_le (b M : ℕ) :
    ∑ x ∈ Nat.primesLE b ×ˢ Finset.range M,
        (((x.2 : ℝ) + 2) * Real.log (x.1 : ℝ) ^ 2 / ((x.1 : ℝ) ^ (x.2 + 2)))
      ≤ 24 * (1 + Real.log b) := by
  classical
  rw [Finset.sum_product]
  have hinner : ∀ p ∈ Nat.primesLE b,
      ∑ j ∈ Finset.range M, (((j : ℝ) + 2) * Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ (j + 2)))
        ≤ 24 * (1 / (p : ℝ)) := by
    intro p hp
    have := sum_range_primePower_weight_le (Nat.prime_of_mem_primesLE hp).two_le M
    calc ∑ j ∈ Finset.range M, (((j : ℝ) + 2) * Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ (j + 2)))
        ≤ 24 / (p : ℝ) := this
      _ = 24 * (1 / (p : ℝ)) := by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have hsub : Nat.primesLE b ⊆ Finset.Icc 1 b := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesLE hp).one_lt.le, Nat.le_of_mem_primesLE hp⟩
  have hle : ∑ p ∈ Nat.primesLE b, 1 / (p : ℝ) ≤ ∑ m ∈ Finset.Icc 1 b, 1 / (m : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => by positivity
  have hharm := sum_Icc_one_div_le_one_add_log b
  linarith

end RHTower.Sieve
