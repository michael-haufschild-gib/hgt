import GaloisForLFunctions.HTGeometry.QuarterRootTelescopeSum
import Mathlib.Order.Interval.Finset.Nat

/-!
# The Möbius-weight square-root sum bound

`∑_{n ≤ N} (log N − log n)·√⌊N/n⌋ ≤ 16·N`:

per term, `log(N/n) ≤ 4·(N/n)^{1/4}` and `√⌊N/n⌋ ≤ (N/n)^{1/2}`, so each
summand is at most `4·(N/n)^{3/4} = 4·(√√N)³/(√√n)³`, and the quarter-root
telescope `∑ 1/(√√n)³ ≤ 4√√N` closes the sum at `16·(√√N)⁴ = 16N`.  This
dominates the Tatuzawa–Iseki left side for any function whose floor
summatory is `O(√k)`, which is what converts the `ψ`-defect bound into
Selberg's symmetry formula.
-/

namespace RHTower

open Finset

/-- **Weighted square-root sum bound**:
`∑_{n ≤ N} (log N − log n)·√⌊N/n⌋ ≤ 16N`. -/
theorem sum_log_weight_sqrt_floor_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N,
        (Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ)
      ≤ 16 * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set q : ℝ := Real.sqrt (Real.sqrt (N : ℝ)) with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq4 : q ^ (4 : ℕ) = (N : ℝ) := by
    rw [hq, show (Real.sqrt (Real.sqrt (N : ℝ))) ^ (4 : ℕ)
      = ((Real.sqrt (Real.sqrt (N : ℝ))) ^ (2 : ℕ)) ^ (2 : ℕ) from by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hN0.le]
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ)
        ≤ 4 * q ^ (3 : ℕ) * (1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ (3 : ℕ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn.2
    set r : ℝ := Real.sqrt (Real.sqrt ((N : ℝ) / n)) with hr
    set qn : ℝ := Real.sqrt (Real.sqrt (n : ℝ)) with hqn
    have hqn1 : 1 ≤ qn := by
      rw [hqn, show (1 : ℝ) = Real.sqrt (Real.sqrt 1) from by
        rw [Real.sqrt_one, Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by exact_mod_cast hn.1))
    have hqn0 : (0 : ℝ) < qn := by linarith
    have hone : (1 : ℝ) ≤ (N : ℝ) / n := (one_le_div hn0).2 hnN
    -- log part
    have hlogeq : Real.log N - Real.log n = Real.log ((N : ℝ) / n) :=
      (Real.log_div hN0.ne' hn0.ne').symm
    have hlog : Real.log N - Real.log n ≤ 4 * r := by
      rw [hlogeq]
      have := HTGeometry.log_le_four_quarter_root_sub_one hone
      rw [← hr] at this
      linarith [Real.sqrt_nonneg (Real.sqrt ((N : ℝ) / n))]
    have hlognn : 0 ≤ Real.log N - Real.log n := by
      rw [hlogeq]
      exact Real.log_nonneg hone
    -- floor part
    have hfloorle : ((N / n : ℕ) : ℝ) ≤ (N : ℝ) / n := by
      rw [le_div_iff₀ hn0]
      exact_mod_cast Nat.div_mul_le_self N n
    have hfloor : Real.sqrt ((N / n : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / n) :=
      Real.sqrt_le_sqrt hfloorle
    have hsq : Real.sqrt ((N : ℝ) / n) = r ^ (2 : ℕ) := by
      rw [hr, Real.sq_sqrt (Real.sqrt_nonneg _)]
    -- product bound
    have hprod : (Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ)
        ≤ 4 * r * r ^ (2 : ℕ) := by
      have := mul_le_mul hlog hfloor (Real.sqrt_nonneg _)
        (by positivity : (0 : ℝ) ≤ 4 * r)
      rw [hsq] at this
      exact this
    -- split the quarter root of the quotient
    have hrdiv : r = q / qn := by
      rw [hr, hq, hqn, Real.sqrt_div hN0.le, Real.sqrt_div (Real.sqrt_nonneg _)]
    have hfin : 4 * r * r ^ (2 : ℕ) = 4 * q ^ (3 : ℕ) * (1 / qn ^ (3 : ℕ)) := by
      rw [hrdiv]
      field_simp
    rw [hfin] at hprod
    exact hprod
  calc ∑ n ∈ Finset.Icc 1 N,
        (Real.log N - Real.log n) * Real.sqrt ((N / n : ℕ) : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 N,
          4 * q ^ (3 : ℕ) * (1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ (3 : ℕ)) :=
        Finset.sum_le_sum hterm
    _ = 4 * q ^ (3 : ℕ) * ∑ n ∈ Finset.Icc 1 N,
          1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ (3 : ℕ) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * q ^ (3 : ℕ) * (4 * q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := HTGeometry.sum_inv_quarter_root_cube_le N
        rw [← hq] at this
        exact this
    _ = 16 * N := by
        rw [show (4 : ℝ) * q ^ (3 : ℕ) * (4 * q) = 16 * q ^ (4 : ℕ) from by ring, hq4]

end RHTower
