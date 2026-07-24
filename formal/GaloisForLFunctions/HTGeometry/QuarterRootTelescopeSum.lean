import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The quarter-root telescope

Elementary square-root-only versions of `∑_{n ≤ N} n^{-3/4} ≤ 4·N^{1/4}`
and `log x ≤ 4(x^{1/4} − 1)`, with `x^{1/4}` realized as `√√x`:

* `quarter_root_inv_cube_le`: `1/(√√n)³ ≤ 4(√√n − √√(n−1))` — from
  `a⁴ − b⁴ = (a−b)(a³+a²b+ab²+b³) ≤ (a−b)·4a³`.
* `sum_inv_quarter_root_cube_le`: summing the telescope gives `≤ 4√√N`.
* `log_le_four_quarter_root_sub_one`: `log x = 4·log(√√x) ≤ 4(√√x − 1)`.

Together these bound logarithmically-weighted square-root sums like
`∑_{n ≤ N} log(N/n)·√(N/n)` by `O(N)` without improper integrals: the
weight `log(N/n)·√(N/n) ≤ 4·(N/n)^{3/4}` and the `3/4`-power sum
telescopes.
-/

namespace HTGeometry

open Finset

/-- `1/(√√n)³ ≤ 4·(√√n − √√(n−1))` for `1 ≤ n`. -/
theorem quarter_root_inv_cube_le {x : ℝ} (hx : 1 ≤ x) :
    1 / Real.sqrt (Real.sqrt x) ^ 3
      ≤ 4 * (Real.sqrt (Real.sqrt x) - Real.sqrt (Real.sqrt (x - 1))) := by
  set a := Real.sqrt (Real.sqrt x) with ha
  set b := Real.sqrt (Real.sqrt (x - 1)) with hb
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx10 : (0 : ℝ) ≤ x - 1 := by linarith
  have ha1 : 1 ≤ a := by
    rw [ha, show (1 : ℝ) = Real.sqrt (Real.sqrt 1) from by
      rw [Real.sqrt_one, Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hx)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hba : b ≤ a := by
    rw [ha, hb]
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by linarith))
  have ha4 : a ^ 4 = x := by
    rw [ha, show (Real.sqrt (Real.sqrt x)) ^ 4
      = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 from by ring,
      Real.sq_sqrt (Real.sqrt_nonneg x), Real.sq_sqrt hx0]
  have hb4 : b ^ 4 = x - 1 := by
    rw [hb, show (Real.sqrt (Real.sqrt (x - 1))) ^ 4
      = ((Real.sqrt (Real.sqrt (x - 1))) ^ 2) ^ 2 from by ring,
      Real.sq_sqrt (Real.sqrt_nonneg (x - 1)), Real.sq_sqrt hx10]
  have hfact : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) = 1 := by
    have : a ^ 4 - b ^ 4 = 1 := by rw [ha4, hb4]; ring
    nlinarith [this]
  have hS4 : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 ≤ 4 * a ^ 3 := by
    nlinarith [hba, hb0, ha1, sq_nonneg a, sq_nonneg b, sq_nonneg (a - b),
      mul_nonneg hb0 hb0]
  have hab0 : 0 ≤ a - b := by linarith
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  rw [div_le_iff₀ ha3]
  nlinarith [hfact, mul_le_mul_of_nonneg_left hS4 hab0]

/-- **Quarter-root telescope**: `∑_{n ≤ N} 1/(√√n)³ ≤ 4·√√N`. -/
theorem sum_inv_quarter_root_cube_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3
      ≤ 4 * Real.sqrt (Real.sqrt N) := by
  have hstep : ∀ n ∈ Finset.Icc 1 N,
      1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3
        ≤ 4 * (Real.sqrt (Real.sqrt (n : ℝ))
            - Real.sqrt (Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn.1, Nat.cast_one]
    rw [hcast]
    exact quarter_root_inv_cube_le (by exact_mod_cast hn.1)
  calc ∑ n ∈ Finset.Icc 1 N, 1 / Real.sqrt (Real.sqrt (n : ℝ)) ^ 3
      ≤ ∑ n ∈ Finset.Icc 1 N, 4 * (Real.sqrt (Real.sqrt (n : ℝ))
          - Real.sqrt (Real.sqrt ((n - 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum hstep
    _ = 4 * ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (Real.sqrt (n : ℝ))
          - Real.sqrt (Real.sqrt ((n - 1 : ℕ) : ℝ))) := by
        rw [Finset.mul_sum]
    _ = 4 * (Real.sqrt (Real.sqrt N) - Real.sqrt (Real.sqrt ((0 : ℕ) : ℝ))) := by
        congr 1
        have hre : ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (Real.sqrt (n : ℝ))
            - Real.sqrt (Real.sqrt ((n - 1 : ℕ) : ℝ)))
            = ∑ i ∈ Finset.range N, (Real.sqrt (Real.sqrt ((i + 1 : ℕ) : ℝ))
              - Real.sqrt (Real.sqrt ((i : ℕ) : ℝ))) := by
          apply Finset.sum_nbij' (i := fun n => n - 1) (j := fun i => i + 1)
          · intro n hn
            rw [Finset.mem_Icc] at hn
            rw [Finset.mem_range]
            omega
          · intro i hi
            rw [Finset.mem_range] at hi
            rw [Finset.mem_Icc]
            omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            omega
          · intro i _
            omega
          · intro n hn
            rw [Finset.mem_Icc] at hn
            have h1 : n - 1 + 1 = n := by omega
            rw [h1]
        rw [hre]
        exact Finset.sum_range_sub
          (fun i => Real.sqrt (Real.sqrt ((i : ℕ) : ℝ))) N
    _ = 4 * Real.sqrt (Real.sqrt N) := by
        norm_num

/-- `log x ≤ 4·(√√x − 1)` for `1 ≤ x`. -/
theorem log_le_four_quarter_root_sub_one {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 4 * (Real.sqrt (Real.sqrt x) - 1) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hq : Real.log (Real.sqrt (Real.sqrt x)) = Real.log x / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx0.le]
    ring
  have hpos : 0 < Real.sqrt (Real.sqrt x) := by
    apply Real.sqrt_pos.2
    exact Real.sqrt_pos.2 hx0
  have hle := Real.log_le_sub_one_of_pos hpos
  rw [hq] at hle
  linarith

end HTGeometry
