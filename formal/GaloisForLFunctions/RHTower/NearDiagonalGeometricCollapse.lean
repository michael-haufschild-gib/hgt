import GaloisForLFunctions.RHTower.NearDiagonalDyadicSum

/-!
# The geometric collapse of the top-scale sum

The symbolic increasing sum `Σ_{j<J} √((A 2^j)^(3 : ℕ))` is a geometric series with ratio `2√2`, so it is
at most `(3/5)·√((A 2^J)^(3 : ℕ))`: the dyadic blocks' increasing contributions are dominated by the top
block.
-/

namespace RHTower

noncomputable section

theorem sqrt_dyadic_cube (A : ℕ) (j : ℕ) :
    Real.sqrt (((A : ℝ) * 2 ^ j) ^ (3 : ℕ))
      = Real.sqrt ((A : ℝ) ^ (3 : ℕ)) * (2 * Real.sqrt 2) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep : ((A : ℝ) * 2 ^ (j + 1)) ^ (3 : ℕ) = ((A : ℝ) * 2 ^ j) ^ (3 : ℕ) * 8 := by ring
    rw [hstep, Real.sqrt_mul (by positivity), ih]
    have h8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      rw [show (8 : ℝ) = 2 ^ (2 : ℕ) * 2 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    rw [h8]
    ring

theorem two_sqrt_two_lower : (5 / 3 : ℝ) ≤ 2 * Real.sqrt 2 - 1 := by
  have h : (1.41 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1.41 : ℝ) = Real.sqrt (1.41 ^ (2 : ℕ)) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **The geometric collapse.** -/
theorem nearDiagonalTopSum_le (A J : ℕ) :
    nearDiagonalTopSum A J ≤ (3 / 5 : ℝ) * Real.sqrt (((A : ℝ) * 2 ^ J) ^ (3 : ℕ)) := by
  have hc : (1 : ℝ) < 2 * Real.sqrt 2 := by
    have := two_sqrt_two_lower
    linarith
  have hcne : (2 * Real.sqrt 2 : ℝ) ≠ 1 := ne_of_gt hc
  have hgeom : ∑ j ∈ Finset.range J, (2 * Real.sqrt 2) ^ j
      = ((2 * Real.sqrt 2) ^ J - 1) / (2 * Real.sqrt 2 - 1) := geom_sum_eq hcne J
  have hsum : nearDiagonalTopSum A J
      = Real.sqrt ((A : ℝ) ^ (3 : ℕ)) * ∑ j ∈ Finset.range J, (2 * Real.sqrt 2) ^ j := by
    rw [nearDiagonalTopSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => sqrt_dyadic_cube A j
  have hpow : Real.sqrt (((A : ℝ) * 2 ^ J) ^ (3 : ℕ))
      = Real.sqrt ((A : ℝ) ^ (3 : ℕ)) * (2 * Real.sqrt 2) ^ J := sqrt_dyadic_cube A J
  have hA : 0 ≤ Real.sqrt ((A : ℝ) ^ (3 : ℕ)) := Real.sqrt_nonneg _
  have hcJ : 0 < (2 * Real.sqrt 2) ^ J := by positivity
  have hden : (0 : ℝ) < 2 * Real.sqrt 2 - 1 := by linarith
  have hgle : ∑ j ∈ Finset.range J, (2 * Real.sqrt 2) ^ j ≤ (3 / 5 : ℝ) * (2 * Real.sqrt 2) ^ J := by
    rw [hgeom, div_le_iff₀ hden]
    nlinarith [two_sqrt_two_lower, hcJ]
  rw [hsum, hpow]
  nlinarith [mul_le_mul_of_nonneg_left hgle hA]

end

end RHTower
