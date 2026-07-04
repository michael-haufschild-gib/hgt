/-
R1 envelope layer.

`SpurCumulantBounds` proves the analytic bridge in two pieces: the log-cumulant
tail and the scalar exponential truncation error.  This module packages those
pieces into the single polynomial envelope consumed by the MWM R1 lane.
-/
import GaloisForLFunctions.RHTower.SpurCumulantBounds

namespace RHTower

open Polynomial

noncomputable section

/-- Single-constant half-range R1 envelope.

If the log cumulant is truncated at order `n` with `n + 1 = P`, the product multiplier
and its finite polynomial approximation differ by a constant multiple of `j^(2P)/d^P`
on the half range `2*j <= d`. -/
theorem phi_product_multiplierTruncPoly_abs_bound_half_constant (P n : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hnP : n + 1 = P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)| ≤
      (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  have hbase := phi_product_multiplierTruncPoly_abs_bound_half_envelope P n hd hhalf
  have hdpow_pos : 0 < (d : ℝ) ^ P := by positivity
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : n + 2 ≤ 2 * P := by omega
  have hpowj : (j : ℝ) ^ (n + 2) ≤ (j : ℝ) ^ (2 * P) := by
    exact pow_le_pow_right₀ hjR hexp
  have htail_div : (j : ℝ) ^ (n + 2) / (d : ℝ) ^ P ≤
      (j : ℝ) ^ (2 * P) / (d : ℝ) ^ P :=
    div_le_div_of_nonneg_right hpowj (le_of_lt hdpow_pos)
  have htailB : 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) ≤
      2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
    rw [hnP]
    calc
      2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ P
          = 2 * ((j : ℝ) ^ (n + 2) / (d : ℝ) ^ P) := by ring
      _ ≤ 2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
          exact mul_le_mul_of_nonneg_left htail_div (by norm_num : (0 : ℝ) ≤ 2)
  have htrunc_eq :
      ((n : ℝ) * ((j : ℝ) ^ 2 / d)) ^ P / (P.factorial : ℝ) =
        ((n : ℝ) ^ P / (P.factorial : ℝ)) *
          ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
    rw [mul_pow, div_pow]
    rw [← pow_mul]
    ring
  calc
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P n j).eval ((d : ℝ)⁻¹)|
        ≤ 2 * (j : ℝ) ^ (n + 2) / (d : ℝ) ^ (n + 1) +
            ((n : ℝ) * ((j : ℝ) ^ 2 / d)) ^ P / (P.factorial : ℝ) := hbase
    _ ≤ 2 * ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) +
          ((n : ℝ) ^ P / (P.factorial : ℝ)) *
            ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
      exact add_le_add htailB (le_of_eq htrunc_eq)
    _ = (2 + (n : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by ring

/-- R1's usual `n = P - 1` specialization of the single-constant envelope. -/
theorem phi_product_multiplierTruncPoly_abs_bound_half_order (P : ℕ) {j d : ℕ}
    (hd : 0 < d) (hj : 1 ≤ j) (hhalf : 2 * j ≤ d) (hP : 1 ≤ P) :
    |(∏ i ∈ Finset.range j, (1 - (i : ℝ) / d)) -
        (multiplierTruncPoly P (P - 1) j).eval ((d : ℝ)⁻¹)| ≤
      (2 + ((P - 1 : ℕ) : ℝ) ^ P / (P.factorial : ℝ)) *
        ((j : ℝ) ^ (2 * P) / (d : ℝ) ^ P) := by
  exact phi_product_multiplierTruncPoly_abs_bound_half_constant P (P - 1) hd hj hhalf (by omega)

end

end RHTower
