import GaloisForLFunctions.HTGeometry.LogBelowLinear

/-!
# A logarithmic weight against a geometric tail

Two elementary facts let a geometrically decaying sequence absorb a logarithmic weight without any
comparison of orders.  The square of a logarithm is below four times its argument, so one factor of
the decay pays for the whole weight; and the partial sums of a geometric series past an index are
bounded by that index's term over the gap to one.

Together they bound a weighted tail by a single explicit geometric term.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The partial sums of a geometric series with ratio below one are bounded by the reciprocal of the
gap to one. -/
theorem geom_sum_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i ≤ (1 - x)⁻¹ := by
  have hne : x ≠ 1 := ne_of_lt hx1
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hne' : x - 1 ≠ 0 := by intro h; exact hne (by linarith)
  have hne'' : (1 : ℝ) - x ≠ 0 := ne_of_gt hpos
  rw [geom_sum_eq hne]
  have hrw : (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) := by
    field_simp
    ring
  rw [hrw, inv_eq_one_div]
  have hxn : (0 : ℝ) ≤ x ^ n := pow_nonneg hx0 n
  gcongr
  linarith

/-- A geometric tail past an index is bounded by that index's term over the gap to one. -/
theorem sum_Ico_geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K n : ℕ) :
    ∑ k ∈ Finset.Ico K n, x ^ k ≤ x ^ K * (1 - x)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ k ∈ Finset.range (n - K), x ^ (K + k) = x ^ K * x ^ k := fun k _ => pow_add x K k
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_sum_range_le hx0 hx1 (n - K)) (pow_nonneg hx0 K)

/-- **A logarithm squared is below four times its argument.**  Halving the logarithm puts it under
the square root, whose own square is the argument. -/
theorem sq_log_le_four_mul {t : ℝ} (ht : 1 ≤ t) : Real.log t ^ 2 ≤ 4 * t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hlog : Real.log t ≤ 2 * Real.sqrt t := log_le_two_mul_sqrt ht0
  have hlognn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  nlinarith [hlog, hlognn, hsq, Real.sqrt_nonneg t]

/-- The same bound for the absolute value of the logarithm. -/
theorem sq_abs_log_le_four_mul {t : ℝ} (ht : 1 ≤ t) : |Real.log t| ^ 2 ≤ 4 * t := by
  rw [abs_of_nonneg (Real.log_nonneg ht)]
  exact sq_log_le_four_mul ht

end GaloisForLFunctions.HTGeometry
