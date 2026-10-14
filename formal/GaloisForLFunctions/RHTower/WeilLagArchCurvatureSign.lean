import GaloisForLFunctions.RHTower.WeilLagCurvatureGreenRegularization
import GaloisForLFunctions.HTGeometry.InversePowerCurvature
import GaloisForLFunctions.HTGeometry.CenteredMulLogCurvature

/-! # Strict tail sign of the complete archimedean curvature correction

The full trivial-zero curvature has quartic reciprocal decay. The logarithmic
curvature error has cubic reciprocal decay with coefficient one sixth. Their
comparison orients the actual correction on an explicit integer tail.
-/

namespace RHTower.IntegerLagCurvature
noncomputable section
open GaloisForLFunctions.HTGeometry

private theorem inversePowerPrimitive_even (j : ℕ) (x : ℝ) :
    inversePowerPrimitive (2 * j) x =
      (x ^ (2 * (j + 1)))⁻¹ / (2 * ((j : ℝ) + 1) * (2 * (j : ℝ) + 3)) := by
  unfold inversePowerPrimitive
  rw [show 2 * j + 2 = 2 * (j + 1) by omega]
  congr 1
  push_cast
  ring

private theorem inversePowerPrimitive_even_sum {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun j => inversePowerPrimitive (2 * j) x) (trivialZeroSeriesReal x) := by
  simpa only [inversePowerPrimitive_even, trivialZeroSeriesReal] using
    (summable_trivialZeroSeriesReal_term hx).hasSum

private theorem inversePower_majorant_sum {a : ℝ} (ha : 1 < a) :
    HasSum (fun j : ℕ => (a ^ (2 * j + 4))⁻¹) (1 / (a ^ 2 * (a ^ 2 - 1))) := by
  have ha0 : 0 < a := by linarith
  have ha2 : 1 < a ^ 2 := by nlinarith
  have hr : |(a ^ 2)⁻¹| < 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a))]
    exact (inv_lt_one₀ (pow_pos ha0 2)).mpr ha2
  have h := (hasSum_geometric_of_abs_lt_one hr).mul_left ((a ^ 4)⁻¹)
  convert! h using 1
  · funext j
    simp only [← inv_pow, ← pow_mul, ← pow_add]
    congr 1
    omega
  · have ha1 : a ^ 2 - 1 ≠ 0 := by linarith
    field_simp

/-- Quartic reciprocal bound for the complete trivial-zero curvature. -/
theorem trivialCurvature_quartic_bound (n : ℕ) :
    trivialCurvature n ≤
      1 / ((n + 2 : ℝ) ^ 2 * ((n + 2 : ℝ) ^ 2 - 1)) := by
  have h4 := inversePowerPrimitive_even_sum (x := (n : ℝ) + 4) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h3 := inversePowerPrimitive_even_sum (x := (n : ℝ) + 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h2 := inversePowerPrimitive_even_sum (x := (n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hsum := (h4.sub (h3.mul_left 2)).add h2
  have hmaj := inversePower_majorant_sum (a := (n : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hle (j : ℕ) :
      inversePowerPrimitive (2 * j) ((n : ℝ) + 4) -
        2 * inversePowerPrimitive (2 * j) ((n : ℝ) + 3) +
        inversePowerPrimitive (2 * j) ((n : ℝ) + 2) ≤
          (((n : ℝ) + 2) ^ (2 * j + 4))⁻¹ := by
    simpa only [show (n : ℝ) + 3 + 1 = n + 4 by ring,
      show (n : ℝ) + 3 - 1 = n + 2 by ring] using
      inversePowerPrimitive_centered_le (2 * j) (c := (n : ℝ) + 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have h := hsum.summable.tsum_le_tsum hle hmaj.summable
  rw [hsum.tsum_eq, hmaj.tsum_eq] at h
  exact h

/-- Matching cubic reciprocal bounds retain the complete logarithmic source. -/
theorem logCurvature_centered_cubic_bounds (n : ℕ) :
    1 / (6 * (n + 3 : ℝ) ^ 2 * (n + 4)) ≤ logCurvature n - 1 / (n + 3 : ℝ) ∧
      logCurvature n - 1 / (n + 3 : ℝ) ≤ 1 / (6 * (n + 3 : ℝ) ^ 2 * (n + 2)) := by
  simpa only [show (n : ℝ) + 3 + 1 = n + 4 by ring,
    show (n : ℝ) + 3 - 1 = n + 2 by ring, logCurvature] using
    centered_mul_log_bounds (c := (n : ℝ) + 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])

private theorem quartic_lt_cubic {c : ℝ} (hc : 12 ≤ c) :
    1 / ((c - 1) ^ 2 * ((c - 1) ^ 2 - 1)) < 1 / (6 * c ^ 2 * (c + 1)) := by
  have hc0 : 0 < c := by linarith
  have hcp : 0 < c + 1 := by linarith
  have hd : 0 < 6 * c ^ 2 * (c + 1) := by positivity
  have hpoly : 0 < c ^ 3 - 10 * c ^ 2 - c - 2 := by
    have h := mul_nonneg (show 0 ≤ c - 12 by linarith) (sq_nonneg c)
    nlinarith
  have hgap : 6 * c ^ 2 * (c + 1) < (c - 1) ^ 2 * ((c - 1) ^ 2 - 1) := by
    nlinarith [mul_pos hc0 hpoly]
  exact one_div_lt_one_div_of_lt hd hgap

/-- Every native correction beyond the explicit starting index is negative. -/
theorem archCurvatureCorrection_tail_neg (n : ℕ) : archCurvatureCorrection (n + 9) < 0 := by
  have ht := trivialCurvature_quartic_bound (n + 9)
  have hl := (logCurvature_centered_cubic_bounds (n + 9)).1
  have hg := quartic_lt_cubic (c := (n + 9 : ℕ) + 3) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [archCurvatureCorrection_eq]
  have hm : (((n + 9 : ℕ) : ℝ) + 3) - 1 = (n + 9 : ℕ) + 2 := by ring
  have hp : (((n + 9 : ℕ) : ℝ) + 3) + 1 = (n + 9 : ℕ) + 4 := by ring
  rw [hm, hp] at hg
  linarith

end
end RHTower.IntegerLagCurvature
