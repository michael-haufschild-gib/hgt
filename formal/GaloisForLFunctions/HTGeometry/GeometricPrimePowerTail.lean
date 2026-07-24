import Mathlib

/-!
# Geometric prime-power tail bound

The `r ≥ 3` band of the prime-power completion estimate `(PFK15)` of
`xi-physical-prime-log-aperture-fusion-cross-kernel` rests on the elementary geometric tail
`∑_{r ≥ r₀} log n / n^r ≤ 2 log n / n^{r₀}` for `n ≥ 2`: the geometric series from exponent `r₀` is
`(1/n)^{r₀}·(1 - 1/n)⁻¹`, and `(1 - 1/n)⁻¹ ≤ 2` once `n ≥ 2`.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

/-- Geometric tail from exponent `r₀`: for `n ≥ 2`, `∑_{r} (1/n)^(r₀+r) ≤ 2·(1/n)^{r₀}`, since the
geometric sum is `(1/n)^{r₀}·(1-1/n)⁻¹` and `(1-1/n)⁻¹ ≤ 2`. -/
theorem tsum_geom_shift_le_two {n : ℝ} (hn : 2 ≤ n) (r₀ : ℕ) :
    ∑' r : ℕ, (1 / n) ^ (r₀ + r) ≤ 2 * (1 / n) ^ r₀ := by
  have hn0 : 0 < n := by linarith
  have hge : (0:ℝ) ≤ 1 / n := by positivity
  have hlt : (1:ℝ) / n < 1 := by rw [div_lt_one hn0]; linarith
  have hgeom : ∑' r : ℕ, (1 / n) ^ (r₀ + r) = (1 / n) ^ r₀ * (1 - 1 / n)⁻¹ := by
    simp_rw [pow_add]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hge hlt]
  rw [hgeom]
  have hhalf : (1:ℝ) / n ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn
  have hinv : (1 - 1 / n)⁻¹ ≤ 2 := by
    have h2 : (1:ℝ) / 2 ≤ 1 - 1 / n := by linarith
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1 / 2) h2
  calc (1 / n) ^ r₀ * (1 - 1 / n)⁻¹ ≤ (1 / n) ^ r₀ * 2 :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 2 * (1 / n) ^ r₀ := by ring

/-- **`(PFK15)` geometric prime-power tail.**  For `n ≥ 2`,
`∑_{r} log n / n^(r₀+r) ≤ 2 log n / n^{r₀}`. -/
theorem tsum_log_div_pow_shift_le {n : ℝ} (hn : 2 ≤ n) (r₀ : ℕ) :
    ∑' r : ℕ, Real.log n / n ^ (r₀ + r) ≤ 2 * Real.log n / n ^ r₀ := by
  have hn0 : 0 < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hrw : ∀ r : ℕ, Real.log n / n ^ (r₀ + r) = Real.log n * (1 / n) ^ (r₀ + r) := by
    intro r; rw [one_div, inv_pow]; ring
  rw [tsum_congr hrw, tsum_mul_left]
  calc Real.log n * ∑' r : ℕ, (1 / n) ^ (r₀ + r)
      ≤ Real.log n * (2 * (1 / n) ^ r₀) :=
        mul_le_mul_of_nonneg_left (tsum_geom_shift_le_two hn r₀) hlog
    _ = 2 * Real.log n / n ^ r₀ := by rw [one_div, inv_pow]; ring

end GaloisForLFunctions.HTGeometry
