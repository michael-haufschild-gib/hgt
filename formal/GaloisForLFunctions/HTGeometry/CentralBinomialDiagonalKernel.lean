import GaloisForLFunctions.HTGeometry.BernsteinSquareRootKernel
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Central-binomial expansion of the diagonal Bernstein kernel

This file identifies the universal factored square-root kernel with a Cauchy product of two
normalized central-binomial series.  It is the coefficient-side bridge needed for the sharp
half-order asymptotic.
-/

open Filter Topology
open scoped BigOperators Nat Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The normalized central-binomial series at a nonnegative point of the unit interval. -/
theorem normalizedCentralBinom_gf {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => normalizedCentralBinom n * x ^ n)
      ((1 - x) ^ (-1 / 2 : ℝ)) := by
  have hsqrt : |Real.sqrt x| < 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg x)]
    exact (Real.sqrt_lt' zero_lt_one).2 (by simpa using hx1)
  have h := GaloisForLFunctions.centralBinom_gf (Real.sqrt x) hsqrt
  convert h using 2 with n
  · rw [normalizedCentralBinom]
    congr 1
    rw [pow_mul, Real.sq_sqrt hx0]
  · rw [Real.sq_sqrt hx0]

lemma normalizedCentralBinom_nonneg (n : ℕ) :
    0 ≤ normalizedCentralBinom n := by
  exact div_nonneg (by positivity) (by positivity)

/-- Coefficients of the factored diagonal square-root kernel. -/
def centralBinomialDiagonalKernelCoefficient (B D : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    normalizedCentralBinom k * (D ^ 2) ^ k *
      (normalizedCentralBinom (n - k) * (B ^ 2) ^ (n - k))

/-- **Exact diagonal kernel generating identity.**  Inside both characteristic radii, the
central-binomial convolution sums to the universal factored square-root kernel. -/
theorem hasSum_centralBinomialDiagonalKernelCoefficient
    {B D t : ℝ} (ht : 0 ≤ t)
    (hBt : B ^ 2 * t < 1) (hDt : D ^ 2 * t < 1) :
    HasSum
      (fun n : ℕ => centralBinomialDiagonalKernelCoefficient B D n * t ^ n)
      (((1 - B ^ 2 * t) ^ (-1 / 2 : ℝ)) *
        ((1 - D ^ 2 * t) ^ (-1 / 2 : ℝ))) := by
  let f : ℕ → ℝ := fun n => normalizedCentralBinom n * (D ^ 2 * t) ^ n
  let g : ℕ → ℝ := fun n => normalizedCentralBinom n * (B ^ 2 * t) ^ n
  have hBx0 : 0 ≤ B ^ 2 * t := mul_nonneg (sq_nonneg B) ht
  have hDx0 : 0 ≤ D ^ 2 * t := mul_nonneg (sq_nonneg D) ht
  have hf : HasSum f ((1 - D ^ 2 * t) ^ (-1 / 2 : ℝ)) := by
    simpa only [f] using normalizedCentralBinom_gf hDx0 hDt
  have hg : HasSum g ((1 - B ^ 2 * t) ^ (-1 / 2 : ℝ)) := by
    simpa only [g] using normalizedCentralBinom_gf hBx0 hBt
  have hfnorm : Summable (fun n : ℕ => ‖f n‖) := by
    apply hf.summable.congr
    intro n
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (normalizedCentralBinom_nonneg n) (pow_nonneg hDx0 n))]
  have hgnorm : Summable (fun n : ℕ => ‖g n‖) := by
    apply hg.summable.congr
    intro n
    dsimp only [g]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (normalizedCentralBinom_nonneg n) (pow_nonneg hBx0 n))]
  have hcauchy := hasSum_sum_range_mul_of_summable_norm hfnorm hgnorm
  rw [hf.tsum_eq, hg.tsum_eq] at hcauchy
  have hcauchy' : HasSum
      (fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      (((1 - B ^ 2 * t) ^ (-1 / 2 : ℝ)) *
        ((1 - D ^ 2 * t) ^ (-1 / 2 : ℝ))) := by
    simpa only [mul_comm] using hcauchy
  convert hcauchy' using 2 with n
  rw [centralBinomialDiagonalKernelCoefficient]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [f, g]
  rw [mul_pow, mul_pow]
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have htpow : t ^ n = t ^ k * t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [htpow]
  ring

/-- On the physical interval, the Cauchy-product sum is the positive square-root branch used in
`bernsteinSquareRootKernel`. -/
theorem hasSum_centralBinomialDiagonalKernelCoefficient_eq_kernel
    {B D t : ℝ} (ht : 0 < t)
    (hBt : B ^ 2 * t < 1) (hDt : D ^ 2 * t < 1) :
    HasSum
      (fun n : ℕ => centralBinomialDiagonalKernelCoefficient B D n * t ^ n)
      (bernsteinSquareRootKernel B D t) := by
  have hsum := hasSum_centralBinomialDiagonalKernelCoefficient ht.le hBt hDt
  convert hsum using 1
  rw [bernsteinSquareRootKernel]
  have hBpos : 0 < 1 - B ^ 2 * t := sub_pos.mpr hBt
  have hDpos : 0 < 1 - D ^ 2 * t := sub_pos.mpr hDt
  have hBhalf : (1 - B ^ 2 * t) ^ (-1 / 2 : ℝ) =
      1 / Real.sqrt (1 - B ^ 2 * t) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hBpos.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hDhalf : (1 - D ^ 2 * t) ^ (-1 / 2 : ℝ) =
      1 / Real.sqrt (1 - D ^ 2 * t) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hDpos.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  rw [hBhalf, hDhalf]
  field_simp [Real.sqrt_ne_zero'.2 hBpos, Real.sqrt_ne_zero'.2 hDpos]

end

end GaloisForLFunctions.HTGeometry
