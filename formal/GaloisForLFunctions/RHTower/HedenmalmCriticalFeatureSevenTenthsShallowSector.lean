import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureReflectedPairDirectFiveCenterCharge

/-!
# Seven-tenths shallow-band HCF sector gain

Route T makes zeros with real part at least `7/10` negligible relative to the canonical zero count.
For every remaining strict-right zero, the centered spectral displacement has absolute imaginary
part at most `1/5`.  On that thinner strip the real holomorphic square of every real-centered HCF
channel retains `23/25` of its Hermitian energy, rather than only the global `1/2`.

The gain follows from an exact sum-of-squares factorization.  Combining it with the sharp
three-center Hermitian minimum and the two next lattice centers gives the corresponding direct
five-center shallow charge.  This module proves the local analytic input only; it does not identify
the deep-band count with a finite Xi packet or prove the remaining source budget.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact denominator-sector factorization on the spectral strip of half-width `1/5`. -/
theorem criticalFeatureDenominator_shallow_sector_factorization (x y : ℝ) :
    (1 + x ^ 2 - y ^ 2) ^ 2 - 24 * (2 * x * y) ^ 2 =
      (x ^ 2 - (1 - y ^ 2)) ^ 2 +
        4 * x ^ 2 * (1 - 25 * y ^ 2) := by
  ring

/-- **Shallow-strip sector coercivity.**  If the transverse displacement is at most `1/5`, the
real holomorphic square of every real-centered critical feature controls `23/25` of its same-copy
Hermitian energy. -/
theorem twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
    (t : ℝ) {z : ℂ} (hy : |z.im| ≤ 1 / 5) :
    (23 / 25 : ℝ) * Complex.normSq (criticalFeatureCauchyKernelTest t z) ≤
      ((criticalFeatureCauchyKernelTest t z) ^ 2).re := by
  have hz : |z.im| < 1 / 2 := by linarith
  let x : ℝ := z.re - t
  let y : ℝ := z.im
  let A : ℝ := 1 + x ^ 2 - y ^ 2
  let B : ℝ := 2 * x * y
  let D : ℝ := A ^ 2 + B ^ 2
  have hy2 : y ^ 2 ≤ 1 / 25 := by
    have hsq := (sq_le_sq₀ (abs_nonneg y)
      (by norm_num : (0 : ℝ) ≤ 1 / 5)).2 (by simpa [y] using hy)
    rw [sq_abs] at hsq
    norm_num at hsq ⊢
    exact hsq
  have htwentyFive : 0 ≤ 1 - 25 * y ^ 2 := by linarith
  have hsector : 24 * B ^ 2 ≤ A ^ 2 := by
    have hid : A ^ 2 - 24 * B ^ 2 =
        (x ^ 2 - (1 - y ^ 2)) ^ 2 +
          4 * x ^ 2 * (1 - 25 * y ^ 2) := by
      simpa only [A, B] using
        criticalFeatureDenominator_shallow_sector_factorization x y
    have hright : 0 ≤
        (x ^ 2 - (1 - y ^ 2)) ^ 2 +
          4 * x ^ 2 * (1 - 25 * y ^ 2) := by positivity
    linarith
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hDpos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hApos, sq_nonneg B]
  have hden : Complex.normSq (1 + (z - (t : ℂ)) ^ 2) = D := by
    dsimp [D, A, B, x, y]
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re]
    ring
  have hre :
      ((2 / (1 + (z - (t : ℂ)) ^ 2)) ^ 2).re =
        4 * (A ^ 2 - B ^ 2) / D ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im]
    norm_num
    rw [hden]
    have hreDen : ((z - (t : ℂ)) ^ 2).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ 2).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    field_simp [ne_of_gt hDpos]
    ring
  have hnorm :
      Complex.normSq (2 / (1 + (z - (t : ℂ)) ^ 2)) = 4 / D := by
    rw [Complex.normSq_div]
    norm_num [Complex.normSq_apply]
    have hreDen : ((z - (t : ℂ)) ^ 2).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ 2).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    ring
  rw [criticalFeatureCauchyKernelTest_eq t hz, hre, hnorm]
  field_simp [ne_of_gt hDpos]
  nlinarith

/-- Direct five-center shallow-band holomorphic charge.  The thin-strip sector gain applies to all
five centers, while the Hermitian mass uses the exact three-center minimum plus both distance-two
channels. -/
theorem shallowDirectFiveCenterCriticalFeatureHolomorphicCharge_lower
    {t : ℝ} {z : ℂ} (hy : |z.im| ≤ 1 / 5)
    (ht : |z.re - t| ≤ 1 / 2) :
    (23 / 25 : ℝ) * (23232 / 4225 + 32 / 221 : ℝ) ≤
      ((criticalFeatureCauchyKernelTest (t - 2) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t - 1) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest t z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t + 1) z) ^ 2).re +
        ((criticalFeatureCauchyKernelTest (t + 2) z) ^ 2).re := by
  have hz : |z.im| < 1 / 2 := by linarith
  have hthree := sharp_threeCenterCriticalFeatureEnergy_lower hz ht
  have hmDist : |z.re - (t - 2)| ≤ 5 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hpDist : |z.re - (t + 2)| ≤ 5 / 2 := by
    rw [abs_le]
    rcases abs_le.mp ht with ⟨hl, hr⟩
    constructor <;> linarith
  have hmNorm :=
    sixteen_twoHundredTwentyOne_le_normSq_criticalFeatureCauchyKernelTest hz hmDist
  have hpNorm :=
    sixteen_twoHundredTwentyOne_le_normSq_criticalFeatureCauchyKernelTest hz hpDist
  have hm2Sector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t - 2) hy
  have hm1Sector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t - 1) hy
  have h0Sector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq t hy
  have hp1Sector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t + 1) hy
  have hp2Sector :=
    twentyThree_twentyFive_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
      (t + 2) hy
  rw [threeCenterCriticalFeatureEnergy] at hthree
  nlinarith

end


end RHTower
