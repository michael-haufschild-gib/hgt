import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureThreeCenterLatticeQuantum

/-!
# Height-local holomorphic coercivity for three critical-feature centers

On the nearest-center Voronoi cell, the central critical feature satisfies the sharp sector bound
`3/5`, improving the global single-channel factor `1/2`.  Combining this with the elementary
three-center Hermitian quantum gives the exact local holomorphic quantum `242/125`.

This result is deliberately local.  Selecting each zero's nearest three source channels depends on
the Xi divisor, while omitted holomorphic squares need not be nonnegative.  Therefore this theorem
does not by itself improve the source-only lattice budget or the global 75% receiver.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Sharp nearest-cell sector coercivity.**  A real-centered critical feature retains at least
`3/5` of its Hermitian energy when the spectral ordinate lies in its nearest-center cell. -/
theorem three_fifths_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (3 / 5 : ℝ) * Complex.normSq (criticalFeatureCauchyKernelTest t z) ≤
      ((criticalFeatureCauchyKernelTest t z) ^ (2 : ℕ)).re := by
  let x : ℝ := z.re - t
  let y : ℝ := z.im
  let A : ℝ := 1 + x ^ (2 : ℕ) - y ^ (2 : ℕ)
  let B : ℝ := 2 * x * y
  let D : ℝ := A ^ (2 : ℕ) + B ^ (2 : ℕ)
  have hx2 : x ^ (2 : ℕ) ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by simpa [x] using ht)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hy2 : y ^ (2 : ℕ) < 1 / 4 := by
    have h := (sq_lt_sq₀ (abs_nonneg y)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by simpa [y] using hz)
    rw [sq_abs] at h
    norm_num at h ⊢
    exact h
  have hab : 2 * |x| * |y| ≤ x ^ (2 : ℕ) + y ^ (2 : ℕ) := by
    have hsq := sq_nonneg (|x| - |y|)
    nlinarith [sq_abs x, sq_abs y]
  have hcell : x ^ (2 : ℕ) + 3 * y ^ (2 : ℕ) ≤ 1 := by nlinarith
  have hlinear : 4 * |x| * |y| ≤ A := by
    dsimp only [A]
    nlinarith
  have hBabs : |B| = 2 * |x| * |y| := by
    simp [B, abs_mul]
  have hApos : 0 < A := by
    dsimp only [A]
    nlinarith [sq_nonneg x]
  have hsector : 4 * B ^ (2 : ℕ) ≤ A ^ (2 : ℕ) := by
    have htwo : 2 * |B| ≤ A := by
      rw [hBabs]
      nlinarith
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2 * |B|) hApos.le).2 htwo
    nlinarith [sq_abs B]
  have hDpos : 0 < D := by
    dsimp only [D]
    nlinarith [sq_pos_of_pos hApos, sq_nonneg B]
  have hden : Complex.normSq (1 + (z - (t : ℂ)) ^ (2 : ℕ)) = D := by
    dsimp [D, A, B, x, y]
    rw [Complex.normSq_apply]
    simp [pow_two, Complex.mul_re]
    ring
  have hre :
      ((2 / (1 + (z - (t : ℂ)) ^ (2 : ℕ))) ^ (2 : ℕ)).re =
        4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / D ^ (2 : ℕ) := by
    rw [pow_two, Complex.mul_re, Complex.div_re, Complex.div_im]
    norm_num
    rw [hden]
    have hreDen : ((z - (t : ℂ)) ^ (2 : ℕ)).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ (2 : ℕ)).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    field_simp [ne_of_gt hDpos]
    ring
  have hnorm :
      Complex.normSq (2 / (1 + (z - (t : ℂ)) ^ (2 : ℕ))) = 4 / D := by
    rw [Complex.normSq_div]
    norm_num [Complex.normSq_apply]
    have hreDen : ((z - (t : ℂ)) ^ (2 : ℕ)).re = A - 1 := by
      dsimp [A, x, y]
      simp [pow_two, Complex.mul_re]
      ring
    have himDen : ((z - (t : ℂ)) ^ (2 : ℕ)).im = B := by
      dsimp [B, x, y]
      simp [pow_two, Complex.mul_im]
      ring
    rw [hreDen, himDen]
    ring
  rw [criticalFeatureCauchyKernelTest_eq t hz, hre, hnorm]
  have hnumerator : (3 / 5 : ℝ) * 4 * D ≤ 4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) := by
    dsimp only [D]
    nlinarith only [hsector]
  calc
    (3 / 5 : ℝ) * (4 / D) = ((3 / 5 : ℝ) * 4 * D) / D ^ (2 : ℕ) := by
      field_simp [ne_of_gt hDpos]
    _ ≤ 4 * (A ^ (2 : ℕ) - B ^ (2 : ℕ)) / D ^ (2 : ℕ) :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hDpos)).2 hnumerator

/-- **Local three-center holomorphic quantum.**  Nearest-channel `3/5` coercivity, global `1/2`
coercivity for both neighbours, central Hermitian mass `64/25`, and elementary total mass `84/25`
give the exact local source floor `242/125`. -/
theorem twoHundredFortyTwo_oneHundredTwentyFifths_le_threeCenter_re_sq_sum
    {t : ℝ} {z : ℂ} (hz : |z.im| < 1 / 2)
    (ht : |z.re - t| ≤ 1 / 2) :
    (242 / 125 : ℝ) ≤
      ((criticalFeatureCauchyKernelTest (t - 1) z) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest t z) ^ (2 : ℕ)).re +
        ((criticalFeatureCauchyKernelTest (t + 1) z) ^ (2 : ℕ)).re := by
  have hcenterSector :=
    three_fifths_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq t hz ht
  have hminusSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t - 1) hz
  have hplusSector :=
    half_mul_normSq_criticalFeatureCauchyKernelTest_le_re_sq (t + 1) hz
  have htotal := eightyFour_twentyFive_le_threeCenterCriticalFeatureEnergy hz ht
  have hcenter : (64 / 25 : ℝ) ≤
      Complex.normSq (criticalFeatureCauchyKernelTest t z) := by
    have heval := normSq_criticalEvaluation_realCriticalFeature_ge_of_abs_sub_le_half
      (t := t) (z := z) hz ht
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum] at heval
    exact heval
  rw [threeCenterCriticalFeatureEnergy] at htotal
  nlinarith

end

end RHTower
