import GaloisForLFunctions.ArithmeticCriticalityTheory.CurvedGaugeArchimedeanBounds
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# A polynomial lower bound for the Gamma kernel

The reciprocal sinh and cosh polynomials retain their terms through degree
fourteen. Multiplication by finite exponential bounds proves the inequalities
on the whole unit interval, without a power-series convergence assumption.
-/

noncomputable section
open Real
open _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty

/-- Degree-fourteen reciprocal polynomial for `sinh z / z`. -/
def gammaSinhPolynomial14 (z : ℝ) : ℝ :=
  1 - z ^ 2 / 6 + 7 * z ^ 4 / 360 - 31 * z ^ 6 / 15120 +
    127 * z ^ 8 / 604800 - 73 * z ^ 10 / 3421440 +
    1414477 * z ^ 12 / 653837184000 - 8191 * z ^ 14 / 37362124800

/-- Degree-fourteen reciprocal polynomial for `cosh z`. -/
def gammaCoshPolynomial14 (z : ℝ) : ℝ :=
  1 - z ^ 2 / 2 + 5 * z ^ 4 / 24 - 61 * z ^ 6 / 720 +
    1385 * z ^ 8 / 40320 - 50521 * z ^ 10 / 3628800 +
    2702765 * z ^ 12 / 479001600 - 199360981 * z ^ 14 / 87178291200

private def sinhTaylor15 (z : ℝ) : ℝ :=
  z + z ^ 3 / 6 + z ^ 5 / 120 + z ^ 7 / 5040 + z ^ 9 / 362880 +
    z ^ 11 / 39916800 + z ^ 13 / 6227020800 + z ^ 15 / 1307674368000

private def coshTaylor16 (z : ℝ) : ℝ :=
  1 + z ^ 2 / 2 + z ^ 4 / 24 + z ^ 6 / 720 + z ^ 8 / 40320 +
    z ^ 10 / 3628800 + z ^ 12 / 479001600 + z ^ 14 / 87178291200 +
    z ^ 16 / 20922789888000

private theorem hyperbolic_taylor_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    |Real.sinh z - sinhTaylor15 z| ≤ z ^ 17 / 300000000000000 ∧
      |Real.cosh z - coshTaylor16 z| ≤ z ^ 17 / 300000000000000 := by
  have hz : |z| ≤ 1 := by rwa [abs_of_nonneg h0]
  have hnz : |-z| ≤ 1 := by simpa only [abs_neg] using hz
  have hp := Real.exp_bound hz (n := 17) (by norm_num)
  have hm := Real.exp_bound hnz (n := 17) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_neg, abs_of_nonneg h0] at hp hm
  obtain ⟨hpl, hpu⟩ := abs_le.mp hp
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  have h17 := pow_nonneg h0 17
  constructor
  · rw [Real.sinh_eq, abs_le]
    dsimp only [sinhTaylor15]
    constructor <;> nlinarith only [hpl, hpu, hml, hmu, h17]
  · rw [Real.cosh_eq, abs_le]
    dsimp only [coshTaylor16]
    constructor <;> nlinarith only [hpl, hpu, hml, hmu, h17]

private theorem reciprocal_polynomial_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    0 ≤ gammaSinhPolynomial14 z ∧ gammaSinhPolynomial14 z ≤ 2 ∧
      0 ≤ gammaCoshPolynomial14 z ∧ gammaCoshPolynomial14 z ≤ 2 := by
  have hb (n : ℕ) : 0 ≤ z ^ n ∧ z ^ n ≤ 1 :=
    ⟨pow_nonneg h0 n, by simpa only [one_pow] using pow_le_pow_left₀ h0 h1 n⟩
  dsimp only [gammaSinhPolynomial14, gammaCoshPolynomial14]
  constructor
  · linarith only [(hb 2).2, (hb 4).1, (hb 6).2, (hb 8).1,
      (hb 10).2, (hb 12).1, (hb 14).2]
  constructor
  · linarith only [(hb 2).1, (hb 4).2, (hb 6).1, (hb 8).2,
      (hb 10).1, (hb 12).2, (hb 14).1]
  constructor
  · linarith only [(hb 2).2, (hb 4).1, (hb 6).2, (hb 8).1,
      (hb 10).2, (hb 12).1, (hb 14).2]
  · linarith only [(hb 2).1, (hb 4).2, (hb 6).1, (hb 8).2,
      (hb 10).1, (hb 12).2, (hb 14).1]

private theorem reciprocal_polynomial_products {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    gammaSinhPolynomial14 z * sinhTaylor15 z +
        2 * z ^ 17 / 300000000000000 ≤ z ∧
      gammaCoshPolynomial14 z * coshTaylor16 z +
        2 * z ^ 17 / 300000000000000 ≤ 1 := by
  have hn (n : ℕ) : 0 ≤ z ^ n := pow_nonneg h0 n
  have h17 : z ^ 17 ≤ z ^ 16 := pow_le_pow_of_le_one h0 h1 (by norm_num)
  constructor
  · dsimp only [gammaSinhPolynomial14, sinhTaylor15]
    ring_nf
    linarith only [hn 17, hn 19, hn 21, hn 23, hn 25, hn 27, hn 29]
  · dsimp only [gammaCoshPolynomial14, coshTaylor16]
    ring_nf
    linarith only [h17, hn 16, hn 18, hn 20, hn 22, hn 24, hn 26, hn 28, hn 30]

private theorem reciprocal_polynomial_product_errors {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    z - gammaSinhPolynomial14 z * sinhTaylor15 z +
        2 * z ^ 17 / 300000000000000 ≤ z ^ 17 / 10000000 ∧
      1 - gammaCoshPolynomial14 z * coshTaylor16 z +
        2 * z ^ 17 / 300000000000000 ≤ z ^ 16 / 500 := by
  have hn (n : ℕ) : 0 ≤ z ^ n := pow_nonneg h0 n
  have hp (m n : ℕ) (h : m ≤ n) : z ^ n ≤ z ^ m := pow_le_pow_of_le_one h0 h1 h
  constructor
  · dsimp only [gammaSinhPolynomial14, sinhTaylor15]
    ring_nf
    linarith only [hn 17, hp 17 19 (by norm_num), hp 17 21 (by norm_num),
      hp 17 23 (by norm_num), hp 17 25 (by norm_num), hp 17 27 (by norm_num),
      hp 17 29 (by norm_num)]
  · dsimp only [gammaCoshPolynomial14, coshTaylor16]
    ring_nf
    linarith only [hn 16, hp 16 17 (by norm_num), hp 16 18 (by norm_num),
      hp 16 20 (by norm_num), hp 16 22 (by norm_num), hp 16 24 (by norm_num),
      hp 16 26 (by norm_num), hp 16 28 (by norm_num), hp 16 30 (by norm_num)]

/-- The degree-fourteen reciprocal bounds hold throughout the unit interval. -/
theorem gamma_reciprocal_polynomials14_lower {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1) :
    gammaSinhPolynomial14 z ≤ z / Real.sinh z ∧
      gammaCoshPolynomial14 z ≤ 1 / Real.cosh z := by
  obtain ⟨hS, hC⟩ := hyperbolic_taylor_bounds h0.le h1
  have hSu := (abs_le.mp hS).2
  have hCu := (abs_le.mp hC).2
  obtain ⟨hP0, hP2, hQ0, hQ2⟩ := reciprocal_polynomial_bounds h0.le h1
  obtain ⟨hPS, hQC⟩ := reciprocal_polynomial_products h0.le h1
  have hrem : 0 ≤ z ^ 17 / 300000000000000 := by positivity
  constructor
  · apply (le_div_iff₀ (Real.sinh_pos_iff.mpr h0)).mpr
    have h := mul_le_mul_of_nonneg_left hSu hP0
    have hr := mul_le_mul_of_nonneg_right hP2 hrem
    nlinarith only [h, hr, hPS]
  · apply (le_div_iff₀ (Real.cosh_pos z)).mpr
    have h := mul_le_mul_of_nonneg_left hCu hQ0
    have hr := mul_le_mul_of_nonneg_right hQ2 hrem
    nlinarith only [h, hr, hQC]

/-- The discarded reciprocal terms have explicit sixteenth-order error bounds. -/
theorem gamma_reciprocal_polynomials14_errors {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 1) :
    z / Real.sinh z - gammaSinhPolynomial14 z ≤ z ^ 16 / 10000000 ∧
      1 / Real.cosh z - gammaCoshPolynomial14 z ≤ z ^ 16 / 500 := by
  obtain ⟨hS, hC⟩ := hyperbolic_taylor_bounds h0.le h1
  have hSl := (abs_le.mp hS).1
  have hCl := (abs_le.mp hC).1
  obtain ⟨hP0, hP2, hQ0, hQ2⟩ := reciprocal_polynomial_bounds h0.le h1
  obtain ⟨hPS, hQC⟩ := reciprocal_polynomial_product_errors h0.le h1
  obtain ⟨hs, _, hc, _⟩ := sinh_cosh_taylor_bounds h0.le h1
  have hrem : 0 ≤ z ^ 17 / 300000000000000 := by positivity
  constructor
  · have hprod := mul_le_mul_of_nonneg_left hSl hP0
    have herr := mul_le_mul_of_nonneg_right hP2 hrem
    have hs' : z ≤ Real.sinh z := by nlinarith only [hs, pow_nonneg h0.le 3]
    have hscale := mul_le_mul_of_nonneg_left hs'
      (show 0 ≤ z ^ 16 / 10000000 by positivity)
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ (Real.sinh_pos_iff.mpr h0)).mpr
    nlinarith only [hprod, herr, hPS, hscale]
  · have hprod := mul_le_mul_of_nonneg_left hCl hQ0
    have herr := mul_le_mul_of_nonneg_right hQ2 hrem
    have hc' : 1 ≤ Real.cosh z := by nlinarith only [hc, sq_nonneg z]
    have hscale := mul_le_mul_of_nonneg_left hc'
      (show 0 ≤ z ^ 16 / 500 by positivity)
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ (Real.cosh_pos z)).mpr
    nlinarith only [hprod, herr, hQC, hscale]

/-- A higher-order Gamma lower kernel valid across the prime-five boundary. -/
theorem archLevySinhWeight_ge_polynomial14 {t : ℝ} (h0 : 0 < t) (h2 : t ≤ 2) :
    gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2 ≤
      archLevySinhWeight t := by
  obtain ⟨hs, hc⟩ := gamma_reciprocal_polynomials14_lower
    (z := t / 2) (by linarith only [h0]) (by linarith only [h2])
  have he : archLevySinhWeight t =
      1 / (2 * Real.sinh (t / 2)) + 1 / (2 * Real.cosh (t / 2)) := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq h0,
      archLevyDensity_eq_inv_sinh_add_inv_cosh h0]
    ring
  have hs' := div_le_div_of_nonneg_right hs h0.le
  have hc' := div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)
  have hden : Real.sinh (t / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith only [h0])).ne'
  have hid : ((t / 2) / Real.sinh (t / 2)) / t = 1 / (2 * Real.sinh (t / 2)) := by
    field_simp [h0.ne', hden]
  rw [hid] at hs'
  rw [show 1 / Real.cosh (t / 2) / 2 = 1 / (2 * Real.cosh (t / 2)) by ring] at hc'
  rw [he]
  linarith only [hs', hc']

/-- Through diameter `11/10`, the lower kernel loses at most `10⁻⁷` pointwise. -/
theorem archLevySinhWeight_polynomial14_error {t : ℝ} (h0 : 0 < t)
    (h2 : t ≤ 11 / 10) :
    0 ≤ archLevySinhWeight t -
        (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2) ∧
      archLevySinhWeight t -
        (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2) ≤
          1 / 10000000 := by
  have hz0 : 0 ≤ t / 2 := by linarith only [h0]
  have hz1 : t / 2 ≤ 1 := by linarith only [h2]
  have hzq : t / 2 ≤ 11 / 20 := by linarith only [h2]
  refine ⟨sub_nonneg.mpr (archLevySinhWeight_ge_polynomial14 h0
    (by linarith only [h2])), ?_⟩
  obtain ⟨hs, hc⟩ := gamma_reciprocal_polynomials14_errors
    (z := t / 2) (by linarith only [h0]) hz1
  have hs' := div_le_div_of_nonneg_right hs h0.le
  have hc' := div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)
  have hden : Real.sinh (t / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith only [h0])).ne'
  have hcden : Real.cosh (t / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have he : archLevySinhWeight t -
      (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2) =
        ((t / 2) / Real.sinh (t / 2) - gammaSinhPolynomial14 (t / 2)) / t +
          (1 / Real.cosh (t / 2) - gammaCoshPolynomial14 (t / 2)) / 2 := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq h0,
      archLevyDensity_eq_inv_sinh_add_inv_cosh h0]
    field_simp [h0.ne', hden, hcden]
    ring
  have hscale : ((t / 2) ^ 16 / 10000000) / t = (t / 2) ^ 15 / 20000000 := by
    field_simp [h0.ne']
    ring
  rw [hscale] at hs'
  have h15 := pow_le_pow_left₀ hz0 hzq 15
  have h16 := pow_le_pow_left₀ hz0 hzq 16
  norm_num at h15 h16
  rw [he]
  linarith only [hs', hc', h15, h16]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_reciprocal_polynomials14_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gamma_reciprocal_polynomials14_errors
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.archLevySinhWeight_ge_polynomial14
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.archLevySinhWeight_polynomial14_error
