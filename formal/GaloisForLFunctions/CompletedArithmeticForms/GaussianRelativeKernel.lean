import GaloisForLFunctions.CompletedArithmeticForms.FirstAtomGaussianHorizon

/-!
# The physical source after its Gaussian factor is removed

The two-variable Hermite kernel retains the mixed Gaussian exponential before
absolute values are taken. Its source error is governed by the quartic reflection
defect and the literal affine first-atom factor.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- Complex reflection coordinate at the physical Gaussian length scale. -/
def gaussianReflectionCoordinate (q : ℝ) (z : ℂ) : ℂ :=
  2 * (Complex.I * (((Real.sqrt q : ℝ) : ℂ)⁻¹ * z))

/-- The exact source exponent after removal of its quadratic Gaussian term. -/
def gaussianRelativeExponent (q : ℝ) (z : ℂ) : ℂ :=
  -2 * (q : ℂ) * (Complex.cosh (gaussianReflectionCoordinate q z) - 1) - 4 * z ^ 2

/-- The literal first-atom affine correction in Gaussian coordinates. -/
def gaussianRelativeAffine (q : ℝ) (z : ℂ) : ℂ :=
  ((12 * q / (2 * q - 3) ^ 2 : ℝ) : ℂ) *
    (Complex.cosh (gaussianReflectionCoordinate q z) - 1)

/-- Physical first-atom profile divided by its entire Gaussian comparison. -/
def gaussianRelativeProfile (q : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-4 * z ^ 2) * firstAtomGaussianKernel q (gaussianReflectionCoordinate q z)

theorem norm_gaussianReflectionCoordinate_sq {q : ℝ} (hq : 0 < q) (z : ℂ) :
    ‖gaussianReflectionCoordinate q z‖ ^ 2 = 4 * ‖z‖ ^ 2 / q := by
  have hs := Real.sqrt_pos.mpr hq
  simp only [gaussianReflectionCoordinate, norm_mul, Complex.norm_I, one_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow, inv_pow, Real.sq_sqrt hq.le]
  norm_num
  ring

theorem gaussianReflectionCoordinate_quadratic {q : ℝ} (hq : 0 < q) (z : ℂ) :
    -(q : ℂ) * gaussianReflectionCoordinate q z ^ 2 = 4 * z ^ 2 := by
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
  have hqn : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  simp only [gaussianReflectionCoordinate, mul_pow, Complex.I_sq, inv_pow, hs]
  field_simp
  ring

/-- The entire exponent error is exactly the quartic hyperbolic remainder. -/
theorem gaussianRelativeExponent_eq_remainder {q : ℝ} (hq : 0 < q) (z : ℂ) :
    gaussianRelativeExponent q z = -2 * (q : ℂ) *
      (Complex.cosh (gaussianReflectionCoordinate q z) - 1 -
        gaussianReflectionCoordinate q z ^ 2 / 2) := by
  unfold gaussianRelativeExponent
  linear_combination gaussianReflectionCoordinate_quadratic hq z

/-- Exact exponential and affine factorization of the normalized physical source. -/
theorem gaussianRelativeProfile_factor (q : ℝ) (z : ℂ) :
    gaussianRelativeProfile q z =
      Complex.exp (gaussianRelativeExponent q z) * (1 - gaussianRelativeAffine q z) := by
  unfold gaussianRelativeProfile firstAtomGaussianKernel gaussianRelativeExponent gaussianRelativeAffine
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The literal two-variable source kernel in the Gaussian polynomial coordinates. -/
def firstAtomWickKernel (x : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp (-4 * z ^ 2 - 4 * w ^ 2) * firstAtomNormalizedRotatedPair x (z + w)

/-- The mixed Gaussian exponential survives exactly; only the source-relative factor changes. -/
theorem firstAtomWickKernel_eq_relativeProfile {x : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (z w : ℂ) :
    firstAtomWickKernel x z w = Complex.exp (8 * z * w) *
      gaussianRelativeProfile (thetaCuspSingleAtomReflectionScale 1 x) (z + w) := by
  rw [firstAtomWickKernel, firstAtomNormalizedRotatedPair_eq_kernel hq]
  unfold gaussianRelativeProfile gaussianReflectionCoordinate
  have he : -4 * z ^ 2 - 4 * w ^ 2 = 8 * z * w + -4 * (z + w) ^ 2 := by ring
  rw [he, Complex.exp_add, mul_assoc]

/-- On the unit disk the hyperbolic source increment has a quadratic absolute bound. -/
theorem norm_cosh_sub_one_le_quadratic {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖Complex.cosh w - 1‖ ≤ Real.exp 1 * ‖w‖ ^ 2 := by
  have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith only [hw, norm_nonneg w]
  have hw4 : ‖w‖ ^ 4 ≤ ‖w‖ ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg ‖w‖) (sub_nonneg.mpr hw2)]
  have hr := (norm_cosh_quadratic_remainder_le w).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hw) (by positivity))
  have hs := norm_add_le (Complex.cosh w - 1 - w ^ 2 / 2) (w ^ 2 / 2)
  rw [sub_add_cancel, norm_div, norm_pow] at hs
  norm_num only [Complex.norm_ofNat] at hs
  have hp := mul_le_mul_of_nonneg_right hw4 (Real.exp_pos (1 : ℝ)).le
  have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hc : 0 ≤ 23 * Real.exp (1 : ℝ) - 12 := by linarith only [he]
  nlinarith only [hr, hs, hp, mul_nonneg hc (sq_nonneg ‖w‖)]

/-- Absolute constant for the quartic relative source error. -/
def gaussianRelativeErrorConstant : ℝ :=
  50 * Real.exp 1 * Real.exp (2 * Real.exp 1)

theorem gaussianRelativeErrorConstant_pos : 0 < gaussianRelativeErrorConstant := by
  unfold gaussianRelativeErrorConstant
  positivity

/-- The normalized source differs from one by a quartic scale error on a growing disk. -/
theorem gaussianRelativeProfile_error_le {q R : ℝ} (hq : 3 ≤ q) (hR : 1 ≤ R)
    (hRq : 4 * R ^ 2 ≤ q) (hR4q : R ^ 4 ≤ q) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖gaussianRelativeProfile q z - 1‖ ≤ gaussianRelativeErrorConstant * R ^ 4 / q := by
  have hqp : 0 < q := by linarith only [hq]
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hRp : 0 < R := by linarith only [hR]
  have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hu2 : ‖gaussianReflectionCoordinate q z‖ ^ 2 ≤ 4 * R ^ 2 / q := by
    rw [norm_gaussianReflectionCoordinate_sq hqp]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 (by norm_num)) hqp.le
  have hu : ‖gaussianReflectionCoordinate q z‖ ≤ 1 := by
    have hb : 4 * R ^ 2 / q ≤ 1 := (div_le_one hqp).mpr hRq
    nlinarith only [hu2, hb, norm_nonneg (gaussianReflectionCoordinate q z)]
  have hu4 : ‖gaussianReflectionCoordinate q z‖ ^ 4 ≤ 16 * R ^ 4 / q ^ 2 := by
    have h := pow_le_pow_left₀ (sq_nonneg ‖gaussianReflectionCoordinate q z‖) hu2 2
    calc
      _ = (‖gaussianReflectionCoordinate q z‖ ^ 2) ^ 2 := by ring
      _ ≤ (4 * R ^ 2 / q) ^ 2 := h
      _ = _ := by rw [div_pow]; ring
  have hr : ‖Complex.cosh (gaussianReflectionCoordinate q z) - 1 -
      gaussianReflectionCoordinate q z ^ 2 / 2‖ ≤
      (16 * R ^ 4 / q ^ 2) / 24 * Real.exp 1 := by
    exact (norm_cosh_quadratic_remainder_le _).trans
      (mul_le_mul (div_le_div_of_nonneg_right hu4 (by norm_num))
        (Real.exp_le_exp.mpr hu) (Real.exp_pos _).le (by positivity))
  have hδ : R ^ 4 / q ≤ 1 := (div_le_one hqp).mpr hR4q
  have hδ0 : 0 ≤ R ^ 4 / q := by positivity
  have hE : ‖gaussianRelativeExponent q z‖ ≤ 2 * Real.exp 1 * (R ^ 4 / q) := by
    rw [gaussianRelativeExponent_eq_remainder hqp, norm_mul, norm_mul]
    norm_num only [norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hqp]
    calc
      _ ≤ (2 * q) * ((16 * R ^ 4 / q ^ 2) / 24 * Real.exp 1) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (4 * Real.exp 1 / 3) * (R ^ 4 / q) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [Real.exp_pos (1 : ℝ)]) hδ0
  have hEb : ‖gaussianRelativeExponent q z‖ ≤ 2 * Real.exp 1 := by
    apply hE.trans
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hδ (show 0 ≤ 2 * Real.exp (1 : ℝ) by positivity)
  have hB : q ^ 2 ≤ (2 * q - 3) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq)
      (show 0 ≤ 3 * q - 3 by linarith only [hq])]
  have hcoef : 12 * q / (2 * q - 3) ^ 2 ≤ 12 / q := by
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith only [hq])) hqp).mpr
    nlinarith only [hB]
  have hc : ‖Complex.cosh (gaussianReflectionCoordinate q z) - 1‖ ≤
      Real.exp 1 * (4 * R ^ 2 / q) :=
    (norm_cosh_sub_one_le_quadratic hu).trans
      (mul_le_mul_of_nonneg_left hu2 (Real.exp_pos _).le)
  have hR24 : R ^ 2 ≤ R ^ 4 := by
    have hR2 : 1 ≤ R ^ 2 := by nlinarith only [hR]
    nlinarith only [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hR2)]
  have hrq : R ^ 2 / q ^ 2 ≤ R ^ 4 / q := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hqp) hqp).mpr
    have h := mul_le_mul_of_nonneg_left hq1 (show 0 ≤ R ^ 4 by positivity)
    have h' := mul_le_mul_of_nonneg_right (hR24.trans (by simpa using h)) hqp.le
    nlinarith only [h']
  have hA : ‖gaussianRelativeAffine q z‖ ≤ 48 * Real.exp 1 * (R ^ 4 / q) := by
    rw [gaussianRelativeAffine, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 12 * q / (2 * q - 3) ^ 2)]
    calc
      _ ≤ (12 / q) * (Real.exp 1 * (4 * R ^ 2 / q)) :=
        mul_le_mul hcoef hc (norm_nonneg _) (by positivity)
      _ = 48 * Real.exp 1 * (R ^ 2 / q ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrq (by positivity)
  have he : ‖Complex.exp (gaussianRelativeExponent q z)‖ ≤ Real.exp (2 * Real.exp 1) :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hEb)
  have he1 : ‖Complex.exp (gaussianRelativeExponent q z) - 1‖ ≤
      (2 * Real.exp 1 * (R ^ 4 / q)) * Real.exp (2 * Real.exp 1) := by
    have h := norm_complex_exp_sub_sum_le_factorial_tail (gaussianRelativeExponent q z) 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      div_one, pow_one] at h
    exact h.trans (mul_le_mul hE (Real.exp_le_exp.mpr hEb) (Real.exp_pos _).le
      (by positivity))
  rw [gaussianRelativeProfile_factor]
  have hs : Complex.exp (gaussianRelativeExponent q z) * (1 - gaussianRelativeAffine q z) - 1 =
      (Complex.exp (gaussianRelativeExponent q z) - 1) -
        Complex.exp (gaussianRelativeExponent q z) * gaussianRelativeAffine q z := by ring
  rw [hs]
  calc
    _ ≤ ‖Complex.exp (gaussianRelativeExponent q z) - 1‖ +
        ‖Complex.exp (gaussianRelativeExponent q z) * gaussianRelativeAffine q z‖ :=
      norm_sub_le _ _
    _ ≤ (2 * Real.exp 1 * (R ^ 4 / q)) * Real.exp (2 * Real.exp 1) +
        Real.exp (2 * Real.exp 1) * (48 * Real.exp 1 * (R ^ 4 / q)) := by
      rw [norm_mul]
      exact add_le_add he1 (mul_le_mul he hA (norm_nonneg _) (Real.exp_pos _).le)
    _ = _ := by unfold gaussianRelativeErrorConstant; ring

/-- A factored mixed-kernel bound retains the Gaussian cancellation needed by Hermite tests. -/
theorem firstAtomWickKernel_error_le {x R : ℝ}
    (hq : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) (hR : 1 ≤ R)
    (hRq : 4 * R ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hR4q : R ^ 4 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    {z w : ℂ} (hzw : ‖z + w‖ ≤ R) :
    ‖firstAtomWickKernel x z w - Complex.exp (8 * z * w)‖ ≤
      gaussianRelativeErrorConstant * R ^ 4 / thetaCuspSingleAtomReflectionScale 1 x *
        Real.exp (8 * ‖z‖ * ‖w‖) := by
  rw [firstAtomWickKernel_eq_relativeProfile hq]
  rw [← mul_sub_one, norm_mul]
  have he : ‖Complex.exp (8 * z * w)‖ ≤ Real.exp (8 * ‖z‖ * ‖w‖) := by
    simpa only [norm_mul, Complex.norm_ofNat] using Complex.norm_exp_le_exp_norm (8 * z * w)
  calc
    _ ≤ Real.exp (8 * ‖z‖ * ‖w‖) *
        (gaussianRelativeErrorConstant * R ^ 4 / thetaCuspSingleAtomReflectionScale 1 x) :=
      mul_le_mul he (gaussianRelativeProfile_error_le hq hR hRq hR4q hzw)
        (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

#print axioms gaussianRelativeProfile_error_le
#print axioms firstAtomWickKernel_eq_relativeProfile
#print axioms firstAtomWickKernel_error_le

end GaloisForLFunctions.CompletedArithmeticForms
