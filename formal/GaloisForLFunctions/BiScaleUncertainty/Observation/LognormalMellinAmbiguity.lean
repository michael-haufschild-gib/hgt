import GaloisForLFunctions.RHTower.WD.MomentsDoNotDetermineTheLogMean

/-!
# Complex moments beyond integer sampling

Sinusoidally perturbed Gaussian densities are normalized and nonnegative.
For `X = exp Y`, all integer Mellin moments and their shift recurrence are
independent of the perturbation. The full complex moment formula identifies
its invisible coefficient from a single quarter-order moment.
-/

open MeasureTheory Complex
open GaloisForLFunctions.RHTower.WD
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

/-- The normalized Gaussian exponential kernel. -/
def gaussianMomentKernel (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp (-(1 / 2 : ℂ) * (y : ℂ)^2 + z * y) /
    (Real.sqrt (2 * Real.pi) : ℂ)

lemma integrable_gaussianMomentKernel (z : ℂ) : Integrable (gaussianMomentKernel z) :=
  (integrable_cexp_gauss z).div_const _

lemma integral_gaussianMomentKernel (z : ℂ) :
    ∫ y, gaussianMomentKernel z y = Complex.exp (z^2 / 2) := by
  unfold gaussianMomentKernel
  rw [integral_div, integral_cexp_gauss]
  have h : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)).ne'
  exact mul_div_cancel_left₀ _ h

/-- A sinusoidal tilt is a difference of two imaginary Gaussian shifts. -/
private lemma sin_exponential (z : ℂ) :
    Complex.sin z = (Complex.exp (z*I) - Complex.exp (-(z*I))) / (2*I) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).2
  have h := Complex.two_sin (x := z)
  rw [neg_mul] at h
  linear_combination I * h + (Complex.exp (-(z*I)) - Complex.exp (z*I)) * Complex.I_sq

lemma gaussianMomentKernel_mul_sin (z : ℂ) (q y : ℝ) :
    gaussianMomentKernel z y * (Real.sin (q*y) : ℂ) =
      (gaussianMomentKernel (z + q * I) y - gaussianMomentKernel (z - q * I) y) /
        (2 * I) := by
  rw [Complex.ofReal_sin, sin_exponential]
  unfold gaussianMomentKernel
  have hp : -(1 / 2 : ℂ) * (y : ℂ)^2 + (z + q*I)*y =
      (-(1 / 2 : ℂ)*(y : ℂ)^2 + z*y) + (q*y)*I := by ring
  have hm : -(1 / 2 : ℂ) * (y : ℂ)^2 + (z - q*I)*y =
      (-(1 / 2 : ℂ)*(y : ℂ)^2 + z*y) + -((q*y)*I) := by ring
  rw [hp, hm]
  simp only [Complex.exp_add]
  simp only [Complex.ofReal_mul]
  ring

lemma integrable_gaussianMomentKernel_mul_sin (z : ℂ) (q : ℝ) :
    Integrable (fun y => gaussianMomentKernel z y * (Real.sin (q*y) : ℂ)) := by
  simp_rw [gaussianMomentKernel_mul_sin]
  exact ((integrable_gaussianMomentKernel _).sub (integrable_gaussianMomentKernel _)).div_const _

/-- Gaussian integration retains the full complex Mellin variable, not only integer samples. -/
theorem integral_gaussianMomentKernel_mul_sin (z : ℂ) (q : ℝ) :
    (∫ y, gaussianMomentKernel z y * (Real.sin (q*y) : ℂ)) =
      Complex.exp (z^2/2 - (q : ℂ)^2/2) * Complex.sin (q*z) := by
  simp_rw [gaussianMomentKernel_mul_sin]
  rw [integral_div, integral_sub (integrable_gaussianMomentKernel _)
    (integrable_gaussianMomentKernel _), integral_gaussianMomentKernel,
    integral_gaussianMomentKernel, sin_exponential]
  have hp : (z + (q : ℂ)*I)^2/2 = z^2/2 - (q : ℂ)^2/2 + (q*z)*I := by
    linear_combination ((q : ℂ)^2/2) * Complex.I_sq
  have hm : (z - (q : ℂ)*I)^2/2 = z^2/2 - (q : ℂ)^2/2 + -((q*z)*I) := by
    linear_combination ((q : ℂ)^2/2) * Complex.I_sq
  rw [hp, hm]
  simp only [Complex.exp_add]
  ring

/-- Positive Gaussian densities with a bounded sinusoidal perturbation. -/
def gaussianSineDensity (θ q y : ℝ) : ℝ :=
  gaussWeight y * (1 + Real.sin θ * Real.sin (q*y)) / Real.sqrt (2*Real.pi)

/-- Positivity is built into the parametrization; no positivity hypothesis is needed. -/
theorem gaussianSineDensity_nonneg (θ q y : ℝ) : 0 ≤ gaussianSineDensity θ q y := by
  have h : |Real.sin θ * Real.sin (q*y)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _)
  exact div_nonneg (mul_nonneg (gaussWeight_pos y).le (by linarith [(abs_le.mp h).1]))
    (Real.sqrt_nonneg _)

lemma exp_mul_gaussianSineDensity (θ q : ℝ) (z : ℂ) (y : ℝ) :
    Complex.exp (z*y) * (gaussianSineDensity θ q y : ℂ) =
      gaussianMomentKernel z y + (Real.sin θ : ℂ) *
        (gaussianMomentKernel z y * (Real.sin (q*y) : ℂ)) := by
  unfold gaussianSineDensity gaussianMomentKernel gaussWeight
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  have he : -(1/2 : ℂ)*(y : ℂ)^2 + z*y = z*y + -((y : ℂ)^2/2) := by ring
  rw [he, Complex.exp_add]
  ring

lemma integrable_exp_mul_gaussianSineDensity (θ q : ℝ) (z : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (z*y) * (gaussianSineDensity θ q y : ℂ)) := by
  simp_rw [exp_mul_gaussianSineDensity]
  exact (integrable_gaussianMomentKernel z).add
    ((integrable_gaussianMomentKernel_mul_sin z q).const_mul _)

/-- Exact complex moments of the positive sinusoidal family. -/
theorem integral_exp_mul_gaussianSineDensity (θ q : ℝ) (z : ℂ) :
    (∫ y : ℝ, Complex.exp (z*y) * (gaussianSineDensity θ q y : ℂ)) =
      Complex.exp (z^2/2) *
        (1 + (Real.sin θ : ℂ) * Complex.exp (-((q : ℂ)^2/2)) * Complex.sin (q*z)) := by
  simp_rw [exp_mul_gaussianSineDensity]
  rw [integral_add (integrable_gaussianMomentKernel _)
    ((integrable_gaussianMomentKernel_mul_sin _ _).const_mul _), integral_const_mul,
    integral_gaussianMomentKernel, integral_gaussianMomentKernel_mul_sin,
    sub_eq_add_neg, Complex.exp_add]
  ring

/-- Every perturbation has total mass one. -/
theorem integral_gaussianSineDensity (θ q : ℝ) : ∫ y, gaussianSineDensity θ q y = 1 := by
  have h := integral_exp_mul_gaussianSineDensity θ q 0
  simp only [zero_mul, Complex.exp_zero, one_mul, zero_pow (by omega : (2:ℕ) ≠ 0),
    zero_div, mul_zero, Complex.sin_zero, add_zero] at h
  have hint := integrable_exp_mul_gaussianSineDensity θ q 0
  simp only [zero_mul, Complex.exp_zero, one_mul] at hint
  have hr := congrArg Complex.re h
  have hre := integral_re hint
  simp only [RCLike.re_to_complex] at hre
  rw [← hre] at hr
  simpa using hr

/-- The Mellin moments of `X = exp Y` on the integer-invisible Gaussian family. -/
def lognormalSineMoment (θ : ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ, Complex.exp (z*y) * (gaussianSineDensity θ (2*Real.pi) y : ℂ)

lemma lognormalSineMoment_eq (θ : ℝ) (z : ℂ) :
    lognormalSineMoment θ z = Complex.exp (z^2/2) *
      (1 + (Real.sin θ : ℂ) * Complex.exp (-2*(Real.pi : ℂ)^2) *
        Complex.sin (2*Real.pi*z)) := by
  rw [lognormalSineMoment, integral_exp_mul_gaussianSineDensity]
  congr 3
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

/-- All integer Mellin samples forget the perturbation. -/
theorem lognormalSineMoment_int (θ : ℝ) (k : ℤ) :
    lognormalSineMoment θ k = Complex.exp ((k : ℂ)^2/2) := by
  rw [lognormalSineMoment_eq]
  have h : Complex.sin (2*Real.pi*(k : ℂ)) = 0 := by
    have h := Complex.sin_add_int_mul_two_pi 0 k
    simpa only [zero_add, Complex.sin_zero, mul_comm] using h
  rw [h]
  ring

/-- The same difference equation holds for every member of the indistinguishable family. -/
theorem lognormalSineMoment_shift (θ : ℝ) (z : ℂ) :
    lognormalSineMoment θ (z+1) = Complex.exp (z+1/2) * lognormalSineMoment θ z := by
  rw [lognormalSineMoment_eq, lognormalSineMoment_eq,
    show (2 : ℂ)*Real.pi*(z+1) = 2*Real.pi*z + 2*Real.pi by ring,
    Complex.sin_add_two_pi,
    show (z+1)^2/2 = (z+1/2) + z^2/2 by ring, Complex.exp_add, mul_assoc]

/-- A quarter moment detects exactly the coefficient hidden from every integer moment. -/
theorem lognormalSineMoment_quarter (θ : ℝ) :
    lognormalSineMoment θ (1/4) = Complex.exp (1/32) *
      (1 + (Real.sin θ : ℂ) * Complex.exp (-2*(Real.pi : ℂ)^2)) := by
  rw [lognormalSineMoment_eq]
  norm_num only
  rw [show (2 : ℂ)*Real.pi*(1/4) = (Real.pi : ℂ)/2 by ring, Complex.sin_pi_div_two,
    mul_one]

/-- One fractional moment restores identification within this entire positive family. -/
theorem lognormalSineMoment_quarter_eq_iff (θ φ : ℝ) :
    lognormalSineMoment θ (1/4) = lognormalSineMoment φ (1/4) ↔
      Real.sin θ = Real.sin φ := by
  rw [lognormalSineMoment_quarter, lognormalSineMoment_quarter,
    mul_right_inj' (Complex.exp_ne_zero _), add_right_inj,
    mul_left_inj' (Complex.exp_ne_zero _), Complex.ofReal_inj]

/-- The normalized nonnegative densities are integrable. -/
theorem integrable_gaussianSineDensity (θ q : ℝ) : Integrable (gaussianSineDensity θ q) := by
  have h := (integrable_exp_mul_gaussianSineDensity θ q 0).re
  simpa only [zero_mul, Complex.exp_zero, one_mul, RCLike.re_to_complex,
    Complex.ofReal_re] using h

/-- Equal integer moments and equal shift recurrences coexist with distinct positive laws. -/
theorem lognormalSineDensity_distinct :
    gaussianSineDensity 0 (2*Real.pi) ≠ gaussianSineDensity (Real.pi/2) (2*Real.pi) := by
  intro h
  have hm : lognormalSineMoment 0 (1/4) = lognormalSineMoment (Real.pi/2) (1/4) := by
    unfold lognormalSineMoment
    rw [h]
  have hs := (lognormalSineMoment_quarter_eq_iff 0 (Real.pi/2)).mp hm
  norm_num only [Real.sin_zero, Real.sin_pi_div_two] at hs

#print axioms lognormalSineDensity_distinct
#print axioms gaussianSineDensity_nonneg
#print axioms integrable_gaussianSineDensity
#print axioms integral_exp_mul_gaussianSineDensity
#print axioms integral_gaussianSineDensity
#print axioms lognormalSineMoment_int
#print axioms lognormalSineMoment_shift
#print axioms lognormalSineMoment_quarter_eq_iff

end
end GaloisForLFunctions.BiScaleUncertainty.Observation
