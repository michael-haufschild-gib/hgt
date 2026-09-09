import GaloisForLFunctions.HTGeometry.DilatonOscillatorApplications
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integer tensor charges of the corpus's Gaussian dilaton

The tensor-charge construction of arXiv:2509.25276v7 section 5.2 multiplies the generating
log-weight by the integer charge. The shared-connection viewpoint of arXiv:2404.10461 then
predicts the same scaling of its logarithmic derivative. Here both laws act on the literal
Gaussian dilaton already used by the corpus's Schwartz oscillator. The finite-density sector
on the real line is characterized exactly, including zero and reversed charges.
-/

noncomputable section
open Polynomial MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- A real scaling of the existing Gaussian dilaton log-weight. -/
def gomesGaussianLogWeight (a : ℝ) : ℝ[X] := C a * gaussianDilatonLogWeight

/-- The integer tensor charge of a chosen generating scale. -/
def gomesGaussianTensorLogWeight (b : ℝ) (n : ℤ) : ℝ[X] := gomesGaussianLogWeight ((n : ℝ) * b)

/-- The literal dilaton density of the integer tensor charge. -/
def gomesGaussianTensorDensity (b : ℝ) (n : ℤ) : ℝ → ℝ :=
  dilatonWeight (gomesGaussianTensorLogWeight b n)

/-- Exact scaled Gaussian log-weight. -/
theorem gomesGaussianLogWeight_eval (a x : ℝ) :
    (gomesGaussianLogWeight a).eval x = -2 * Real.pi * a * x ^ 2 := by
  simp [gomesGaussianLogWeight, gaussianDilatonLogWeight]
  ring

/-- The first derivative is the common Gaussian connection coefficient. -/
theorem gomesGaussianLogWeight_derivative_eval (a x : ℝ) :
    (gomesGaussianLogWeight a).derivative.eval x = -4 * Real.pi * a * x := by
  simp [gomesGaussianLogWeight, gaussianDilatonLogWeight]
  ring

/-- The second derivative gives a constant charge-dependent curvature term. -/
theorem gomesGaussianLogWeight_second_derivative_eval (a x : ℝ) :
    (gomesGaussianLogWeight a).derivative.derivative.eval x = -4 * Real.pi * a := by
  simp [gomesGaussianLogWeight, gaussianDilatonLogWeight]
  ring

/-- Tensor addition is already exact at the polynomial log-weight level. -/
theorem gomesGaussianLogWeight_add (a c : ℝ) :
    gomesGaussianLogWeight (a + c) = gomesGaussianLogWeight a + gomesGaussianLogWeight c := by
  simp [gomesGaussianLogWeight, add_mul]

/-- Dualization negates the log-weight. -/
theorem gomesGaussianLogWeight_neg (a : ℝ) :
    gomesGaussianLogWeight (-a) = -gomesGaussianLogWeight a := by
  simp [gomesGaussianLogWeight]

/-- Unit scale is the corpus's existing oscillator log-weight. -/
theorem gomesGaussianLogWeight_one : gomesGaussianLogWeight 1 = gaussianDilatonLogWeight := by
  simp [gomesGaussianLogWeight]

/-- Integer tensor composition adds the polynomial charges. -/
theorem gomesGaussianTensorLogWeight_add (b : ℝ) (m n : ℤ) :
    gomesGaussianTensorLogWeight b (m + n) =
      gomesGaussianTensorLogWeight b m + gomesGaussianTensorLogWeight b n := by
  simp only [gomesGaussianTensorLogWeight, Int.cast_add, add_mul, gomesGaussianLogWeight_add]

/-- The scalar density agrees with the literal real Gaussian kernel. -/
theorem gomesGaussianTensorDensity_formula (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesGaussianTensorDensity b n x = Real.exp (-(2 * Real.pi * ((n : ℝ) * b)) * x ^ 2) := by
  rw [gomesGaussianTensorDensity, dilatonWeight, gomesGaussianTensorLogWeight,
    gomesGaussianLogWeight_eval]
  congr 1
  ring

/-- Tensor multiplication holds pointwise everywhere on the real line. -/
theorem gomesGaussianTensorDensity_add (b : ℝ) (m n : ℤ) (x : ℝ) :
    gomesGaussianTensorDensity b (m + n) x =
      gomesGaussianTensorDensity b m x * gomesGaussianTensorDensity b n x := by
  simp only [gomesGaussianTensorDensity, dilatonWeight, gomesGaussianTensorLogWeight_add,
    eval_add, Real.exp_add]

/-- The dual density is the reciprocal density at every real point. -/
theorem gomesGaussianTensorDensity_neg (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesGaussianTensorDensity b (-n) x = (gomesGaussianTensorDensity b n x)⁻¹ := by
  simp only [gomesGaussianTensorDensity, dilatonWeight, gomesGaussianTensorLogWeight,
    Int.cast_neg, neg_mul, gomesGaussianLogWeight_neg, eval_neg, Real.exp_neg]

/-- Gaussian charged densities never vanish. -/
theorem gomesGaussianTensorDensity_pos (b : ℝ) (n : ℤ) (x : ℝ) :
    0 < gomesGaussianTensorDensity b n x := dilatonWeight_pos _ x

/-- Every charge gives a continuous scalar density, whether or not its mass is finite. -/
theorem gomesGaussianTensorDensity_continuous (b : ℝ) (n : ℤ) :
    Continuous (gomesGaussianTensorDensity b n) := by
  unfold gomesGaussianTensorDensity dilatonWeight
  fun_prop

/-- Charged densities are the literal integer powers of the generating density. -/
theorem gomesGaussianTensorDensity_zpow (b : ℝ) (n : ℤ) (x : ℝ) :
    gomesGaussianTensorDensity b n x = (gomesGaussianTensorDensity b 1 x) ^ n := by
  rw [gomesGaussianTensorDensity_formula, gomesGaussianTensorDensity_formula]
  simp only [Int.cast_one, one_mul]
  rw [show -(2 * Real.pi * ((n : ℝ) * b)) * x ^ 2 =
    (-(2 * Real.pi * b) * x ^ 2) * (n : ℝ) by ring, Real.exp_mul, Real.rpow_intCast]

/-- Finiteness of the real-line density selects precisely the strictly positive effective charges. -/
theorem gomesGaussianTensorDensity_integrable_iff (b : ℝ) (n : ℤ) :
    Integrable (gomesGaussianTensorDensity b n) ↔ 0 < (n : ℝ) * b := by
  have hf : gomesGaussianTensorDensity b n =
      (fun x : ℝ => Real.exp (-(2 * Real.pi * ((n : ℝ) * b)) * x ^ 2)) :=
    funext (gomesGaussianTensorDensity_formula b n)
  rw [hf, integrable_exp_neg_mul_sq_iff]
  have hp : 0 < 2 * Real.pi := mul_pos (by linarith) Real.pi_pos
  constructor
  · intro h
    by_contra hq
    have hm := mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hq)
    linarith
  · intro h
    exact mul_pos hp h

/-- Every density differentiates with the charge-scaled Gaussian connection. -/
theorem gomesGaussianTensorDensity_hasDerivAt (b : ℝ) (n : ℤ) (x : ℝ) :
    HasDerivAt (gomesGaussianTensorDensity b n)
      (gomesGaussianTensorDensity b n x * (-4 * Real.pi * ((n : ℝ) * b) * x)) x := by
  change HasDerivAt (fun y => Real.exp ((gomesGaussianLogWeight ((n : ℝ) * b)).eval y))
    (Real.exp ((gomesGaussianLogWeight ((n : ℝ) * b)).eval x) *
      (-4 * Real.pi * ((n : ℝ) * b) * x)) x
  simpa only [gomesGaussianLogWeight_derivative_eval] using
    ((gomesGaussianLogWeight ((n : ℝ) * b)).hasDerivAt x).exp

/-- The logarithmic connection remembers only the effective charge. -/
theorem gomesGaussianTensorDensity_logDerivative (b : ℝ) (n : ℤ) (x : ℝ) :
    deriv (gomesGaussianTensorDensity b n) x / gomesGaussianTensorDensity b n x =
      -4 * Real.pi * ((n : ℝ) * b) * x := by
  rw [(gomesGaussianTensorDensity_hasDerivAt b n x).deriv]
  exact mul_div_cancel_left₀ _ (ne_of_gt (gomesGaussianTensorDensity_pos b n x))

/-- Equality of charged densities across generators is exactly equality of their effective charges. -/
theorem gomesGaussianTensorDensity_eq_iff (b c : ℝ) (m n : ℤ) :
    gomesGaussianTensorDensity b m = gomesGaussianTensorDensity c n ↔
      (m : ℝ) * b = (n : ℝ) * c := by
  constructor
  · intro h
    have he := congrFun h 1
    rw [gomesGaussianTensorDensity_formula, gomesGaussianTensorDensity_formula] at he
    have hx := Real.exp_injective he
    simp only [one_pow, mul_one, neg_inj] at hx
    exact mul_left_cancel₀ (ne_of_gt (mul_pos (by linarith : (0 : ℝ) < 2) Real.pi_pos)) hx
  · intro h
    simp only [gomesGaussianTensorDensity, gomesGaussianTensorLogWeight, h]

end GaloisForLFunctions.HTGeometry
