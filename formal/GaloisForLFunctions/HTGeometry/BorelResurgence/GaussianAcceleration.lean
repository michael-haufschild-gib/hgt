import GaloisForLFunctions.HTGeometry.RiemannGaussian.GaussianHeat
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gaussian acceleration from Borel level one to level two

The kernel `exp (-x² / (4t)) / sqrt (πt)` averages the positive half-line. Its action on quadratic
exponentials is an inverse square root. The integrability criterion is stated separately from
the value of Lean's totalized integral, so a zero outside the convergence region is never
interpreted as a resummation.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real level-one to level-two acceleration kernel. -/
def gaussianAccelerationKernel (t x : ℝ) : ℝ :=
  (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * x ^ 2)

/-- Gaussian acceleration along the positive real Borel ray. -/
def gaussianAcceleration (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), gaussianAccelerationKernel t x * f x

/-- Acceleration uses the same Gaussian family as heat broadening. -/
theorem gaussianAccelerationKernel_eq_translatedGaussian (t x : ℝ) :
    gaussianAccelerationKernel t x =
      (Real.sqrt (Real.pi * t))⁻¹ *
        RiemannGaussian.translatedGaussian ((4 * t)⁻¹) 0 x := by
  simp only [gaussianAccelerationKernel, RiemannGaussian.translatedGaussian, sub_zero]

theorem gaussianAccelerationKernel_nonneg (t x : ℝ) :
    0 ≤ gaussianAccelerationKernel t x := by
  unfold gaussianAccelerationKernel
  positivity

theorem gaussianAccelerationKernel_exp_pos (s x : ℝ) :
    0 < gaussianAccelerationKernel (Real.exp s) x := by
  unfold gaussianAccelerationKernel
  positivity

/-- Multiplication by quadratic growth changes the Gaussian's inverse variance. -/
theorem gaussianAccelerationKernel_mul_quadratic (t a x : ℝ) :
    gaussianAccelerationKernel t x * Real.exp (a * x ^ 2) =
      (Real.sqrt (Real.pi * t))⁻¹ *
        Real.exp (-((4 * t)⁻¹ - a) * x ^ 2) := by
  rw [gaussianAccelerationKernel, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Exact evaluation before simplifying the normalization; valid for the totalized integral. -/
theorem gaussianAcceleration_quadratic_raw (t a : ℝ) :
    gaussianAcceleration (fun x => Real.exp (a * x ^ 2)) t =
      (Real.sqrt (Real.pi * t))⁻¹ *
        (Real.sqrt (Real.pi / ((4 * t)⁻¹ - a)) / 2) := by
  unfold gaussianAcceleration
  simp_rw [gaussianAccelerationKernel_mul_quadratic]
  rw [integral_const_mul, integral_gaussian_Ioi]

/-- The positive-time acceleration integral exists exactly below the quadratic growth threshold. -/
theorem integrable_gaussianAcceleration_quadratic_iff (s a : ℝ) :
    IntegrableOn (fun x => gaussianAccelerationKernel (Real.exp s) x *
      Real.exp (a * x ^ 2)) (Ioi 0) ↔ a < (4 * Real.exp s)⁻¹ := by
  simp_rw [gaussianAccelerationKernel_mul_quadratic]
  rw [IntegrableOn, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (by positivity)),
    ← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff]
  exact sub_pos

/-- Quadratic exponential growth becomes an inverse-square-root singularity.
The preceding integrability equivalence identifies the genuine convergence region. -/
theorem gaussianAcceleration_quadratic (s a : ℝ) :
    gaussianAcceleration (fun x => Real.exp (a * x ^ 2)) (Real.exp s) =
      (Real.sqrt (1 - 4 * Real.exp s * a))⁻¹ := by
  rw [gaussianAcceleration_quadratic_raw]
  have ht : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have hq : (4 * Real.exp s)⁻¹ - a =
      (1 - 4 * Real.exp s * a) / (4 * Real.exp s) := by
    field_simp [ht]
  rw [hq, div_div_eq_mul_div]
  have he : Real.pi * (4 * Real.exp s) / (1 - 4 * Real.exp s * a) =
      (Real.pi * Real.exp s) * (4 / (1 - 4 * Real.exp s * a)) := by ring
  rw [he, Real.sqrt_mul (show 0 ≤ Real.pi * Real.exp s by positivity)
    (4 / (1 - 4 * Real.exp s * a)), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
  have hs : Real.sqrt (Real.pi * Real.exp s) ≠ 0 := by positivity
  field_simp [hs]

/-- Every positive-time kernel has total mass one on the positive ray. -/
theorem integral_gaussianAccelerationKernel (s : ℝ) :
    (∫ x in Ioi (0 : ℝ), gaussianAccelerationKernel (Real.exp s) x) = 1 := by
  simpa only [gaussianAcceleration, zero_mul, mul_zero, Real.exp_zero, mul_one, sub_zero,
    Real.sqrt_one, inv_one] using gaussianAcceleration_quadratic s 0

/-- Gaussian damping gives an everywhere-convergent inverse-square-root family. -/
theorem gaussianAcceleration_gaussian (s r : ℝ) :
    gaussianAcceleration (fun x => RiemannGaussian.translatedGaussian (r ^ 2) 0 x)
      (Real.exp s) = (Real.sqrt (1 + 4 * Real.exp s * r ^ 2))⁻¹ := by
  simpa only [RiemannGaussian.translatedGaussian, sub_zero, mul_neg, sub_neg_eq_add]
    using gaussianAcceleration_quadratic s (-(r ^ 2))

/-- Damped Gaussians satisfy the required integrability without an analytic premise. -/
theorem integrable_gaussianAcceleration_gaussian (s r : ℝ) :
    IntegrableOn (fun x => gaussianAccelerationKernel (Real.exp s) x *
      RiemannGaussian.translatedGaussian (r ^ 2) 0 x) (Ioi 0) := by
  have h := (integrable_gaussianAcceleration_quadratic_iff s (-(r ^ 2))).mpr
    (lt_of_le_of_lt (neg_nonpos.mpr (sq_nonneg r)) (by positivity))
  simpa only [RiemannGaussian.translatedGaussian, sub_zero] using h

end

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.gaussianAccelerationKernel_eq_translatedGaussian
#print axioms GaloisForLFunctions.HTGeometry.gaussianAccelerationKernel_nonneg
#print axioms GaloisForLFunctions.HTGeometry.gaussianAccelerationKernel_exp_pos
#print axioms GaloisForLFunctions.HTGeometry.gaussianAccelerationKernel_mul_quadratic
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_quadratic_raw
#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_quadratic_iff
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_quadratic
#print axioms GaloisForLFunctions.HTGeometry.integral_gaussianAccelerationKernel
#print axioms GaloisForLFunctions.HTGeometry.gaussianAcceleration_gaussian
#print axioms GaloisForLFunctions.HTGeometry.integrable_gaussianAcceleration_gaussian
