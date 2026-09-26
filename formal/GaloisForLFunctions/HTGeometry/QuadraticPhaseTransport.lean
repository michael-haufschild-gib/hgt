import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Transport of quadratic phase kernels

The vector field `L = y d/dx + x d/dy` preserves `x^2-y^2`. For
`K = exp(I*(a*(x^2-y^2)+b*x))`, its second derivative is
`L^2 K = (I*b*x-b^2*y^2)*K`. Pairing `b` and `-b` gives a bound
`2*b^2*(x^2+y^2)` for real parameters, including the product-rule correction.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The vector field `y d/dx + x d/dy` acting on a complex kernel. -/
noncomputable def quadraticPhaseTransport (K : ℂ → ℂ → ℂ) (x y : ℂ) : ℂ :=
  y * deriv (fun z => K z y) x + x * deriv (K x) y

/-- A quadratic phase invariant under hyperbolic transport, with a linear perturbation. -/
noncomputable def quadraticPhaseKernel (a b x y : ℂ) : ℂ :=
  exp (I * (a * (x ^ 2 - y ^ 2) + b * x))

theorem quadraticPhaseKernel_dx (a b x y : ℂ) :
    HasDerivAt (fun z => quadraticPhaseKernel a b z y)
      (I * (2 * a * x + b) * quadraticPhaseKernel a b x y) x := by
  have h := ((((((hasDerivAt_id x).pow 2).sub_const (y ^ 2)).const_mul a).add
    ((hasDerivAt_id x).const_mul b)).const_mul I).cexp
  convert h using 1 <;> first | rfl | (dsimp [quadraticPhaseKernel, id]; ring)

theorem quadraticPhaseKernel_dy (a b x y : ℂ) :
    HasDerivAt (quadraticPhaseKernel a b x)
      (-2 * I * a * y * quadraticPhaseKernel a b x y) y := by
  have h := ((((((hasDerivAt_id y).pow 2).const_sub (x ^ 2)).const_mul a).add_const
    (b * x)).const_mul I).cexp
  convert h using 1 <;> first | rfl | (dsimp [quadraticPhaseKernel, id]; ring)

theorem quadraticPhaseTransport_quadraticPhase (a b x y : ℂ) :
    quadraticPhaseTransport (quadraticPhaseKernel a b) x y =
      I * b * y * quadraticPhaseKernel a b x y := by
  rw [quadraticPhaseTransport, (quadraticPhaseKernel_dx a b x y).deriv,
    (quadraticPhaseKernel_dy a b x y).deriv]
  ring

/-- The second transport derivative includes the derivative of the first multiplier. -/
theorem quadraticPhaseTransport_twice_quadraticPhase (a b x y : ℂ) :
    quadraticPhaseTransport (quadraticPhaseTransport (quadraticPhaseKernel a b)) x y =
      (I * b * x - b ^ 2 * y ^ 2) * quadraticPhaseKernel a b x y := by
  have hfun : quadraticPhaseTransport (quadraticPhaseKernel a b) =
      fun u v => I * b * v * quadraticPhaseKernel a b u v := by
    funext u v
    exact quadraticPhaseTransport_quadraticPhase a b u v
  have hy := (((hasDerivAt_id y).const_mul (I * b)).mul
    (quadraticPhaseKernel_dy a b x y))
  change HasDerivAt (fun v => I * b * v * quadraticPhaseKernel a b x v) _ y at hy
  rw [hfun, quadraticPhaseTransport,
    ((quadraticPhaseKernel_dx a b x y).const_mul (I * b * y)).deriv, hy.deriv]
  ring_nf
  simp only [I_sq, id_eq]
  ring

theorem quadraticPhaseTransport_twice_paired (a b x y : ℂ) :
    quadraticPhaseTransport (quadraticPhaseTransport (quadraticPhaseKernel a b)) x y +
      quadraticPhaseTransport (quadraticPhaseTransport (quadraticPhaseKernel a (-b))) x y =
    -2 * exp (I * a * (x ^ 2 - y ^ 2)) *
      (b * x * sin (b * x) + b ^ 2 * y ^ 2 * cos (b * x)) := by
  rw [quadraticPhaseTransport_twice_quadraticPhase, quadraticPhaseTransport_twice_quadraticPhase]
  have hp : I * (a * (x ^ 2 - y ^ 2) + b * x) =
      I * a * (x ^ 2 - y ^ 2) + b * x * I := by ring
  have hn : I * (a * (x ^ 2 - y ^ 2) + -b * x) =
      I * a * (x ^ 2 - y ^ 2) + -(b * x) * I := by ring
  simp only [quadraticPhaseKernel, hp, hn, exp_add, Complex.sin, Complex.cos]
  ring_nf

/-- Opposite linear phases recover a quadratic bound in the phase coefficient. -/
theorem quadraticPhaseTransport_twice_paired_norm (a b x y : ℝ) :
    ‖quadraticPhaseTransport (quadraticPhaseTransport (quadraticPhaseKernel a b)) x y +
      quadraticPhaseTransport (quadraticPhaseTransport (quadraticPhaseKernel a (-b))) x y‖ ≤
    2 * b ^ 2 * (x ^ 2 + y ^ 2) := by
  have habs : |b * x * Real.sin (b * x) + b ^ 2 * y ^ 2 * Real.cos (b * x)| ≤
      b ^ 2 * (x ^ 2 + y ^ 2) := by
    calc
      _ ≤ |b * x * Real.sin (b * x)| + |b ^ 2 * y ^ 2 * Real.cos (b * x)| := abs_add_le _ _
      _ = |b * x| * |Real.sin (b * x)| + b ^ 2 * y ^ 2 * |Real.cos (b * x)| := by
        rw [abs_mul (b * x), abs_mul (b ^ 2 * y ^ 2),
          abs_of_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg y))]
      _ ≤ |b * x| * |b * x| + b ^ 2 * y ^ 2 * 1 := by
        exact add_le_add (mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity))
      _ = b ^ 2 * (x ^ 2 + y ^ 2) := by rw [← sq, sq_abs]; ring
  rw [quadraticPhaseTransport_twice_paired]
  have he : ‖exp (I * (a : ℂ) * ((x : ℂ) ^ 2 - (y : ℂ) ^ 2))‖ = 1 := by
    rw [norm_exp]
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  have hc : (b : ℂ) * x * sin ((b : ℂ) * x) + (b : ℂ) ^ 2 * (y : ℂ) ^ 2 * cos ((b : ℂ) * x) =
      ((b * x * Real.sin (b * x) + b ^ 2 * y ^ 2 * Real.cos (b * x) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_mul, norm_mul, he, hc, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [norm_neg, norm_ofNat, mul_one]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left habs (show (0 : ℝ) ≤ 2 by norm_num)

end GaloisForLFunctions.HTGeometry
