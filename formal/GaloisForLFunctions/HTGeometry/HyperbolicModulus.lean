import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The modulus of a hyperbolic sine on a vertical line

Along the line `Re = a` the hyperbolic sine has squared modulus `sinh²a cos²θ + cosh²a sin²θ`: the
real and imaginary parts separate into the two hyperbolic functions against the two circular ones.

At the quarter-period frequencies, where the cosine vanishes, the squared modulus is exactly
`cosh²a` — independent of the frequency.  That constancy is what makes a free clock's spectral
weights flat: the factor `1 + x²` in the weight is cancelled by the `1 + x²` hidden in the
denominator `|1 - i x|²`, leaving no dependence on the mode.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- **The squared modulus of `sinh` on a vertical line.**  The real and imaginary parts separate
into hyperbolic times circular factors. -/
theorem normSq_sinh_sub_mul_I (a θ : ℝ) :
    Complex.normSq (Complex.sinh ((a : ℂ) - (θ : ℂ) * Complex.I))
      = Real.sinh a ^ 2 * Real.cos θ ^ 2 + Real.cosh a ^ 2 * Real.sin θ ^ 2 := by
  rw [Complex.sinh_sub, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh,
    ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **At a quarter-period frequency the modulus is constant.**  Where the cosine vanishes the
squared modulus is `cosh²a`, with no dependence on the frequency. -/
theorem normSq_sinh_sub_mul_I_of_cos_eq_zero {a θ : ℝ} (h : Real.cos θ = 0) :
    Complex.normSq (Complex.sinh ((a : ℂ) - (θ : ℂ) * Complex.I)) = Real.cosh a ^ 2 := by
  rw [normSq_sinh_sub_mul_I, h]
  have hs : Real.sin θ ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq θ
    rw [h] at this
    linarith
  rw [hs]
  ring

/-- The cosine vanishes at every half-odd multiple of `π`, which is where the quarter-period
frequencies `x_k = (k + 1/2)π/a` of aperture `a` send `x a`. -/
theorem cos_quarterPeriod_eq_zero (k : ℤ) :
    Real.cos ((k + 1 / 2) * Real.pi) = 0 := by
  have : ((k : ℝ) + 1 / 2) * Real.pi = (k : ℝ) * Real.pi + Real.pi / 2 := by ring
  rw [this, Real.cos_add_pi_div_two]
  simp [Real.sin_int_mul_pi]

/-- **The free-clock cancellation.**  At a quarter-period frequency the product of `1 + x²` with the
squared modulus of `sinh(a - i x a)/(1 - i x)` is `cosh²a`, independent of `x`: the `1 + x²` of the
weight is exactly cancelled by `|1 - i x|²`. -/
theorem quarterPeriod_weight_const {a x : ℝ} (h : Real.cos (x * a) = 0) :
    (1 + x ^ 2) *
        (Complex.normSq (Complex.sinh ((a : ℂ) - ((x * a : ℝ) : ℂ) * Complex.I)) /
          Complex.normSq (1 - (x : ℂ) * Complex.I))
      = Real.cosh a ^ 2 := by
  have hden : Complex.normSq (1 - (x : ℂ) * Complex.I) = 1 + x ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im]
    ring
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  rw [hden, normSq_sinh_sub_mul_I_of_cos_eq_zero h]
  field_simp

/-! ## The free-clock normalizations

The two normalizing integrals of the free model are elementary: the squared norm of the deficiency
vector is a hyperbolic sine, and that of an eigenvector is the aperture length.  Combining them with
the constant modulus above collapses the weight to `coth a / a` by the double-angle identity. -/

/-- The deficiency normalization of the free model. -/
theorem integral_exp_two_mul (a : ℝ) :
    ∫ s in (-a)..a, Real.exp (2 * s) = Real.sinh (2 * a) := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (two_ne_zero), integral_exp,
    Real.sinh_eq]
  rw [show (2 : ℝ) * -a = -(2 * a) by ring]
  rw [smul_eq_mul]
  ring

/-- The eigenvector normalization of the free model: a unimodular eigenfunction has squared norm the
aperture length. -/
theorem integral_one_symm (a : ℝ) : ∫ _s in (-a)..a, (1 : ℝ) = 2 * a := by
  simp
  ring

/-- **The free-clock weight.**  The constant modulus over the two normalizations is `coth a / a`, by
the double-angle identity for the hyperbolic sine. -/
theorem freeClockWeight_eq_coth {a : ℝ} (ha : a ≠ 0) (hs : Real.sinh a ≠ 0) :
    4 * Real.cosh a ^ 2 / (2 * a * Real.sinh (2 * a))
      = Real.cosh a / (a * Real.sinh a) := by
  rw [Real.sinh_two_mul]
  have hc : Real.cosh a ≠ 0 := ne_of_gt (Real.cosh_pos a)
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
