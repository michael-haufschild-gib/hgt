import GaloisForLFunctions.RHTower.CCMComplexMellinColligation

/-!
# A prime delay is not a passive impedance

The complex CCM source resolves each prime-power channel into positive Gram features.  A tempting
shortcut is to treat the corresponding delay mode `exp(i * lambda * z)` itself as a Herglotz or
positive-real impedance on the upper half-plane.  This file closes that shortcut exactly.

For every positive frequency `lambda`, two points on the same horizontal line `Im z = 1` give
imaginary parts `+exp(-lambda)` and `-exp(-lambda)`.  Thus no nonzero prime delay maps the upper
half-plane into its closure.

The positive conclusion is structural: a passive prime construction must occur after nonlinear
coupling--for example a contractive scattering colligation followed by a Cayley transform, or an
internal Schur complement.  It cannot be a positive sum of raw delay modes interpreted one by one
as impedances.
-/

open Complex Real

namespace GaloisForLFunctions.RHTower

/-- The analytic delay mode with positive real frequency `lambda`. -/
noncomputable def primeDelayMode (lambda : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (I * (lambda : ℂ) * z)

/-- Two test points are obtained by taking `sign = 1` and `sign = -1`. -/
noncomputable def primeDelayUpperPoint (lambda sign : ℝ) : ℂ :=
  Complex.ofReal (sign * Real.pi / (2 * lambda)) + I

@[simp] theorem primeDelayUpperPoint_re (lambda sign : ℝ) :
    (primeDelayUpperPoint lambda sign).re = sign * Real.pi / (2 * lambda) := by
  simp only [primeDelayUpperPoint, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]

/-- Both test points lie on the horizontal line `Im z = 1` in the upper half-plane. -/
@[simp] theorem primeDelayUpperPoint_im (lambda sign : ℝ) :
    (primeDelayUpperPoint lambda sign).im = 1 := by
  simp only [primeDelayUpperPoint, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]

/-- At phase `pi/2`, a positive-frequency delay has positive imaginary part. -/
theorem primeDelayMode_upperPoint_one {lambda : ℝ} (hlambda : 0 < lambda) :
    (primeDelayMode lambda (primeDelayUpperPoint lambda 1)).im = Real.exp (-lambda) := by
  have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
  rw [primeDelayMode, Complex.exp_im]
  have hre : (I * (lambda : ℂ) * primeDelayUpperPoint lambda 1).re = -lambda := by
    simp [Complex.mul_re]
  have him : (I * (lambda : ℂ) * primeDelayUpperPoint lambda 1).im = Real.pi / 2 := by
    simp [Complex.mul_re, Complex.mul_im]
    field_simp
  rw [hre, him, Real.sin_pi_div_two, mul_one]

/-- At phase `-pi/2`, the same delay has negative imaginary part on the same horizontal line. -/
theorem primeDelayMode_upperPoint_neg_one {lambda : ℝ} (hlambda : 0 < lambda) :
    (primeDelayMode lambda (primeDelayUpperPoint lambda (-1))).im = -Real.exp (-lambda) := by
  have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
  rw [primeDelayMode, Complex.exp_im]
  have hre : (I * (lambda : ℂ) * primeDelayUpperPoint lambda (-1)).re = -lambda := by
    simp [Complex.mul_re]
  have him : (I * (lambda : ℂ) * primeDelayUpperPoint lambda (-1)).im = -Real.pi / 2 := by
    simp [Complex.mul_re, Complex.mul_im]
    field_simp
  rw [hre, him]
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring, Real.sin_neg,
    Real.sin_pi_div_two]
  ring

/-- **Raw-delay Herglotz no-go.**  A positive-frequency prime delay does not map the upper
half-plane into the closed upper half-plane. -/
theorem primeDelayMode_not_upperHalfPlaneValued {lambda : ℝ} (hlambda : 0 < lambda) :
    ¬ (∀ z : ℂ, 0 < z.im → 0 ≤ (primeDelayMode lambda z).im) := by
  intro h
  have hz := h (primeDelayUpperPoint lambda (-1)) (by simp)
  rw [primeDelayMode_upperPoint_neg_one hlambda] at hz
  have hexp : 0 < Real.exp (-lambda) := Real.exp_pos _
  linarith

end GaloisForLFunctions.RHTower
