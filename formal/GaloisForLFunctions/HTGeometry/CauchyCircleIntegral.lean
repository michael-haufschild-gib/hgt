import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The Cauchy kernel of the circle, integrated along the period

The factor `1 - r e^{i d y}` has real part `1 - r cos(d y) > 0` for `0 ≤ r < 1`, so it never leaves
the right half plane and the principal logarithm is a genuine antiderivative along the whole real
line.  Consequently `y + (i/d) log(1 - r e^{idy})` is an antiderivative of the Cauchy kernel
`(1 - r e^{idy})^{-1}`, and the integral of the kernel over any interval is computed exactly.
-/

open Complex

noncomputable section

namespace HTGeometry

/-- `1 - r e^{i d y}`. -/
def circleFactor (r d y : ℝ) : ℂ := 1 - (r : ℂ) * Complex.exp ((d : ℂ) * (y : ℂ) * I)

theorem exp_circleArg_re (d y : ℝ) :
    (Complex.exp ((d : ℂ) * (y : ℂ) * I)).re = Real.cos (d * y) := by
  rw [show (d : ℂ) * (y : ℂ) * I = ((d * y : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_re _

theorem exp_circleArg_im (d y : ℝ) :
    (Complex.exp ((d : ℂ) * (y : ℂ) * I)).im = Real.sin (d * y) := by
  rw [show (d : ℂ) * (y : ℂ) * I = ((d * y : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.exp_ofReal_mul_I_im _

theorem circleFactor_re (r d y : ℝ) : (circleFactor r d y).re = 1 - r * Real.cos (d * y) := by
  simp [circleFactor, Complex.sub_re, Complex.mul_re, exp_circleArg_re, exp_circleArg_im]

theorem circleFactor_re_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    0 < (circleFactor r d y).re := by
  rw [circleFactor_re]
  nlinarith [Real.neg_one_le_cos (d * y), Real.cos_le_one (d * y)]

theorem circleFactor_mem_slitPlane {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    circleFactor r d y ∈ Complex.slitPlane :=
  Or.inl (circleFactor_re_pos hr0 hr1 d y)

theorem circleFactor_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    circleFactor r d y ≠ 0 := by
  intro h
  have := circleFactor_re_pos hr0 hr1 d y
  rw [h] at this
  simp at this

theorem circleFactor_im (r d y : ℝ) : (circleFactor r d y).im = -(r * Real.sin (d * y)) := by
  simp [circleFactor, Complex.sub_im, Complex.mul_im, exp_circleArg_re, exp_circleArg_im]

/-- The squared modulus of the circle factor. -/
theorem normSq_circleFactor (r d y : ℝ) :
    Complex.normSq (circleFactor r d y) = 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
  rw [Complex.normSq_apply, circleFactor_re, circleFactor_im]
  nlinarith [Real.sin_sq_add_cos_sq (d * y)]

theorem normSq_circleFactor_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    0 < Complex.normSq (circleFactor r d y) :=
  Complex.normSq_pos.mpr (circleFactor_ne_zero hr0 hr1 d y)

/-- The antiderivative of the Cauchy kernel along the circle. -/
def circleAntideriv (r d y : ℝ) : ℂ :=
  (y : ℂ) + (I / (d : ℂ)) * Complex.log (circleFactor r d y)

theorem hasDerivAt_circleFactor (r d y : ℝ) :
    HasDerivAt (fun t : ℝ => circleFactor r d t)
      (-((r : ℂ) * I * (d : ℂ) * Complex.exp ((d : ℂ) * (y : ℂ) * I))) y := by
  have hbase : HasDerivAt (fun t : ℝ => (d : ℂ) * (t : ℂ) * I) ((d : ℂ) * I) y := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
    simpa using ((h.const_mul (d : ℂ)).mul_const I)
  have hexp := (hbase.cexp)
  have := (hexp.const_mul (r : ℂ)).const_sub 1
  simpa [circleFactor] using this.congr_deriv (by ring)

theorem hasDerivAt_circleAntideriv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {d : ℝ} (hd : d ≠ 0)
    (y : ℝ) :
    HasDerivAt (fun t : ℝ => circleAntideriv r d t) (circleFactor r d y)⁻¹ y := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hne := circleFactor_ne_zero hr0 hr1 d y
  have hlog : HasDerivAt (fun t : ℝ => Complex.log (circleFactor r d t))
      ((-((r : ℂ) * I * (d : ℂ) * Complex.exp ((d : ℂ) * (y : ℂ) * I))) / circleFactor r d y) y := by
    have h2 := (Complex.hasDerivAt_log
      (circleFactor_mem_slitPlane hr0 hr1 d y)).scomp y (hasDerivAt_circleFactor r d y)
    simp only [Function.comp_def, smul_eq_mul] at h2
    exact h2.congr_deriv (by rw [div_eq_mul_inv])
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := Complex.ofRealCLM.hasDerivAt
  have hsum := hid.add ((hlog.const_mul (I / (d : ℂ))))
  refine hsum.congr_deriv ?_
  have hexpand : circleFactor r d y
      = 1 - (r : ℂ) * Complex.exp ((d : ℂ) * (y : ℂ) * I) := rfl
  field_simp [circleAntideriv]
  rw [hexpand]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem continuous_circleFactor (r d : ℝ) : Continuous (circleFactor r d) := by
  unfold circleFactor
  fun_prop

theorem continuous_circleKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℝ) :
    Continuous (fun y : ℝ => (circleFactor r d y)⁻¹) :=
  (continuous_circleFactor r d).inv₀ (fun y => circleFactor_ne_zero hr0 hr1 d y)

/-- **The exact integral of the Cauchy kernel along the circle.** -/
theorem integral_circleKernel {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {d : ℝ} (hd : d ≠ 0) (u v : ℝ) :
    (∫ y in u..v, (circleFactor r d y)⁻¹)
      = ((v : ℂ) - (u : ℂ))
        + (I / (d : ℂ)) *
            (Complex.log (circleFactor r d v) - Complex.log (circleFactor r d u)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_circleAntideriv hr0 hr1 hd y)
    ((continuous_circleKernel hr0 hr1 d).intervalIntegrable u v)]
  rw [circleAntideriv, circleAntideriv]
  ring

theorem circleKernel_re (r d y : ℝ) :
    ((circleFactor r d y)⁻¹).re
      = (1 - r * Real.cos (d * y)) / (1 - 2 * r * Real.cos (d * y) + r ^ 2) := by
  rw [Complex.inv_re, circleFactor_re, normSq_circleFactor]

theorem circleKernel_im (r d y : ℝ) :
    ((circleFactor r d y)⁻¹).im
      = r * Real.sin (d * y) / (1 - 2 * r * Real.cos (d * y) + r ^ 2) := by
  rw [Complex.inv_im, circleFactor_im, normSq_circleFactor]
  ring

/-- The Poisson factor `2 Re (1 - r e^{idy})^{-1} - 1 = (1-r²)/|1-re^{idy}|²`. -/
def poissonFactor (r d y : ℝ) : ℝ := 2 * ((circleFactor r d y)⁻¹).re - 1

theorem poissonFactor_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    poissonFactor r d y = (1 - r ^ 2) / (1 - 2 * r * Real.cos (d * y) + r ^ 2) := by
  have hpos : 0 < 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
    have := normSq_circleFactor_pos hr0 hr1 d y
    rwa [normSq_circleFactor] at this
  rw [poissonFactor, circleKernel_re]
  field_simp
  ring

theorem poissonFactor_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d y : ℝ) :
    0 ≤ poissonFactor r d y := by
  have hpos : 0 < 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
    have := normSq_circleFactor_pos hr0 hr1 d y
    rwa [normSq_circleFactor] at this
  rw [poissonFactor_eq hr0 hr1]
  have : (0 : ℝ) ≤ 1 - r ^ 2 := by nlinarith
  positivity

/-- Reflection across the half period flips the sign of the imaginary part of the kernel. -/
theorem circleKernel_im_reflect {d T : ℝ} (hT : d * T = 2 * Real.pi) (r y : ℝ) :
    ((circleFactor r d (T - y))⁻¹).im = -((circleFactor r d y)⁻¹).im := by
  have harg : d * (T - y) = 2 * Real.pi - d * y := by
    rw [mul_sub, hT]
  rw [circleKernel_im, circleKernel_im, harg]
  rw [Real.cos_sub, Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring

/-- Reflection across the half period preserves the Poisson factor. -/
theorem poissonFactor_reflect {d T : ℝ} (hT : d * T = 2 * Real.pi) (r y : ℝ) :
    poissonFactor r d (T - y) = poissonFactor r d y := by
  have harg : d * (T - y) = 2 * Real.pi - d * y := by
    rw [mul_sub, hT]
  rw [poissonFactor, poissonFactor, circleKernel_re, circleKernel_re, harg]
  rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring_nf

/-- Away from the singularity the imaginary part of the kernel is uniformly bounded. -/
theorem abs_circleKernel_im_le {r γ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {d y : ℝ}
    (hγ : Real.cos (d * y) ≤ γ) (hγ1 : γ < 1) (hγ0 : -1 < γ) :
    |((circleFactor r d y)⁻¹).im| ≤ 1 / (1 - γ ^ 2) := by
  have hden : 0 < 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
    have := normSq_circleFactor_pos hr0 hr1 d y
    rwa [normSq_circleFactor] at this
  have hγpos : 0 < 1 - γ ^ 2 := by nlinarith
  have hlow : 1 - γ ^ 2 ≤ 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
    nlinarith [sq_nonneg (r - γ), hr0, hγ]
  have hnum : |r * Real.sin (d * y)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hr0]
    have h1 : |Real.sin (d * y)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [abs_nonneg (Real.sin (d * y))]
  rw [circleKernel_im, abs_div, abs_of_pos hden]
  rw [div_le_div_iff₀ hden hγpos]
  nlinarith [hnum, hγpos, hden, abs_nonneg (r * Real.sin (d * y))]

/-- On the first half period the imaginary part of the kernel is nonnegative. -/
theorem circleKernel_im_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {d y : ℝ}
    (hsin : 0 ≤ Real.sin (d * y)) : 0 ≤ ((circleFactor r d y)⁻¹).im := by
  have hden : 0 < 1 - 2 * r * Real.cos (d * y) + r ^ 2 := by
    have := normSq_circleFactor_pos hr0 hr1 d y
    rwa [normSq_circleFactor] at this
  rw [circleKernel_im]
  positivity

end HTGeometry

end
