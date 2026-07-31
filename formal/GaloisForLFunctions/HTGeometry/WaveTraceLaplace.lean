import GaloisForLFunctions.HTGeometry.WaveTraceSpectrum

/-!
# Laplace transform of a wave trace

A single complex frequency contributes the elementary Laplace kernel
`∫₀^∞ sin (gamma * t) e^{-s t} dt = gamma / (s ^ 2 + gamma ^ 2)`,
valid on the half-plane to the right of the frequency's horizontal width.

Summed against a polynomial weight this produces the meromorphic active-pole transform of
the wave trace, whose poles sit exactly at `± i * gamma`.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The elementary sine kernel -/

variable {gamma s : ℂ}

private theorem laplace_exp_re_neg_left (h : |gamma.im| < s.re) :
    (-(gamma * Complex.I) - s).re < 0 := by
  have h1 : (-(gamma * Complex.I) - s).re = gamma.im - s.re := by
    simp [Complex.sub_re, Complex.neg_re, Complex.mul_re]
  rw [h1]
  have := le_abs_self gamma.im
  linarith

private theorem laplace_exp_re_neg_right (h : |gamma.im| < s.re) :
    (gamma * Complex.I - s).re < 0 := by
  have h1 : (gamma * Complex.I - s).re = -gamma.im - s.re := by
    simp [Complex.sub_re, Complex.mul_re]
  rw [h1]
  have := neg_le_abs gamma.im
  linarith

theorem sin_mul_exp_eq (gamma s : ℂ) (t : ℝ) :
    Complex.sin (gamma * t) * Complex.exp (-s * t) =
      (Complex.exp ((-(gamma * Complex.I) - s) * t) -
        Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2 := by
  rw [Complex.sin]
  rw [show (-(gamma * (t : ℂ)) * Complex.I) = (-(gamma * Complex.I)) * (t : ℂ) by ring,
    show (gamma * (t : ℂ) * Complex.I) = (gamma * Complex.I) * (t : ℂ) by ring]
  rw [show ((-(gamma * Complex.I) - s) * (t : ℂ)) =
      (-(gamma * Complex.I)) * (t : ℂ) + (-s * (t : ℂ)) by ring,
    show ((gamma * Complex.I - s) * (t : ℂ)) =
      (gamma * Complex.I) * (t : ℂ) + (-s * (t : ℂ)) by ring]
  rw [Complex.exp_add, Complex.exp_add]
  ring

theorem integrableOn_sin_mul_exp (h : |gamma.im| < s.re) :
    IntegrableOn (fun t : ℝ => Complex.sin (gamma * t) * Complex.exp (-s * t))
      (Ioi (0 : ℝ)) := by
  have h1 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_left h) 0
  have h2 := integrableOn_exp_mul_complex_Ioi (laplace_exp_re_neg_right h) 0
  have hint : IntegrableOn
      (fun t : ℝ =>
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2)
      (Ioi (0 : ℝ)) := ((h1.sub h2).mul_const Complex.I).div_const 2
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (sin_mul_exp_eq gamma s t).symm

theorem sq_add_sq_ne_zero (h : |gamma.im| < s.re) : s ^ 2 + gamma ^ 2 ≠ 0 := by
  have hleft : s + gamma * Complex.I ≠ 0 := by
    intro hz
    have : (s + gamma * Complex.I).re = 0 := by rw [hz]; simp
    rw [Complex.add_re, Complex.mul_re] at this
    simp at this
    have h2 := le_abs_self gamma.im
    linarith
  have hright : s - gamma * Complex.I ≠ 0 := by
    intro hz
    have : (s - gamma * Complex.I).re = 0 := by rw [hz]; simp
    rw [Complex.sub_re, Complex.mul_re] at this
    simp at this
    have h2 := neg_le_abs gamma.im
    linarith
  have hfac : s ^ 2 + gamma ^ 2 = (s + gamma * Complex.I) * (s - gamma * Complex.I) := by
    linear_combination (gamma ^ 2) * Complex.I_sq
  rw [hfac]
  exact mul_ne_zero hleft hright

/-- **Elementary sine Laplace kernel.** To the right of the horizontal width of a frequency,
its damped sine integrates to the resolvent kernel. -/
theorem integral_sin_mul_exp (h : |gamma.im| < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      gamma / (s ^ 2 + gamma ^ 2) := by
  have hleft := laplace_exp_re_neg_left h
  have hright := laplace_exp_re_neg_right h
  have h1 := integrableOn_exp_mul_complex_Ioi hleft 0
  have h2 := integrableOn_exp_mul_complex_Ioi hright 0
  have hcongr : (∫ t in Ioi (0 : ℝ), Complex.sin (gamma * t) * Complex.exp (-s * t)) =
      ∫ t in Ioi (0 : ℝ),
        (Complex.exp ((-(gamma * Complex.I) - s) * t) -
          Complex.exp ((gamma * Complex.I - s) * t)) * Complex.I / 2 := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    exact sin_mul_exp_eq gamma s t
  rw [hcongr]
  rw [integral_div, integral_mul_const, integral_sub h1 h2,
    integral_exp_mul_complex_Ioi hleft, integral_exp_mul_complex_Ioi hright]
  have hane : (-(gamma * Complex.I) - s) ≠ 0 := fun hz => by
    rw [hz] at hleft; simp at hleft
  have hbne : (gamma * Complex.I - s) ≠ 0 := fun hz => by
    rw [hz] at hright; simp at hright
  have hsq := sq_add_sq_ne_zero h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp
  ring_nf
  linear_combination (-(2 * gamma * s ^ 2)) * Complex.I_sq

end

end GaloisForLFunctions.HTGeometry
