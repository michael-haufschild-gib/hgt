import GaloisForLFunctions.RHTower.ChenGuptaLiAffinePoisson

noncomputable section

namespace RHTower

/-- A certified nonzero real input for the local derivative formula of CGL's Mellin phase. -/
structure CGLMellinPhaseInput where
  value : ℝ
  nonzero : value ≠ 0

/-- CGL's positive-axis Mellin oscillation `x ↦ x^{it}` written through the real logarithm. -/
def cglMellinPhase (t x : ℝ) : ℂ :=
  Complex.exp ((t : ℂ) * (Real.log x : ℂ) * Complex.I)

/-- The Mellin phase has unit norm for every real input. -/
theorem norm_cglMellinPhase (t x : ℝ) : ‖cglMellinPhase t x‖ = 1 := by
  rw [cglMellinPhase, Complex.norm_exp]
  have him : (((t : ℂ) * (Real.log x : ℂ) * Complex.I).re) = 0 := by simp
  rw [him, Real.exp_zero]

/-- Exact derivative of CGL's Mellin phase at a certified nonzero input. -/
theorem hasDerivAt_cglMellinPhase (t : ℝ) (x : CGLMellinPhaseInput) :
    HasDerivAt (cglMellinPhase t)
      (cglMellinPhase t x.value *
        ((t : ℂ) * (x.value⁻¹ : ℂ) * Complex.I)) x.value := by
  unfold cglMellinPhase
  have hlog : HasDerivAt Real.log x.value⁻¹ x.value :=
    Real.hasDerivAt_log x.nonzero
  have hlogC : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) (↑(x.value⁻¹) : ℂ) x.value := by
    exact hlog.ofReal_comp
  have harg : HasDerivAt (fun y : ℝ =>
      (t : ℂ) * (Real.log y : ℂ) * Complex.I)
      ((t : ℂ) * (↑(x.value⁻¹) : ℂ) * Complex.I) x.value := by
    simpa only [mul_assoc] using (hlogC.const_mul (t : ℂ)).mul_const Complex.I
  simpa only [Complex.ofReal_inv, mul_assoc] using harg.cexp

end RHTower
