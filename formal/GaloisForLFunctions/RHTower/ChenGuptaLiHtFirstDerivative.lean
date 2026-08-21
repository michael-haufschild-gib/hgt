/-
# Chen--Gupta--Li `h_t`: first derivative

This is the first parameter-sensitive analytic layer for CGL Lemma 4.3.  It
identifies the literal derivative of `h_t(x)=w(x)^2 x^{it}` globally, including
the nonpositive region where compact support kills the logarithmic phase.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHt

noncomputable section

namespace RHTower

/-- The support of a CGL bump is contained in its certified source interval. -/
theorem cglSmoothBump_support_subset (w : CGLSmoothBump) :
    Function.support w.value ⊆ Set.Icc (1 : ℝ) 2 := by
  intro x hx
  by_contra hnot
  exact hx (w.outside_support x hnot)

/-- The topological support of a CGL bump remains in the source interval. -/
theorem cglSmoothBump_tsupport_subset (w : CGLSmoothBump) :
    tsupport w.value ⊆ Set.Icc (1 : ℝ) 2 :=
  closure_minimal (cglSmoothBump_support_subset w) isClosed_Icc

/-- The bump derivative vanishes on the entire nonpositive half-line. -/
theorem deriv_cglSmoothBump_eq_zero_of_nonpos (w : CGLSmoothBump) {x : ℝ}
    (hx : x ≤ 0) : deriv w.value x = 0 := by
  apply deriv_of_notMem_tsupport
  intro hmem
  have hbounds := cglSmoothBump_tsupport_subset w hmem
  linarith [hbounds.1]

/-- The literal CGL kernel has the same support interval as the cutoff. -/
theorem cglSmoothBumpHtValue_support_subset (w : CGLSmoothBump) (t : ℝ) :
    Function.support (cglSmoothBumpHtValue w t) ⊆ Set.Icc (1 : ℝ) 2 := by
  intro x hx
  by_contra hnot
  have hw : w.value x = 0 := w.outside_support x hnot
  exact hx (by simp [cglSmoothBumpHtValue, hw])

/-- The topological support of the literal CGL kernel is contained in `[1,2]`. -/
theorem cglSmoothBumpHtValue_tsupport_subset (w : CGLSmoothBump) (t : ℝ) :
    tsupport (cglSmoothBumpHtValue w t) ⊆ Set.Icc (1 : ℝ) 2 :=
  closure_minimal (cglSmoothBumpHtValue_support_subset w t) isClosed_Icc

/-- The literal CGL kernel derivative vanishes on the nonpositive half-line. -/
theorem deriv_cglSmoothBumpHtValue_eq_zero_of_nonpos (w : CGLSmoothBump) (t : ℝ) {x : ℝ}
    (hx : x ≤ 0) : deriv (cglSmoothBumpHtValue w t) x = 0 := by
  apply deriv_of_notMem_tsupport
  intro hmem
  have hbounds := cglSmoothBumpHtValue_tsupport_subset w t hmem
  linarith [hbounds.1]

/-- Pointwise first derivative of CGL's literal kernel. -/
noncomputable def cglSmoothBumpHtDerivativeValue (w : CGLSmoothBump) (t x : ℝ) : ℂ :=
  ((deriv w.value x) * w.value x + w.value x * deriv w.value x) * cglMellinPhase t x +
    w.value x * w.value x *
      (cglMellinPhase t x * ((t : ℂ) * (x⁻¹ : ℂ) * Complex.I))

/-- Positive-axis derivative formula for the literal CGL kernel. -/
theorem hasDerivAt_cglSmoothBumpHtValue_of_pos (w : CGLSmoothBump) (t : ℝ)
    (x : CGLMellinPhaseInput) :
    HasDerivAt (cglSmoothBumpHtValue w t)
      (((deriv w.value x.value) * w.value x.value + w.value x.value * deriv w.value x.value) *
        cglMellinPhase t x.value +
        w.value x.value * w.value x.value *
          (cglMellinPhase t x.value *
            ((t : ℂ) * (x.value⁻¹ : ℂ) * Complex.I))) x.value := by
  have hdif : Differentiable ℝ w.value :=
    w.smooth.differentiable (by simp)
  have hw : HasDerivAt w.value (deriv w.value x.value) x.value :=
    (hdif x.value).hasDerivAt
  have hsq : HasDerivAt (fun y : ℝ => w.value y * w.value y)
      (deriv w.value x.value * w.value x.value + w.value x.value * deriv w.value x.value)
      x.value :=
    hw.mul hw
  apply HasDerivAt.of_isLittleO
  exact (by
    simpa [cglSmoothBumpHtValue, smul_eq_mul] using
      (hsq.mul (hasDerivAt_cglMellinPhase t x)).isLittleO)

/-- Global first derivative formula for CGL's literal `h_t`. -/
theorem deriv_cglSmoothBumpHtValue (w : CGLSmoothBump) (t x : ℝ) :
    deriv (cglSmoothBumpHtValue w t) x = cglSmoothBumpHtDerivativeValue w t x := by
  by_cases hx : 0 < x
  · exact (hasDerivAt_cglSmoothBumpHtValue_of_pos w t ⟨x, hx.ne'⟩).deriv
  · have hxnonpos : x ≤ 0 := le_of_not_gt hx
    unfold cglSmoothBumpHtDerivativeValue
    rw [deriv_cglSmoothBumpHtValue_eq_zero_of_nonpos w t hxnonpos,
      deriv_cglSmoothBump_eq_zero_of_nonpos w hxnonpos,
      w.outside_support x (by
        intro hmem
        linarith [hmem.1])]
    simp

/-- Pointwise parameter-linear norm control for the literal first derivative of `h_t`. -/
theorem norm_cglSmoothBumpHtDerivativeValue_le (w : CGLSmoothBump) (t x : ℝ) :
    ‖cglSmoothBumpHtDerivativeValue w t x‖ ≤
      2 * ‖deriv w.value x‖ * ‖w.value x‖ +
        |t| * ‖w.value x‖ ^ 2 * |x⁻¹| := by
  unfold cglSmoothBumpHtDerivativeValue
  calc
    ‖(deriv w.value x * w.value x + w.value x * deriv w.value x) *
        cglMellinPhase t x + w.value x * w.value x * (cglMellinPhase t x *
          ((t : ℂ) * (x⁻¹ : ℂ) * Complex.I))‖ ≤
        ‖(deriv w.value x * w.value x + w.value x * deriv w.value x) *
          cglMellinPhase t x‖ +
        ‖w.value x * w.value x * (cglMellinPhase t x *
          ((t : ℂ) * (x⁻¹ : ℂ) * Complex.I))‖ := norm_add_le _ _
    _ ≤
        (‖deriv w.value x * w.value x‖ + ‖w.value x * deriv w.value x‖) *
          ‖cglMellinPhase t x‖ +
        ‖w.value x * w.value x‖ * ‖cglMellinPhase t x‖ *
          ‖(t : ℂ) * (x⁻¹ : ℂ) * Complex.I‖ := by
      simp only [norm_mul]
      rw [norm_cglMellinPhase]
      have hfirst : ‖deriv w.value x * w.value x + w.value x * deriv w.value x‖ ≤
          ‖deriv w.value x‖ * ‖w.value x‖ + ‖w.value x‖ * ‖deriv w.value x‖ := by
        calc
          ‖deriv w.value x * w.value x + w.value x * deriv w.value x‖ ≤
              ‖deriv w.value x * w.value x‖ + ‖w.value x * deriv w.value x‖ := norm_add_le _ _
          _ = ‖deriv w.value x‖ * ‖w.value x‖ + ‖w.value x‖ * ‖deriv w.value x‖ := by
            rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hfirst zero_le_one)
        (le_of_eq (by ring))
    _ = 2 * ‖deriv w.value x‖ * ‖w.value x‖ +
        |t| * ‖w.value x‖ ^ 2 * |x⁻¹| := by
      simp only [norm_mul, norm_cglMellinPhase, Complex.norm_real, Complex.norm_I,
        norm_inv, Real.norm_eq_abs, abs_inv]
      ring

/-- Pointwise parameter-linear norm control for `deriv h_t`. -/
theorem norm_deriv_cglSmoothBumpHtValue_le (w : CGLSmoothBump) (t x : ℝ) :
    ‖deriv (cglSmoothBumpHtValue w t) x‖ ≤
      2 * ‖deriv w.value x‖ * ‖w.value x‖ +
        |t| * ‖w.value x‖ ^ 2 * |x⁻¹| := by
  rw [deriv_cglSmoothBumpHtValue]
  exact norm_cglSmoothBumpHtDerivativeValue_le w t x

end RHTower
