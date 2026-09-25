import GaloisForLFunctions.RHTower.CCMUnitRieszVolterraLaplace

open Set MeasureTheory Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

def expClockOnDampedSource (a : ℝ) (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp ((1 + a) * t) * φ t -
    a * Real.exp ((1 + a) * t) *
      ∫ h in Ioc (0 : ℝ) t,
        Real.exp (-((1 + a) * (t - h))) * φ h

private theorem integrableOn_exp_mul_linear_source
    {z : ℂ} (hz : 0 < z.re) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : Measurable φ) (hbnd : ∀ h : ℝ, 0 < h → |φ h| ≤ C * (1 + h)) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * (φ t : ℂ))
      (Ioi (0 : ℝ)) volume := by
  have hmajor := integrableOn_Ioi_linear_exp_majorant (C := C) hz
  apply Integrable.mono' hmajor
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.const_mul z).neg)).mul
        (Complex.measurable_ofReal.comp hφ) |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hφbound := hbnd t ht
    have hzbound : Real.exp (-(z.re * t)) ≤ Real.exp (-(z.re / 2 * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hCbound : C * (1 + t) ≤ |C| * (1 + t) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have hpow : 0 ≤ |C| * (1 + t) := by positivity
    calc
      ‖Complex.exp (-(z * (t : ℂ))) * (φ t : ℂ)‖ =
          Real.exp (-(z.re * t)) * |φ t| := by
            rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
            congr 1
            simp [Complex.mul_re]
      _ ≤ Real.exp (-(z.re * t)) * (|C| * (1 + t)) := by
            gcongr
            exact hφbound.trans hCbound
      _ ≤ Real.exp (-(z.re / 2 * t)) * (|C| * (1 + t)) :=
            mul_le_mul_of_nonneg_right hzbound hpow
      _ = |C| * ((1 + t) * Real.exp (-(z.re / 2 * t))) := by ring

/-- Exponential clocking translates the Abel parameter of a linearly bounded damped source. -/
theorem expClockOnDampedSource_abel_shift
    {a : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : Measurable φ) (hbnd : ∀ h : ℝ, 0 < h → |φ h| ≤ C * (1 + h))
    {u : ℂ} (hu : 1 + a < u.re) :
    u * ∫ t in Ioi (0 : ℝ),
      Complex.exp (-(u * (t : ℂ))) * (expClockOnDampedSource a φ t : ℂ) =
      (u - (a : ℂ)) * ∫ t in Ioi (0 : ℝ),
        Complex.exp (-((u - (1 + a : ℝ)) * (t : ℂ))) * (φ t : ℂ) := by
  let z : ℂ := u - (1 + a : ℝ)
  have hz : 0 < z.re := by
    dsimp [z]
    linarith
  have hkernel : 0 ≤ 1 + a := by linarith
  have hfirst := integrableOn_exp_mul_linear_source hz hφ hbnd
  have hsecond := integrableOn_Ioi_cexp_mul_expVolterra hkernel hz hφ hbnd
  have hvol := integral_Ioi_expVolterra_laplace hkernel hz hφ hbnd
  have hpoint (t : ℝ) :
      Complex.exp (-(u * (t : ℂ))) * (expClockOnDampedSource a φ t : ℂ) =
        Complex.exp (-(z * (t : ℂ))) * (φ t : ℂ) -
          (a : ℂ) * (Complex.exp (-(z * (t : ℂ))) *
            ((∫ h in Ioc (0 : ℝ) t,
                Real.exp (-((1 + a) * (t - h))) * φ h : ℝ) : ℂ)) := by
    have hexp : Complex.exp (-(u * (t : ℂ))) *
        Complex.exp ((1 + (a : ℂ)) * (t : ℂ)) =
        Complex.exp (-(z * (t : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      dsimp [z]
      push_cast
      ring
    unfold expClockOnDampedSource
    push_cast
    calc
      _ = (Complex.exp (-(u * (t : ℂ))) *
            Complex.exp ((1 + (a : ℂ)) * (t : ℂ))) * (φ t : ℂ) -
          (a : ℂ) * (Complex.exp (-(u * (t : ℂ))) *
            Complex.exp ((1 + (a : ℂ)) * (t : ℂ))) *
            ((∫ h in Ioc (0 : ℝ) t,
                Real.exp (-((1 + a) * (t - h))) * φ h : ℝ) : ℂ) := by ring
      _ = _ := by rw [hexp]; ring
  have heq : (∫ t in Ioi (0 : ℝ),
      Complex.exp (-(u * (t : ℂ))) * (expClockOnDampedSource a φ t : ℂ)) =
      (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * (φ t : ℂ)) -
        (a : ℂ) * ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
          ((∫ h in Ioc (0 : ℝ) t,
              Real.exp (-((1 + a) * (t - h))) * φ h : ℝ) : ℂ) := by
    simp_rw [hpoint]
    rw [MeasureTheory.integral_sub hfirst (hsecond.const_mul a),
      MeasureTheory.integral_const_mul]
  rw [heq, hvol]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp only [zero_re] at hu
    linarith
  let L : ℂ := ∫ t in Ioi (0 : ℝ),
    Complex.exp (-(z * (t : ℂ))) * (φ t : ℂ)
  change u * (L - (a : ℂ) * ((z + (1 + a : ℝ))⁻¹ * L)) =
    (u - (a : ℂ)) * L
  have hzsum : z + (1 + a : ℝ) = u := by
    dsimp [z]
    push_cast
    ring
  rw [hzsum]
  field_simp [hu0]

end

end GaloisForLFunctions.RHTower
