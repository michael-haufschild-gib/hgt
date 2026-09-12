import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-! # Actual beta transform ratios for the primitive theta-ray interior

Gamma recurrence gives the two shifted integral ratios. Every oscillatory
hyperbolic power is proved absolutely integrable before it is combined.
-/

open Complex Real MeasureTheory
namespace RHTower
noncomputable section

def thetaCuspPrimitiveRayBetaFourierDensity (a s : ℝ) : ℝ :=
  (2 : ℝ) ^ (a - 1) *
    Complex.normSq (Complex.Gamma (((a : ℂ) + (s : ℂ) * Complex.I) / 2)) /
      Real.Gamma a

theorem thetaCuspPrimitiveRayBetaFourierDensity_nonneg
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    0 ≤ thetaCuspPrimitiveRayBetaFourierDensity a s :=
  HTGeometry.integral_cosh_rpow_neg_mul_exp_nonneg ha s

theorem thetaCuspPrimitiveRayBetaFourierDensity_add_two
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    thetaCuspPrimitiveRayBetaFourierDensity (a + 2) s =
      (a ^ 2 + s ^ 2) / (a * (a + 1)) *
        thetaCuspPrimitiveRayBetaFourierDensity a s := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha1 : a + 1 ≠ 0 := by linarith
  have hG : Real.Gamma a ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos ha)
  have hz : ((a : ℂ) + (s : ℂ) * Complex.I) / 2 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have harg : (((a + 2 : ℝ) : ℂ) + (s : ℂ) * Complex.I) / 2 =
      ((a : ℂ) + (s : ℂ) * Complex.I) / 2 + 1 := by
    push_cast
    ring
  have hnorm : Complex.normSq (((a : ℂ) + (s : ℂ) * Complex.I) / 2) =
      (a ^ 2 + s ^ 2) / 4 := by
    simp [Complex.normSq_apply]
    ring
  have hpower : (2 : ℝ) ^ (a + 2 - 1) = 4 * (2 : ℝ) ^ (a - 1) := by
    rw [show a + 2 - 1 = (a - 1) + 2 by ring,
      Real.rpow_add (by norm_num)]
    norm_num
    ring
  have hgamma : Real.Gamma (a + 2) = (a + 1) * a * Real.Gamma a := by
    rw [show a + 2 = (a + 1) + 1 by ring,
      Real.Gamma_add_one ha1, Real.Gamma_add_one ha0]
    ring
  unfold thetaCuspPrimitiveRayBetaFourierDensity
  rw [harg, Complex.Gamma_add_one _ hz, Complex.normSq_mul, hnorm,
    hpower, hgamma]
  field_simp [ha0, ha1, hG]

theorem thetaCuspPrimitiveRayBetaFourierDensity_add_four
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    thetaCuspPrimitiveRayBetaFourierDensity (a + 4) s =
      ((a ^ 2 + s ^ 2) * ((a + 2) ^ 2 + s ^ 2)) /
          (a * (a + 1) * (a + 2) * (a + 3)) *
        thetaCuspPrimitiveRayBetaFourierDensity a s := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha1 : a + 1 ≠ 0 := by linarith
  have ha2 : a + 2 ≠ 0 := by linarith
  have ha3 : a + 3 ≠ 0 := by linarith
  rw [show a + 4 = (a + 2) + 2 by ring,
    thetaCuspPrimitiveRayBetaFourierDensity_add_two (by linarith : 0 < a + 2),
    thetaCuspPrimitiveRayBetaFourierDensity_add_two ha]
  field_simp [ha0, ha1, ha2, ha3]
  ring

def thetaCuspPrimitiveRayBetaFourierIntegrand (a s t : ℝ) : ℂ :=
  ((Real.cosh t ^ (-a) : ℝ) : ℂ) *
    Complex.exp (-((s : ℂ) * (t : ℂ)) * Complex.I)

theorem integrable_thetaCuspPrimitiveRayBetaFourierIntegrand
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Integrable (thetaCuspPrimitiveRayBetaFourierIntegrand a s) := by
  have hcont : Continuous (thetaCuspPrimitiveRayBetaFourierIntegrand a s) := by
    unfold thetaCuspPrimitiveRayBetaFourierIntegrand
    have hc : Continuous (fun t : ℝ => Real.cosh t ^ (-a)) :=
      Real.continuous_cosh.rpow_const (fun t => Or.inl (Real.cosh_pos t).ne')
    fun_prop
  refine (HTGeometry.integrable_cosh_rpow_neg ha).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards [] with t
  unfold thetaCuspPrimitiveRayBetaFourierIntegrand
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (Real.cosh_pos t) _), Complex.norm_exp]
  simp

theorem integral_thetaCuspPrimitiveRayBetaFourierIntegrand
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (∫ t : ℝ, thetaCuspPrimitiveRayBetaFourierIntegrand a s t) =
      (thetaCuspPrimitiveRayBetaFourierDensity a s : ℂ) :=
  HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal ha s

end
end RHTower
