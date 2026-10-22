import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCubicSlopeJets
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare Filter Topology

theorem nonlinearSlope_coeff_zero (r : ℂ) :
    (affineLine r (nonlinearShift scaledSlope)).coeff 0=0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,affineLine_eval]
  exact (nonlinearSlope_low_jets r).1
theorem nonlinearSlope_coeff_one (r : ℂ) :
    (affineLine r (nonlinearShift scaledSlope)).coeff 1=0 := by
  have he := (nonlinearSlope_low_jets r).2.1
  simp only [planeJet1,planeValue,←affineLine_eval,←affineLine_derivative] at he
  simpa [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] using he
theorem nonlinearSlope_coeff_two (r : ℂ) :
    (affineLine r (nonlinearShift scaledSlope)).coeff 2=0 := by
  have he := (nonlinearSlope_low_jets r).2.2
  simp only [planeJet2,planeValue,←affineLine_eval,←affineLine_derivative] at he
  norm_num [←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_derivative] at he
  exact he

def nonlinearSlopeCore (r : ℂ) : Polynomial ℂ :=
  (affineLine r (nonlinearShift scaledSlope)).divX.divX.divX

theorem nonlinearSlope_factor (r : ℂ) :
    affineLine r (nonlinearShift scaledSlope)=Polynomial.X^3*nonlinearSlopeCore r := by
  have h0 : affineLine r (nonlinearShift scaledSlope)=
      Polynomial.X*(affineLine r (nonlinearShift scaledSlope)).divX := by
    simpa [nonlinearSlope_coeff_zero] using
      (Polynomial.X_mul_divX_add (affineLine r (nonlinearShift scaledSlope))).symm
  have h1 : (affineLine r (nonlinearShift scaledSlope)).divX=
      Polynomial.X*(affineLine r (nonlinearShift scaledSlope)).divX.divX := by
    simpa [Polynomial.coeff_divX,nonlinearSlope_coeff_one] using
      (Polynomial.X_mul_divX_add (affineLine r (nonlinearShift scaledSlope)).divX).symm
  have h2 : (affineLine r (nonlinearShift scaledSlope)).divX.divX=
      Polynomial.X*nonlinearSlopeCore r := by
    simpa [nonlinearSlopeCore,Polynomial.coeff_divX,nonlinearSlope_coeff_two] using
      (Polynomial.X_mul_divX_add (affineLine r (nonlinearShift scaledSlope)).divX.divX).symm
  rw [h0,h1,h2]
  ring

theorem nonlinearSlopeCore_zero (r : ℂ) :
    (nonlinearSlopeCore r).eval 0=1944*axisMinorMass-63*principalMass*r^2 := by
  simpa [nonlinearSlopeCore,←Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_divX] using
    nonlinearSlope_coeff_three r

theorem nonlinearSlopeCore_real_zero (r : ℝ) :
    ((nonlinearSlopeCore (r:ℂ)).eval 0).re=
      63*((6:ℝ)^24*1990656*1679616)*(122880/7-r^2) := by
  have hm : axisMinorMass=(5120/9)*principalMass := by norm_num [axisMinorMass,principalMass]
  have he : 1944*axisMinorMass-63*principalMass*(r:ℂ)^2=
      63*principalMass*((122880/7:ℂ)-(r:ℂ)^2) := by rw [hm]; ring
  rw [nonlinearSlopeCore_zero,he,principalMass_real]
  norm_cast
  simp [Complex.mul_re, Complex.sub_re, -Complex.ofReal_pow]

theorem nonlinearSlope_value (h r : ℝ) :
    regularSlopeValue h r (r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3)=
      h^3*((nonlinearSlopeCore (r:ℂ)).eval (h:ℂ)).re := by
  have he := congrArg (Polynomial.eval (h:ℂ)) (nonlinearSlope_factor (r:ℂ))
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    affineLine_eval,nonlinearShift_eval,zero_add] at he
  have hcst : (r:ℂ)*(1/12-7*(h:ℂ)/72)+((r:ℂ)^2/144)*(h:ℂ)^2-
      (7*(r:ℂ)^2/432)*(h:ℂ)^3=
      ((r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3:ℝ):ℂ) := by push_cast; ring
  rw [hcst] at he
  have hre := congrArg Complex.re he
  simpa only [regularSlopeValue,←Complex.ofReal_pow,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hre

theorem nonlinearSlope_sign (r : ℝ) :
    (r^2<122880/7 → ∀ᶠ h in 𝓝[>] (0:ℝ),
      0<regularSlopeValue h r (r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3)) ∧
    (122880/7<r^2 → ∀ᶠ h in 𝓝[>] (0:ℝ),
      regularSlopeValue h r (r*(1/12-7*h/72)+(r^2/144)*h^2-(7*r^2/432)*h^3)<0) := by
  have hc : Continuous (fun h : ℝ => ((nonlinearSlopeCore (r:ℂ)).eval (h:ℂ)).re) :=
    Complex.continuous_re.comp ((nonlinearSlopeCore (r:ℂ)).continuous.comp Complex.continuous_ofReal)
  have hC : 0<(63:ℝ)*((6:ℝ)^24*1990656*1679616) := by positivity
  constructor
  · intro hr
    have hz : 0<((nonlinearSlopeCore (r:ℂ)).eval 0).re := by
      rw [nonlinearSlopeCore_real_zero]
      exact mul_pos hC (sub_pos.mpr hr)
    have hn := hc.continuousAt.eventually_const_lt hz
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
    rw [nonlinearSlope_value]
    exact mul_pos (pow_pos hh 3) hn
  · intro hr
    have hz : ((nonlinearSlopeCore (r:ℂ)).eval 0).re<0 := by
      rw [nonlinearSlopeCore_real_zero]
      exact mul_neg_of_pos_of_neg hC (sub_neg.mpr hr)
    have hn := hc.continuousAt.eventually_lt_const hz
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with h hn hh
    rw [nonlinearSlope_value]
    exact mul_neg_of_pos_of_neg (pow_pos hh 3) hn

end
end HTGeometry.ThetaRatioInfinity
