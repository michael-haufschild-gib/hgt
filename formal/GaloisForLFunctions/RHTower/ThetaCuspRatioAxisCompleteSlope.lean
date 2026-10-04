import GaloisForLFunctions.RHTower.ThetaCuspRatioAxisCompleteMinor

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def axisSlopeOperator (P : Polynomial ℂ) :=
  (6-Polynomial.X)*(-36*Polynomial.X^2-12*Polynomial.X^3)*P.derivative+
    (17*Polynomial.X-66)*Polynomial.X*(-36-12*Polynomial.X)*P

theorem axisSlopeOperator_C_mul (P : Polynomial ℂ) (c : ℂ) :
    axisSlopeOperator (Polynomial.C c*P)=Polynomial.C c*axisSlopeOperator P := by
  unfold axisSlopeOperator
  simp only [Polynomial.derivative_mul,Polynomial.derivative_C,zero_mul,zero_add]
  ring

theorem axisSlope_eq_operator : axis scaledSlope=axisSlopeOperator (axis scaledMinor) := by
  have hc : axis clockLinear=Polynomial.X*(-36-12*Polynomial.X) := by
    apply Polynomial.funext
    intro h
    norm_num [clockLinear,axis,axisCoord,driftSquare,deficit]
    ring
  simp only [scaledSlope,map_add,map_sub,map_mul,map_ofNat,axis_X,axisCoord]
  rw [axis_flow,hc]
  unfold axisSlopeOperator
  ring

def axisSlopeShape : Polynomial ℂ :=
  (-36-12*Polynomial.X)*
    ((6-Polynomial.X)*(2*axisMinorShape+Polynomial.X*axisMinorShape.derivative)+
      (17*Polynomial.X-66)*axisMinorShape)

theorem axisSlope_normalized :
    Polynomial.C axisMinorMass⁻¹*axis scaledSlope=Polynomial.X^3*axisSlopeShape := by
  rw [axisSlope_eq_operator,←axisSlopeOperator_C_mul,axisMinor_normalized]
  unfold axisSlopeOperator axisSlopeShape
  simp only [Polynomial.derivative_mul,Polynomial.derivative_pow,Polynomial.derivative_X]
  norm_num [Polynomial.C_ofNat]
  ring

def axisSlopeValueNorm (h : ℂ) : {c : ℂ // axisSlopeShape.eval h=c} := by
  have he : axisSlopeShape.eval h=axisSlopeShape.eval h := rfl
  conv at he =>
    rhs
    norm_num [axisSlopeShape,axisMinorShape,Polynomial.derivative_add,
      Polynomial.derivative_sub,Polynomial.derivative_mul,Polynomial.derivative_pow]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisSlopePositiveForm (h : ℝ) : ℝ :=
  1944+1692*h+(4077/2)*h^2+(8781/4)*h^3+(24335/24)*h^4+
  h^5*((3491/16-4619/288-454729/5184-51673/1152)+
    (1-h)*(4619/288+(454729/5184)*(1+h)+(51673/1152)*(1+h+h^2)))+
  (41155/6912)*h^9+(6670877/559872)*h^10+(793001/186624)*h^11+
  (1400219/1679616)*h^12+(2572699/15116544)*h^13+
  (210335/5038848)*h^14+(296285/45349632)*h^15+(169193/408146688)*h^16

theorem axisSlopeShape_re (h : ℝ) :
    (axisSlopeShape.eval (h:ℂ)).re=axisSlopePositiveForm h := by
  rw [(axisSlopeValueNorm (h:ℂ)).property]
  norm_num [axisSlopeValueNorm,axisSlopePositiveForm,Complex.mul_re,←Complex.ofReal_pow]
  ring

theorem axisSlopeShape_pos {h : ℝ} (h0 : 0≤h) (h1 : h≤1) :
    0<(axisSlopeShape.eval (h:ℂ)).re := by
  rw [axisSlopeShape_re]
  have hr : (0:ℝ)<3491/16-4619/288-454729/5184-51673/1152 := by norm_num
  have hd : 0≤1-h := sub_nonneg.mpr h1
  unfold axisSlopePositiveForm
  positivity

theorem axis_scaledSlope_pos {h : ℝ} (h0 : 0<h) (h1 : h≤1) :
    0<(eval (basePoint (h:ℂ) 0 0) scaledSlope).re := by
  have he := congrArg (Polynomial.eval (h:ℂ)) axisSlope_normalized
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X] at he
  have hp := axisSlopeShape_pos h0.le h1
  have hs : 0<(((h:ℂ)^3)*axisSlopeShape.eval (h:ℂ)).re := by
    simpa only [←Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using (mul_pos (pow_pos h0 3) hp)
  rw [←he] at hs
  rw [←axis_eval]
  norm_num [axisMinorMass,Complex.mul_re] at hs
  nlinarith only [hs]

end
end HTGeometry.ThetaRatioInfinity
