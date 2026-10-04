import GaloisForLFunctions.RHTower.ThetaCuspRatioAxisCompleteMoments

namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def axisMinorValueNorm (h : ℂ) :
    {c : ℂ // axisMinorMass⁻¹*(axis scaledMinor).eval h=c} := by
  have he : axisMinorMass⁻¹*(axis scaledMinor).eval h=
      axisMinorMass⁻¹*(axis scaledMinor).eval h := rfl
  conv at he =>
    rhs
    simp only [scaledMinor,map_add,map_sub,map_mul,map_neg,map_pow,map_ofNat,axis_X,axisCoord,
      Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_neg,
      Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X]
    rw [(axisMoment2ValueNorm h).property,(axisMoment4ValueNorm h).property,
      (axisMoment6ValueNorm h).property,(axisMoment8ValueNorm h).property,
      (axisMoment10ValueNorm h).property]
    norm_num [axisMoment2ValueNorm,axisMoment4ValueNorm,axisMoment6ValueNorm,
      axisMoment8ValueNorm,axisMoment10ValueNorm,axisMinorMass]
    ring_nf (config := {mode := .raw})
  exact ⟨_,he⟩

def axisMinorShape : Polynomial ℂ :=
  1+Polynomial.C (11/12)*Polynomial.X+Polynomial.C (205/144)*Polynomial.X^2+
  Polynomial.C (383/216)*Polynomial.X^3+Polynomial.C (5933/5184)*Polynomial.X^4+
  Polynomial.C (9265/15552)*Polynomial.X^5+Polynomial.C (17081/62208)*Polynomial.X^6+
  Polynomial.C (725/23328)*Polynomial.X^7-Polynomial.C (111199/2239488)*Polynomial.X^8-
  Polynomial.C (291577/10077696)*Polynomial.X^9-Polynomial.C (418387/60466176)*Polynomial.X^10-
  Polynomial.C (2771/2834352)*Polynomial.X^11-Polynomial.C (114995/544195584)*Polynomial.X^12-
  Polynomial.C (51773/816293376)*Polynomial.X^13-Polynomial.C (51257/4897760256)*Polynomial.X^14-
  Polynomial.C (91/136048896)*Polynomial.X^15

theorem axisMinor_normalized :
    Polynomial.C axisMinorMass⁻¹*axis scaledMinor=Polynomial.X^2*axisMinorShape := by
  apply Polynomial.funext
  intro h
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  calc
    _ = (axisMinorValueNorm h).val := (axisMinorValueNorm h).property
    _ = _ := by norm_num [axisMinorValueNorm,axisMinorShape]; ring


end
end HTGeometry.ThetaRatioInfinity
