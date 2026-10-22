import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalMinorDerivatives

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def slopeHomogeneous (Y T : ℂ) : Polynomial ℂ :=
  12*((Polynomial.C (2*Y)-3*Polynomial.X)*
    (Polynomial.C Y*(Polynomial.C (Y+T)+Polynomial.X)*minorYHomogeneous Y T+
      Polynomial.X*Polynomial.C T*minorTHomogeneous Y T)-
    12*Polynomial.C Y*(Polynomial.C (Y+T)+Polynomial.X)*minorHomogeneous Y T)

theorem slopeHomogeneous_zero (Y T : ℂ) : (slopeHomogeneous Y T).coeff 0=0 := by
  norm_num [slopeHomogeneous,minorYHomogeneous_zero,minorTHomogeneous_zero,
    minorHomogeneous_zero]

theorem slopeHomogeneous_one (Y T : ℂ) :
    (slopeHomogeneous Y T).coeff 1=221184*(12:ℂ)^18*Y^5*(T+Y)^2*T^15 := by
  norm_num [slopeHomogeneous,Polynomial.mul_coeff_one,minorYHomogeneous_zero,
    minorTHomogeneous_zero,minorHomogeneous_zero,minorYHomogeneous_one,minorHomogeneous_one]
  ring

theorem pull_integerThirdSlope : pull integerThirdSlope=
    12*((2*y-3)*delta (pull integerThirdMinor)-12*pull integerThirdMinor*y*(y+t+1)) := by
  have hs : delta (2*y-3)=2*y*(y+t+1) := by
    simp [delta,y,t,pderiv_X]
    ring
  simp only [integerThirdSlope,map_sub,map_mul,map_ofNat,pull_lie,pull_integerJet,
    pow_zero,map_one,one_mul,jet,hs]
  ring

theorem slopeHomogeneous_eval (Y T h : ℂ) (hh : h≠0) :
    (slopeHomogeneous Y T).eval h=
      h^23*eval (terminalPoint (Y/h) (T/h)) (pull integerThirdSlope) := by
  rw [pull_integerThirdSlope]
  simp only [slopeHomogeneous,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,
    delta,map_mul,map_sub,map_add,map_ofNat,map_one,y,t,eval_X,terminalPoint]
  rw [minorHomogeneous_eval _ _ _ hh,minorYHomogeneous_eval _ _ _ hh,
    minorTHomogeneous_eval _ _ _ hh]
  field_simp [hh]

def slopeRegularized (Y T : ℂ) : Polynomial ℂ := (slopeHomogeneous Y T).divX

theorem slopeRegularized_zero (Y T : ℂ) :
    (slopeRegularized Y T).coeff 0=221184*(12:ℂ)^18*Y^5*(T+Y)^2*T^15 := by
  rw [slopeRegularized,Polynomial.coeff_divX]
  exact slopeHomogeneous_one Y T

theorem slopeRegularized_eval (Y T h : ℂ) (hh : h≠0) :
    (slopeRegularized Y T).eval h=
      h^22*eval (terminalPoint (Y/h) (T/h)) (pull integerThirdSlope) := by
  have hp : Polynomial.X*slopeRegularized Y T=slopeHomogeneous Y T := by
    simpa only [slopeRegularized,slopeHomogeneous_zero,map_zero,add_zero] using
      Polynomial.X_mul_divX_add (slopeHomogeneous Y T)
  have hv := congrArg (Polynomial.eval h) hp
  simp only [Polynomial.eval_mul,Polynomial.eval_X] at hv
  rw [slopeHomogeneous_eval Y T h hh] at hv
  apply mul_left_cancel₀ hh
  calc
    h*(slopeRegularized Y T).eval h =
      h^23*eval (terminalPoint (Y/h) (T/h)) (pull integerThirdSlope) := hv
    _ = h*(h^22*eval (terminalPoint (Y/h) (T/h)) (pull integerThirdSlope)) := by ring

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
