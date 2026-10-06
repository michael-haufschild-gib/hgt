import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalHomogeneousSlope
import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlopeSeam

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial ThetaRatioSquare ThetaRatioInfinity

theorem pull_eval (P : Poly) (Y T : ℂ) :
    eval (terminalPoint Y T) (pull P)=eval (basePoint 3 ((Y-1)/3) (T+Y+1)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,pull_X,eval_X,hP]
    congr 1
    cases i <;> norm_num [pullCoord,y,t,terminalPoint,basePoint,map_ofNat]
    ring

theorem square_eval_three (P : Poly) (k z : ℂ) :
    eval (basePoint 3 k z) (square P)=eval (basePoint 9 k z) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => cases i <;> norm_num [hP,squareCoord,basePoint]

theorem shear_eval_three (P : Poly) (k z : ℂ) :
    eval (basePoint 3 k z) (shear P)=eval (basePoint 3 k (3*z)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P i hP => cases i <;> simp [hP,shearCoord,basePoint]

theorem reducedSlope_terminal_eval (Y T : ℂ) :
    eval (basePoint 9 ((Y-1)/3) ((T+Y+1)/3)) reducedSlope=
      (1/3)*eval (terminalPoint Y T) (pull integerThirdSlope) := by
  have he := congrArg (eval (basePoint 3 ((Y-1)/3) ((T+Y+1)/3))) integerSlope_shear_factor
  rw [shear_eval_three,map_mul,square_eval_three,eval_X] at he
  simp only [basePoint] at he
  rw [show 3*((T+Y+1)/3)=T+Y+1 by ring] at he
  rw [pull_eval]
  linear_combination -he/3

theorem reducedSlope_regularization (Y T h : ℂ) (hh : h≠0) :
    (1/3)*(slopeRegularized Y T).eval h=
      h^22*eval (basePoint 9 ((Y/h-1)/3) ((T/h+Y/h+1)/3)) reducedSlope := by
  rw [slopeRegularized_eval _ _ _ hh,reducedSlope_terminal_eval]
  ring

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
