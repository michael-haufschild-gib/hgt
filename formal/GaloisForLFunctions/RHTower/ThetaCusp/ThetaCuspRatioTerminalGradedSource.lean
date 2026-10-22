import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalGradedRemainder

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial ThetaRatioInfinity ThetaRatioSquare

def kineticSourceCoord (v k : ℂ) : Coord → Polynomial ℂ
  | .U => C v
  | .K => C k
  | .J => X

def kineticSourcePolynomial (P : Poly) (v k : ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom C (kineticSourceCoord v k) P

theorem kineticSourcePolynomial_eval (P : Poly) (v k z : ℂ) :
    (kineticSourcePolynomial P v k).eval z=MvPolynomial.eval (basePoint v k z) P := by
  unfold kineticSourcePolynomial
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add,eval_add,hP,hQ]
  | mul_X P i hP =>
    simp only [map_mul,MvPolynomial.eval₂Hom_X',MvPolynomial.eval_X,
      eval_mul,hP]
    congr 1
    cases i <;> simp [kineticSourceCoord,basePoint]

def shiftedSlopeFamily (h : ℂ) : Polynomial ℂ :=
  terminalFamilyEval C (X-1-C h) (C h) slopeFamily

theorem shiftedSlopeFamily_eval (h w : ℂ) :
    (shiftedSlopeFamily h).eval w=(slopeRegularized 1 (w-1-h)).eval h := by
  have he := terminalFamilyEval_hom (C:ℂ →+* Polynomial ℂ) (evalRingHom w)
    (X-1-C h) (C h) slopeFamily
  have hc : (evalRingHom w).comp C=RingHom.id ℂ := by ext c; simp
  rw [hc] at he
  simp only [coe_evalRingHom,eval_sub,eval_X,eval_one,eval_C] at he
  rw [terminalFamilyEval_complex,specialize_slopeFamily] at he
  exact he

theorem complete_terminal_graded_source (h : ℂ) (hh : h≠0) :
    C (1/3)*shiftedSlopeFamily h=
      C (h^22)*(kineticSourcePolynomial ThetaRatioSquare.reducedSlope 9 ((1/h-1)/3)).comp
        (C (1/(3*h))*X) := by
  apply Polynomial.funext
  intro w
  simp only [eval_mul,eval_C,eval_comp,eval_X]
  rw [shiftedSlopeFamily_eval,reducedSlope_regularization _ _ _ hh,
    kineticSourcePolynomial_eval]
  have hc : ((w-1-h)/h+1/h+1)/3=1/(3*h)*w := by
    field_simp [hh]
    ring
  rw [hc]


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
