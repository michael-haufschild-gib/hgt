import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalSurplusRescale

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial
open scoped QuadraticAlgebra

def flatSourcePolynomial (k : ℂ) : Polynomial ℂ :=
  kineticSourcePolynomial ThetaRatioSquare.reducedSlope 9 k

def flatSourceSurplus (k z : ℂ) : Polynomial ℂ := flatSurplus k z (flatSourcePolynomial k)

theorem graded_source_remainders (h : ℂ) (hh : h≠0) :
    gradedAtScalar h (1/3)*gradedAtChange h gradedRemainder=
      gradedAtScalar h (h^22)*flatToGraded h hh
        (flatNormal (inverseClockK h) (flatSourcePolynomial (inverseClockK h))) := by
  have he := congrArg (gradedAtEval h) (complete_terminal_graded_source h hh)
  simp only [map_mul,gradedAtEval_C] at he
  rw [←gradedAtChange_remainder,←flatToGraded_normal] at he
  exact he

theorem gradedReducedRead_eval (h z : ℂ) (hh : h≠0) :
    (gradedReducedRead z).eval (C h)=
      C (h^22)*surplusSubstitution h (flatSourceSurplus (inverseClockK h) z) := by
  let N := flatNormal (inverseClockK h) (flatSourcePolynomial (inverseClockK h))
  have hr := congrArg QuadraticAlgebra.re (graded_source_remainders h hh)
  have hi := congrArg QuadraticAlgebra.im (graded_source_remainders h hh)
  simp only [gradedAtScalar,RingHom.comp_apply,QuadraticAlgebra.re_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,add_zero] at hr
  simp only [gradedAtScalar,RingHom.comp_apply,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,add_zero] at hi
  change C (1/3)*gradedRemainder.re.eval (C h)=C (h^22)*surplusSubstitution h N.re at hr
  change C (1/3)*gradedRemainder.im.eval (C h)=
    C (h^22)*(C (1/(3*h))*surplusSubstitution h N.im) at hi
  have hc : (C (3*z)*C h)*C (1/(3*h))=C z := by
    rw [←map_mul,←map_mul]
    congr 1
    field_simp [hh]
  simp only [gradedReducedRead,gradedRead,eval_mul,eval_add,eval_C,eval_X]
  calc
    _ = C (1/3)*gradedRemainder.re.eval (C h)+
        (C (3*z)*C h)*(C (1/3)*gradedRemainder.im.eval (C h)) := by ring
    _ = C (h^22)*surplusSubstitution h N.re+
        (C (3*z)*C h)*(C (h^22)*(C (1/(3*h))*surplusSubstitution h N.im)) := by rw [hr,hi]
    _ = C (h^22)*(surplusSubstitution h N.re+
        ((C (3*z)*C h)*C (1/(3*h)))*surplusSubstitution h N.im) := by ring
    _ = C (h^22)*(surplusSubstitution h N.re+C z*surplusSubstitution h N.im) := by rw [hc]
    _ = _ := by simp [flatSourceSurplus,flatSurplus,N,surplusSubstitution]

theorem gradedReducedRead_coeff (h z : ℂ) (hh : h≠0) (n : ℕ) :
    ((gradedReducedRead z).eval (C h)).coeff n=
      h^22*(flatSourceSurplus (inverseClockK h) z).coeff n*(1/h^2)^n := by
  rw [gradedReducedRead_eval _ _ hh,coeff_C_mul,surplusSubstitution_coeff]
  ring

theorem gradedReducedRead_six (h z : ℂ) (hh : h≠0) :
    ((gradedReducedRead z).eval (C h)).coeff 6=
      h^10*(flatSourceSurplus (inverseClockK h) z).coeff 6 := by
  rw [gradedReducedRead_coeff _ _ hh]
  have hp : h^22*(1/h^2)^6=h^10 := by
    field_simp [hh]
  calc
    _ = (h^22*(1/h^2)^6)*(flatSourceSurplus (inverseClockK h) z).coeff 6 := by ring
    _ = _ := by rw [hp]


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
