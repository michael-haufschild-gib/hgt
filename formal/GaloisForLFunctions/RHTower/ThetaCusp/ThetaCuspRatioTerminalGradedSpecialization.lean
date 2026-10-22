import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalGradedSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalQuadraticScale

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial
open scoped QuadraticAlgebra

abbrev GradedAt (h : ℂ) := QuadraticAlgebra (Polynomial ℂ)
  (gradedMass.eval (C h)) (gradedDrift.eval (C h))

def gradedAtChange (h : ℂ) : GradedQuadratic →+* GradedAt h :=
  quadraticChange (evalRingHom (C h)) rfl rfl

def gradedAtScalar (h : ℂ) : ℂ →+* GradedAt h :=
  (algebraMap (Polynomial ℂ) (GradedAt h)).comp C

def gradedAtEval (h : ℂ) : Polynomial ℂ →+* GradedAt h :=
  eval₂RingHom (gradedAtScalar h) QuadraticAlgebra.omega

theorem gradedAtChange_scalar (h c : ℂ) :
    gradedAtChange h (gradedScalar c)=gradedAtScalar h c := by
  simp [gradedAtChange,gradedScalar,gradedAtScalar,quadraticChange_scalar]

theorem gradedAtChange_clock (h : ℂ) :
    gradedAtChange h gradedClock=gradedAtScalar h h := by
  simp [gradedAtChange,gradedClock,gradedAtScalar,quadraticChange_scalar]

theorem gradedAtChange_omega (h : ℂ) :
    gradedAtChange h QuadraticAlgebra.omega=QuadraticAlgebra.omega :=
  quadraticChange_omega _ _ _

theorem gradedAtChange_scalar_hom (h : ℂ) :
    (gradedAtChange h).comp gradedScalar=gradedAtScalar h := by
  apply RingHom.ext
  intro c
  exact gradedAtChange_scalar h c

theorem gradedAtEval_C (h c : ℂ) : gradedAtEval h (C c)=gradedAtScalar h c := by
  simp [gradedAtEval]

theorem gradedAtEval_X (h : ℂ) : gradedAtEval h X=QuadraticAlgebra.omega := by
  simp [gradedAtEval]

theorem gradedAtEval_C_hom (h : ℂ) : (gradedAtEval h).comp C=gradedAtScalar h :=
  eval₂RingHom_comp_C _ _

theorem gradedAtChange_remainder (h : ℂ) :
    gradedAtChange h gradedRemainder=gradedAtEval h (shiftedSlopeFamily h) := by
  rw [gradedRemainder,terminalFamilyEval_hom,shiftedSlopeFamily,terminalFamilyEval_hom,
    gradedAtChange_scalar_hom,gradedAtEval_C_hom]
  simp only [map_sub,map_one,gradedAtChange_omega,gradedAtChange_clock,
    gradedAtEval_X,gradedAtEval_C]

theorem gradedRead_eval (h z : ℂ) :
    (gradedRead z).eval (C h)=
      (gradedAtEval h (shiftedSlopeFamily h)).re+
        C (3*z*h)*(gradedAtEval h (shiftedSlopeFamily h)).im := by
  have hr := congrArg QuadraticAlgebra.re (gradedAtChange_remainder h)
  have hi := congrArg QuadraticAlgebra.im (gradedAtChange_remainder h)
  change gradedRemainder.re.eval (C h)=_ at hr
  change gradedRemainder.im.eval (C h)=_ at hi
  simp only [gradedRead,eval_add,eval_mul,eval_C,eval_X,hr,hi,map_mul]


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
