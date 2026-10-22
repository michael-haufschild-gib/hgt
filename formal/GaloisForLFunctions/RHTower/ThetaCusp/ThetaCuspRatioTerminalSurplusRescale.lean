import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalGradedSpecialization

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial
open scoped QuadraticAlgebra

abbrev FlatQuadratic (k : ℂ) := QuadraticAlgebra (Polynomial ℂ)
  (C ((k-1)/9)-C (1/9)*X) (C ((2-k)/3))

def flatScalar (k : ℂ) : ℂ →+* FlatQuadratic k :=
  (algebraMap (Polynomial ℂ) (FlatQuadratic k)).comp C

def flatNormal (k : ℂ) : Polynomial ℂ →+* FlatQuadratic k :=
  eval₂RingHom (flatScalar k) QuadraticAlgebra.omega

def flatSurplus (k z : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  (flatNormal k P).re+C z*(flatNormal k P).im

def inverseClockK (h : ℂ) : ℂ := (1/h-1)/3

def surplusSubstitution (h : ℂ) : Polynomial ℂ →+* Polynomial ℂ :=
  eval₂RingHom C (C (1/h^2)*X)

theorem surplusSubstitution_coeff (h : ℂ) (P : Polynomial ℂ) (n : ℕ) :
    (surplusSubstitution h P).coeff n=P.coeff n*(1/h^2)^n := by
  exact comp_C_mul_X_coeff

theorem gradedMass_eval (h : ℂ) : gradedMass.eval (C h)=C ((h-4*h^2)/3)-X := by
  apply Polynomial.funext
  intro e
  simp [gradedMass]
  ring

theorem gradedDrift_eval (h : ℂ) : gradedDrift.eval (C h)=C ((7*h-1)/3) := by
  apply Polynomial.funext
  intro e
  simp [gradedDrift]
  ring

theorem quadratic_rescale_mass (h : ℂ) (hh : h≠0) :
    (C (1/(3*h)))^2*gradedMass.eval (C h)=
      surplusSubstitution h (C ((inverseClockK h-1)/9)-C (1/9)*X) := by
  rw [gradedMass_eval]
  apply Polynomial.funext
  intro e
  simp [surplusSubstitution,inverseClockK]
  field_simp [hh]
  ring

theorem quadratic_rescale_drift (h : ℂ) (hh : h≠0) :
    C (1/(3*h))*gradedDrift.eval (C h)=
      surplusSubstitution h (C ((2-inverseClockK h)/3)) := by
  rw [gradedDrift_eval]
  apply Polynomial.funext
  intro e
  simp [surplusSubstitution,inverseClockK]
  field_simp [hh]
  ring

def flatToGraded (h : ℂ) (hh : h≠0) : FlatQuadratic (inverseClockK h) →+* GradedAt h :=
  quadraticScale (surplusSubstitution h) (C (1/(3*h)))
    (quadratic_rescale_mass h hh) (quadratic_rescale_drift h hh)

theorem flatToGraded_scalar (h : ℂ) (hh : h≠0) (c : ℂ) :
    flatToGraded h hh (flatScalar (inverseClockK h) c)=gradedAtScalar h c := by
  simp [flatToGraded,flatScalar,gradedAtScalar,quadraticScale_scalar,surplusSubstitution]

theorem flatToGraded_omega (h : ℂ) (hh : h≠0) :
    flatToGraded h hh QuadraticAlgebra.omega=
      gradedAtScalar h (1/(3*h))*QuadraticAlgebra.omega :=
  quadraticScale_omega _ _ _ _

theorem flatToGraded_scalar_hom (h : ℂ) (hh : h≠0) :
    (flatToGraded h hh).comp (flatScalar (inverseClockK h))=gradedAtScalar h := by
  apply RingHom.ext
  intro c
  exact flatToGraded_scalar h hh c

theorem flatToGraded_normal (h : ℂ) (hh : h≠0) (P : Polynomial ℂ) :
    flatToGraded h hh (flatNormal (inverseClockK h) P)=
      gradedAtEval h (P.comp (C (1/(3*h))*X)) := by
  change flatToGraded h hh (P.eval₂ (flatScalar (inverseClockK h)) QuadraticAlgebra.omega)=
    (P.comp (C (1/(3*h))*X)).eval₂ (gradedAtScalar h) QuadraticAlgebra.omega
  rw [hom_eval₂,flatToGraded_scalar_hom,flatToGraded_omega,eval₂_comp]
  simp


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
