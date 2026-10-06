import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalGradedFamily
import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalQuadraticChange

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open Polynomial
open scoped QuadraticAlgebra

def terminalFamilyEval {R : Type*} [CommRing R]
    (c : ℂ →+* R) (T h : R) : TerminalFamily →+* R :=
  eval₂RingHom (eval₂RingHom c T) h

theorem terminalFamilyEval_hom {R S : Type*} [CommRing R] [CommRing S]
    (c : ℂ →+* R) (f : R →+* S) (T h : R) (P : TerminalFamily) :
    f (terminalFamilyEval c T h P)=terminalFamilyEval (f.comp c) (f T) (f h) P := by
  change f (P.eval₂ (eval₂RingHom c T) h)=P.eval₂ (eval₂RingHom (f.comp c) (f T)) (f h)
  rw [hom_eval₂]
  congr 1
  apply RingHom.ext
  intro q
  exact hom_eval₂ (p:=q) (f:=c) (g:=f) T

theorem terminalFamilyEval_zero {R : Type*} [CommRing R]
    (c : ℂ →+* R) (T : R) (P : TerminalFamily) :
    terminalFamilyEval c T 0 P=(P.coeff 0).eval₂ c T := by
  exact eval₂_at_zero _

theorem terminalFamilyEval_complex (T h : ℂ) (P : TerminalFamily) :
    terminalFamilyEval (RingHom.id ℂ) T h P=(specializeTerminal T P).eval h := by
  change P.eval₂ (eval₂RingHom (RingHom.id ℂ) T) h=
    (P.map (evalRingHom T)).eval h
  rw [eval_map]
  rfl

def gradedMass : TerminalFamily := C (C (1/3))*(X-4*X^2)-C X

def gradedDrift : TerminalFamily := C (C (1/3))*(7*X-1)

abbrev GradedQuadratic := QuadraticAlgebra TerminalFamily gradedMass gradedDrift
abbrev PrincipalPolynomialQuadratic :=
  QuadraticAlgebra (Polynomial ℂ) (-X) (C (-1/3:ℂ))

def gradedScalar : ℂ →+* GradedQuadratic :=
  (algebraMap TerminalFamily GradedQuadratic).comp (C.comp C)

def gradedClock : GradedQuadratic := algebraMap TerminalFamily GradedQuadratic X

def gradedRemainder : GradedQuadratic :=
  terminalFamilyEval gradedScalar (QuadraticAlgebra.omega-1-gradedClock) gradedClock slopeFamily

def gradedRead (z : ℂ) : TerminalFamily :=
  gradedRemainder.re+C (C (3*z))*X*gradedRemainder.im

def gradedChange : GradedQuadratic →+* PrincipalPolynomialQuadratic :=
  quadraticChange (evalRingHom (0:Polynomial ℂ))
    (by simp [gradedMass]) (by simp [gradedDrift,neg_div])

theorem gradedChange_scalar (c : ℂ) :
    gradedChange (gradedScalar c)=algebraMap (Polynomial ℂ) _ (C c) := by
  simp [gradedChange,gradedScalar,quadraticChange_scalar]

theorem gradedChange_clock : gradedChange gradedClock=0 := by
  simp [gradedChange,gradedClock,quadraticChange_scalar]

theorem gradedChange_omega : gradedChange QuadraticAlgebra.omega=QuadraticAlgebra.omega :=
  quadraticChange_omega _ _ _

theorem gradedChange_scalar_hom : gradedChange.comp gradedScalar=
    (algebraMap (Polynomial ℂ) PrincipalPolynomialQuadratic).comp C := by
  apply RingHom.ext
  intro c
  exact gradedChange_scalar c

theorem gradedChange_remainder : gradedChange gradedRemainder=
    221184*(12:PrincipalPolynomialQuadratic)^18*QuadraticAlgebra.omega^2*
      (QuadraticAlgebra.omega-1)^15 := by
  unfold gradedRemainder
  rw [terminalFamilyEval_hom,gradedChange_scalar_hom]
  simp only [map_sub,map_one,gradedChange_omega,gradedChange_clock,sub_zero]
  rw [terminalFamilyEval_zero,slopeFamily_zero]
  simp [eval₂_pow]

theorem gradedRead_zero (z : ℂ) : (gradedRead z).coeff 0=
    221184*(12:Polynomial ℂ)^18*
      (((QuadraticAlgebra.omega:PrincipalPolynomialQuadratic)^2)*
        (QuadraticAlgebra.omega-1)^15).re := by
  have he := congrArg QuadraticAlgebra.re gradedChange_remainder
  change gradedRemainder.re.eval (0:Polynomial ℂ)=_ at he
  rw [←coeff_zero_eq_eval_zero] at he
  simp only [gradedRead,coeff_add,mul_coeff_zero,coeff_X_zero,mul_zero,zero_mul,add_zero]
  rw [he]
  have hs : (221184:PrincipalPolynomialQuadratic)*12^18 =
      algebraMap (Polynomial ℂ) _ (221184*(12:Polynomial ℂ)^18) := by
    simp [map_ofNat]
  rw [mul_assoc,hs]
  simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im,mul_zero,zero_mul,add_zero]

def principalPolynomialValue : Polynomial ℂ :=
  (((QuadraticAlgebra.omega:PrincipalPolynomialQuadratic)^2)*
    (QuadraticAlgebra.omega-1)^15).re

theorem principalPolynomialValue_eval (e : ℂ) :
    principalPolynomialValue.eval e=principalQuadraticValue e := by
  let f : PrincipalPolynomialQuadratic →+* PrincipalQuadratic e :=
    quadraticChange (evalRingHom e) (by simp) (by simp)
  have hw : f QuadraticAlgebra.omega=QuadraticAlgebra.omega :=
    quadraticChange_omega _ _ _
  change (f (((QuadraticAlgebra.omega:PrincipalPolynomialQuadratic)^2)*
    (QuadraticAlgebra.omega-1)^15)).re=principalQuadraticValue e
  rw [map_mul,map_pow,map_pow,map_sub,map_one,hw]
  rfl

theorem principalReducedSurplusPolynomial_complex_eval (e : ℂ) :
    (principalReducedSurplusPolynomial.map Complex.ofRealHom).eval e=
      (73728*(12:ℂ)^18/(6:ℂ)^15)*e*deficitShape (1-36*e) := by
  simp [principalReducedSurplusPolynomial,principalSurplusPolynomial,
    Polynomial.map_sum,Polynomial.eval_finsetSum,deficitShape,map_ofNat]
  ring

def gradedReducedRead (z : ℂ) : TerminalFamily := C (C (1/3))*gradedRead z

theorem gradedReducedRead_zero (z : ℂ) : (gradedReducedRead z).coeff 0=
    principalReducedSurplusPolynomial.map Complex.ofRealHom := by
  rw [gradedReducedRead,coeff_C_mul,gradedRead_zero]
  apply Polynomial.funext
  intro e
  change (C (1/3)*(221184*12^18*principalPolynomialValue)).eval e=_
  simp only [eval_mul,eval_C,eval_ofNat,eval_pow]
  rw [principalPolynomialValue_eval,principalQuadraticValue_eq,
    principalReducedSurplusPolynomial_complex_eval]
  ring

theorem gradedReducedRead_zero_six (z : ℂ) :
    ((gradedReducedRead z).coeff 0).coeff 6= -(8192/3)*189994*(12:ℂ)^18 := by
  rw [gradedReducedRead_zero,coeff_map,principalReducedSurplusPolynomial_coeff_six]
  norm_num


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
