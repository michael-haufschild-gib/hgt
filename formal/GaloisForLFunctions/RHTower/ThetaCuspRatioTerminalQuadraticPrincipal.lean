import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalPrincipalAlgebra
import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open scoped QuadraticAlgebra

theorem map_deficitShape {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d : R) : f (deficitShape d)=deficitShape (f d) := by
  simp [deficitShape]

theorem quadratic_constant_selection {R : Type*} [CommRing R] {a b : R}
    (F : QuadraticAlgebra R a b) :
    (QuadraticAlgebra.omega-star QuadraticAlgebra.omega)*algebraMap R _ F.re=
      QuadraticAlgebra.omega*star F-star QuadraticAlgebra.omega*F := by
  ext <;> simp
  ring

abbrev PrincipalQuadratic (e : ℂ) := QuadraticAlgebra ℂ (-e) (-1/3:ℂ)

def principalQuadraticValue (e : ℂ) : ℂ :=
  (((QuadraticAlgebra.omega : PrincipalQuadratic e)^2)*
    ((QuadraticAlgebra.omega : PrincipalQuadratic e)-1)^15).re

-- Exact constant remainder, also at the double-root value 36e=1.
-- The coefficient of omega cancels the conjugate difference without division by it.
theorem principalQuadraticValue_eq (e : ℂ) :
    principalQuadraticValue e=e/(6:ℂ)^15*deficitShape (1-36*e) := by
  let w : PrincipalQuadratic e := QuadraticAlgebra.omega
  let C : ℂ →+* PrincipalQuadratic e := algebraMap ℂ (PrincipalQuadratic e)
  let D : PrincipalQuadratic e := 6*w+1
  let F : PrincipalQuadratic e := w^2*(w-1)^15
  have hD : D^2=C (1-36*e) := by
    dsimp only [D,w,C]
    ext <;> simp [pow_two] <;> ring
  have hP : deficitShape (D^2)=C (deficitShape (1-36*e)) := by
    rw [hD,←map_deficitShape]
  have hw : w*star w=C e := by
    dsimp only [w,C]
    ext <;> simp
  have h1 : 1+D= -6*star w := by
    dsimp only [D,w]
    ext <;> simp
    ring
  have h7 : 7+D= -6*(star w-1) := by
    dsimp only [D,w]
    ext <;> simp
    ring
  have hm1 : 1-D= -6*w := by dsimp only [D]; ring
  have hm7 : 7-D= -6*(w-1) := by dsimp only [D]; ring
  have ho := principal_odd_part D
  rw [h1,h7,hm1,hm7,hP,mul_pow,mul_pow] at ho
  have hdifference : (6:PrincipalQuadratic e)^16*
      (star w*(star w-1)^15-w*(w-1)^15)=
        2*D*C (deficitShape (1-36*e)) := by
    calc
      _ = (-6*star w)*((-6)^15*(star w-1)^15)-
        (-6*w)*((-6)^15*(w-1)^15) := by ring
      _ = _ := ho
  have hselect := quadratic_constant_selection F
  change (w-star w)*C F.re=w*star F-star w*F at hselect
  have hprod : w*star F-star w*F=
      C e*(star w*(star w-1)^15-w*(w-1)^15) := by
    dsimp only [F]
    simp only [star_mul,star_pow,star_sub,star_one]
    calc
      _ = (w*star w)*(star w*(star w-1)^15-w*(w-1)^15) := by ring
      _ = _ := by rw [hw]
  rw [hprod] at hselect
  have hscaled : (6:PrincipalQuadratic e)^16*((w-star w)*C F.re)=
      C e*(2*D*C (deficitShape (1-36*e))) := by
    rw [hselect]
    calc
      _ = C e*((6:PrincipalQuadratic e)^16*
        (star w*(star w-1)^15-w*(w-1)^15)) := by ring
      _ = _ := by rw [hdifference]
  have hi := congrArg QuadraticAlgebra.im hscaled
  dsimp only [C,D,w] at hi
  norm_num [QuadraticAlgebra.im_mul] at hi
  change F.re=_
  linear_combination hi / (2*(6:ℂ)^16)

def principalReducedSurplus (e : ℝ) : ℝ :=
  (73728*(12:ℝ)^18/(6:ℝ)^15)*e*deficitShape (1-36*e)

def principalReducedSurplusPolynomial : Polynomial ℝ :=
  Polynomial.C (73728*(12:ℝ)^18/(6:ℝ)^15/36)*
    principalSurplusPolynomial.comp (Polynomial.C 36*Polynomial.X)

theorem principalReducedSurplusPolynomial_eval (e : ℝ) :
    principalReducedSurplusPolynomial.eval e=principalReducedSurplus e := by
  simp only [principalReducedSurplusPolynomial,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_comp,Polynomial.eval_X]
  rw [principalSurplusPolynomial_eval]
  unfold principalSurplusShape principalReducedSurplus
  ring

theorem principalReducedSurplus_pos {e : ℝ} (he : 0<e) (he1 : e≤1/36) :
    0<principalReducedSurplus e := by
  have hp := deficitShape_pos (show 0≤1-36*e by linarith)
  unfold principalReducedSurplus
  positivity

theorem principalReducedSurplusPolynomial_coeff_six :
    principalReducedSurplusPolynomial.coeff 6= -(8192/3)*189994*(12:ℝ)^18 := by
  rw [principalReducedSurplusPolynomial,Polynomial.coeff_C_mul,
    Polynomial.comp_C_mul_X_coeff,principalSurplusPolynomial_coeff_six]
  norm_num

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
