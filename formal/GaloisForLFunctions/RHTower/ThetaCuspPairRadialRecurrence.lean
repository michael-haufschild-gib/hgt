import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomScalePolynomials

/-!
# Exact fixed-product radial recurrence for theta atom pairs

Along a reflected ordered pair, the scale product `a=p*r` is constant and the
scale sum `w=p*exp(2*t)+r*exp(-2*t)` satisfies `w''=4*w` and
`(w')^(2 : ℕ)=4*(w^(2 : ℕ)-4*a)`. The literal theta source product is
`4*a*exp(x-w)*(4*a+9-6*w)`.

Conjugating two derivatives by `exp(-w)` gives the polynomial operator
`S_a P = -4*((w^(2 : ℕ)-4*a)*(P''-2*P'+P)+w*(P'-P))`.
Its iterates generate every even reflection derivative of the original atom
pair. The source identification retains the actual squared frequencies and both
atom indices. This supplies the higher moment polynomials for the finite affine
sign problem; no sign of that full quadratic form is assumed or concluded here.
-/

namespace RHTower
noncomputable section
open Polynomial
set_option maxHeartbeats 2000000

private def radialSum (p r t : ℝ) := p*Real.exp (2*t)+r*Real.exp (-2*t)
private def radialDifference (p r t : ℝ) := p*Real.exp (2*t)-r*Real.exp (-2*t)

def thetaPairRadialProfile (p r : ℝ) (P : ℝ[X]) (t : ℝ) : ℝ :=
  Real.exp (-radialSum p r t)*P.eval (radialSum p r t)

/-- The exact operator for one signed even reflection-derivative step. -/
def thetaPairRadialEvenStep (a : ℝ) (P : ℝ[X]) : ℝ[X] :=
  -(C 4*((X^(2 : ℕ)-C (4*a))*(P.derivative.derivative-C 2*P.derivative+P)+
    X*(P.derivative-P)))

private theorem radialSum_deriv (p r t : ℝ) :
    HasDerivAt (radialSum p r) (2*radialDifference p r t) t := by
  unfold radialSum radialDifference
  have hp := (((Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)).const_mul p)
  have hr := (((Real.hasDerivAt_exp (-2*t)).comp t ((hasDerivAt_id t).const_mul (-2))).const_mul r)
  exact (hp.add hr).congr_deriv (by ring)

private theorem radialDifference_deriv (p r t : ℝ) :
    HasDerivAt (radialDifference p r) (2*radialSum p r t) t := by
  unfold radialSum radialDifference
  have hp := (((Real.hasDerivAt_exp (2*t)).comp t ((hasDerivAt_id t).const_mul 2)).const_mul p)
  have hr := (((Real.hasDerivAt_exp (-2*t)).comp t ((hasDerivAt_id t).const_mul (-2))).const_mul r)
  exact (hp.sub hr).congr_deriv (by ring)

private theorem radial_invariant (p r t : ℝ) :
    radialDifference p r t^(2 : ℕ) = radialSum p r t^(2 : ℕ)-4*(p*r) := by
  have he : Real.exp (2*t)*Real.exp (-2*t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    radialDifference p r t^(2 : ℕ) = radialSum p r t^(2 : ℕ)-
        4*(p*r)*(Real.exp (2*t)*Real.exp (-2*t)) := by
      unfold radialDifference radialSum
      ring
    _ = radialSum p r t^(2 : ℕ)-4*(p*r) := by rw [he]; ring

private theorem radialProfile_deriv (p r : ℝ) (P : ℝ[X]) (t : ℝ) :
    HasDerivAt (thetaPairRadialProfile p r P)
      (2*radialDifference p r t*thetaPairRadialProfile p r (P.derivative-P) t) t := by
  have hw := radialSum_deriv p r t
  have hg := hw.neg.exp
  have hP := (P.hasDerivAt (radialSum p r t)).comp t hw
  exact (hg.mul hP).congr_deriv (by
    simp only [thetaPairRadialProfile,eval_sub,Function.comp_apply,Pi.neg_apply]
    ring)

/-- The fixed-product scalar operator gives the literal profile's second derivative. -/
theorem thetaPairRadialProfile_second (p r : ℝ) (P : ℝ[X]) :
    deriv (deriv (thetaPairRadialProfile p r P)) =
      fun t => -thetaPairRadialProfile p r (thetaPairRadialEvenStep (p*r) P) t := by
  have hf : deriv (thetaPairRadialProfile p r P) = fun t =>
      2*radialDifference p r t*thetaPairRadialProfile p r (P.derivative-P) t :=
    funext fun t => (radialProfile_deriv p r P t).deriv
  rw [hf]
  funext t
  have hd := ((radialDifference_deriv p r t).const_mul 2).mul
    (radialProfile_deriv p r (P.derivative-P) t)
  change deriv ((fun y => 2*radialDifference p r y)*
    thetaPairRadialProfile p r (P.derivative-P)) t = _
  rw [hd.deriv]
  simp only [thetaPairRadialProfile,thetaPairRadialEvenStep,eval_neg,eval_mul,
    eval_C,eval_add,eval_sub,eval_pow,eval_X,derivative_sub]
  ring_nf
  simp_rw [radial_invariant]
  ring

/-- Finite source polynomials at every even reflection order. -/
def thetaPairRadialEvenPolynomial (a : ℝ) : ℕ → ℝ[X]
  | 0 => C (4*a+9)-C 6*X
  | k+1 => thetaPairRadialEvenStep a (thetaPairRadialEvenPolynomial a k)

/-- All even profile derivatives follow the exact fixed-product recurrence. -/
theorem thetaPairRadialProfile_even (p r : ℝ) (k : ℕ) :
    iteratedDeriv (2*k)
        (thetaPairRadialProfile p r (thetaPairRadialEvenPolynomial (p*r) 0)) =
      fun t => (-1 : ℝ)^k*
        thetaPairRadialProfile p r (thetaPairRadialEvenPolynomial (p*r) k) t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1) = (2*k+1)+1 by omega,iteratedDeriv_succ,iteratedDeriv_succ,ih]
    simp only [deriv_const_mul_field',thetaPairRadialProfile_second,
      thetaPairRadialEvenPolynomial,pow_succ]
    funext t
    ring

private theorem sourceTerm_radial_zero (n : ℕ) (y : ℝ) :
    thetaCuspSourceTerm y n =
      Real.exp (y/2-thetaCuspSingleAtomReflectionScale n y)*
        (4*thetaCuspSingleAtomReflectionScale n y^(2 : ℕ)-
          6*thetaCuspSingleAtomReflectionScale n y) := by
  simpa only [iteratedDeriv_zero,thetaCuspFirstAtomJetPolynomial,
    eval_sub,eval_mul,eval_C,eval_pow,eval_X] using
    iteratedDeriv_thetaCuspAtom_eq_scale_polynomial n 0 y

private theorem sourceScale_add (n : ℕ) (x t : ℝ) :
    thetaCuspSingleAtomReflectionScale n (x+t) =
      thetaCuspSingleAtomReflectionScale n x*Real.exp (2*t) := by
  unfold thetaCuspSingleAtomReflectionScale
  rw [show 2*(x+t) = 2*x+2*t by ring,Real.exp_add]
  ring

private theorem sourceScale_sub (n : ℕ) (x t : ℝ) :
    thetaCuspSingleAtomReflectionScale n (x-t) =
      thetaCuspSingleAtomReflectionScale n x*Real.exp (-2*t) := by
  unfold thetaCuspSingleAtomReflectionScale
  rw [show 2*(x-t) = 2*x+(-2*t) by ring,Real.exp_add]
  ring

/-- The literal ordered theta pair is the seeded fixed-product radial profile. -/
theorem thetaCuspAtomPair_eq_radialProfile (n m : ℕ) (x : ℝ) :
    (fun t => thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) m) =
      fun t => 4*(thetaCuspSingleAtomReflectionScale n x*
        thetaCuspSingleAtomReflectionScale m x)*Real.exp x*
          thetaPairRadialProfile (thetaCuspSingleAtomReflectionScale n x)
            (thetaCuspSingleAtomReflectionScale m x)
            (thetaPairRadialEvenPolynomial
              (thetaCuspSingleAtomReflectionScale n x*
                thetaCuspSingleAtomReflectionScale m x) 0) t := by
  funext t
  rw [sourceTerm_radial_zero,sourceTerm_radial_zero,sourceScale_add,sourceScale_sub]
  let p := thetaCuspSingleAtomReflectionScale n x
  let r := thetaCuspSingleAtomReflectionScale m x
  have hpr : (p*Real.exp (2*t))*(r*Real.exp (-2*t)) = p*r := by
    have he : Real.exp (2*t)*Real.exp (-2*t) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1
      ring
    calc
      _ = p*r*(Real.exp (2*t)*Real.exp (-2*t)) := by ring
      _ = p*r := by rw [he]; ring
  have hseed :
      (4*(p*Real.exp (2*t))^(2 : ℕ)-6*(p*Real.exp (2*t)))*
        (4*(r*Real.exp (-2*t))^(2 : ℕ)-6*(r*Real.exp (-2*t))) =
      4*(p*r)*(4*(p*r)+9-6*(p*Real.exp (2*t)+r*Real.exp (-2*t))) := by
    calc
      _ = 4*((p*Real.exp (2*t))*(r*Real.exp (-2*t)))*
        (4*((p*Real.exp (2*t))*(r*Real.exp (-2*t)))+9-
          6*(p*Real.exp (2*t)+r*Real.exp (-2*t))) := by ring
      _ = _ := by rw [hpr]
  have he : Real.exp ((x+t)/2-p*Real.exp (2*t))*
      Real.exp ((x-t)/2-r*Real.exp (-2*t)) =
      Real.exp x*Real.exp (-(p*Real.exp (2*t)+r*Real.exp (-2*t))) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  change Real.exp ((x+t)/2-p*Real.exp (2*t))*
      (4*(p*Real.exp (2*t))^(2 : ℕ)-6*(p*Real.exp (2*t)))*
      (Real.exp ((x-t)/2-r*Real.exp (-2*t))*
        (4*(r*Real.exp (-2*t))^(2 : ℕ)-6*(r*Real.exp (-2*t)))) = _
  rw [show Real.exp ((x+t)/2-p*Real.exp (2*t))*
      (4*(p*Real.exp (2*t))^(2 : ℕ)-6*(p*Real.exp (2*t)))*
      (Real.exp ((x-t)/2-r*Real.exp (-2*t))*
        (4*(r*Real.exp (-2*t))^(2 : ℕ)-6*(r*Real.exp (-2*t)))) =
      (Real.exp ((x+t)/2-p*Real.exp (2*t))*
        Real.exp ((x-t)/2-r*Real.exp (-2*t)))*
      ((4*(p*Real.exp (2*t))^(2 : ℕ)-6*(p*Real.exp (2*t)))*
        (4*(r*Real.exp (-2*t))^(2 : ℕ)-6*(r*Real.exp (-2*t)))) by ring]
  rw [he,hseed]
  simp only [thetaPairRadialProfile,thetaPairRadialEvenPolynomial,radialSum,
    eval_sub,eval_mul,eval_C,eval_X]
  change _ = 4*(p*r)*Real.exp x*_
  ring

/-- Every literal even theta-pair reflection derivative is generated by the scalar radial operator. -/
theorem thetaCuspAtomPairEvenJet_eq_radial (n m k : ℕ) (x : ℝ) :
    iteratedDeriv (2*k)
      (fun t => thetaCuspSourceTerm (x+t) n*thetaCuspSourceTerm (x-t) m) 0 =
      (-1 : ℝ)^k*4*(thetaCuspSingleAtomReflectionScale n x*
        thetaCuspSingleAtomReflectionScale m x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale n x-
          thetaCuspSingleAtomReflectionScale m x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale n x*
            thetaCuspSingleAtomReflectionScale m x) k).eval
          (thetaCuspSingleAtomReflectionScale n x+
            thetaCuspSingleAtomReflectionScale m x) := by
  rw [thetaCuspAtomPair_eq_radialProfile,iteratedDeriv_const_mul_field,
    thetaPairRadialProfile_even]
  simp only [thetaPairRadialProfile,radialSum,mul_zero,Real.exp_zero,mul_one]
  have he : Real.exp x*Real.exp (-(thetaCuspSingleAtomReflectionScale n x+
      thetaCuspSingleAtomReflectionScale m x)) =
      Real.exp (x-thetaCuspSingleAtomReflectionScale n x-
        thetaCuspSingleAtomReflectionScale m x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

end
end RHTower
