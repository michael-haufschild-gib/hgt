import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryMomentAlgebra
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryAsymptotic

/-! One frequency-independent rational weight for the complete physical source. -/
namespace RHTower.D4BMJointSource
open Complex Set
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def nonstationarySourceNumerator : ℂ[X] :=
  Polynomial.C 5*((2+3*Polynomial.X)^4*nonstationaryPolynomial 2 2)-
  Polynomial.C (5/2)*((2+3*Polynomial.X)^6*nonstationaryPolynomial 2 1)-
  Polynomial.C (3/2)*((2+3*Polynomial.X)^8*nonstationaryPolynomial 2 0)+
  Polynomial.C (15/2)*((2+3*Polynomial.X)^0*nonstationaryPolynomial 4 4)-
  Polynomial.C (81/4)*((2+3*Polynomial.X)^2*nonstationaryPolynomial 4 3)+
  Polynomial.C 15*((2+3*Polynomial.X)^4*nonstationaryPolynomial 4 2)-
  Polynomial.C (9/4)*((2+3*Polynomial.X)^6*nonstationaryPolynomial 4 1)

theorem nonstationaryIteratedMoment_unshift (n k : ℕ) (w : ℂ)
    (hw : -2 < w.re) (hw1 : w+1 ≠ 0) (hk : k ≤ n) :
    nonstationaryIteratedMoment n k w=(-1:ℂ)^k*(w+1)^k*nonstationaryIteratedMoment n 0 w := by
  have h := nonstationaryIteratedMoment_shift n k w hw hw1 hk
  have hs : (-1:ℂ)^k*(-1)^k=1 := by rw [← mul_pow]; simp
  calc
    _ = (-1:ℂ)^k*((-1:ℂ)^k*nonstationaryIteratedMoment n k w) := by rw [← mul_assoc,hs,one_mul]
    _ = (-1:ℂ)^k*((w+1)^k*nonstationaryIteratedMoment n 0 w) := by rw [h]
    _ = _ := by ring

private theorem lift_to_eight (n k : ℕ) (w : ℂ) (hk : k ≤ 4) :
    nonstationaryMoment ((2+3*Polynomial.X)^(8-2*k)*nonstationaryPolynomial n k) 8 w=
      nonstationaryIteratedMoment n k w := by
  have h := nonstationaryMoment_lift (nonstationaryPolynomial n k) (2*k) (8-2*k) w
  simpa only [show 2*k+(8-2*k)=8 by omega,nonstationaryIteratedMoment] using h

/-- Moving the frequency polynomials through the original finite part creates this fixed numerator. -/
theorem nonstationarySourceNumerator_moment (w : ℂ) (hw : -2 < w.re) (hw1 : w+1 ≠ 0) :
    nonstationaryMoment nonstationarySourceNumerator 8 w =
      (5*(w+1)^2+(5/2:ℂ)*(w+1)-3/2)*nonstationaryMoment ((1-Polynomial.X)^2) 0 w+
      ((15/2:ℂ)*(w+1)^4+(81/4:ℂ)*(w+1)^3+15*(w+1)^2+(9/4:ℂ)*(w+1))*
        nonstationaryMoment ((1-Polynomial.X)^4) 0 w := by
  simp only [nonstationarySourceNumerator,nonstationaryMoment_add,nonstationaryMoment_sub,
    nonstationaryMoment_C_mul,hw]
  rw [lift_to_eight 2 2 w (by omega),lift_to_eight 2 1 w (by omega),
    lift_to_eight 2 0 w (by omega),lift_to_eight 4 4 w (by omega),
    lift_to_eight 4 3 w (by omega),lift_to_eight 4 2 w (by omega),lift_to_eight 4 1 w (by omega)]
  rw [nonstationaryIteratedMoment_unshift 2 2 w hw hw1 (by omega),
    nonstationaryIteratedMoment_unshift 2 1 w hw hw1 (by omega),
    nonstationaryIteratedMoment_unshift 4 4 w hw hw1 (by omega),
    nonstationaryIteratedMoment_unshift 4 3 w hw hw1 (by omega),
    nonstationaryIteratedMoment_unshift 4 2 w hw hw1 (by omega),
    nonstationaryIteratedMoment_unshift 4 1 w hw hw1 (by omega)]
  simp only [nonstationaryIteratedMoment,nonstationaryPolynomial]
  ring

theorem nonstationarySourceNumerator_one : nonstationarySourceNumerator.eval 1=268750 := by
  have h20 := nonstationaryPolynomial_one_eq_zero 2 0 (by omega)
  have h21 := nonstationaryPolynomial_one_eq_zero 2 1 (by omega)
  have h41 := nonstationaryPolynomial_one_eq_zero 4 1 (by omega)
  have h42 := nonstationaryPolynomial_one_eq_zero 4 2 (by omega)
  have h43 := nonstationaryPolynomial_one_eq_zero 4 3 (by omega)
  norm_num [nonstationarySourceNumerator,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_pow,h20,h21,h41,h42,h43,nonstationaryPolynomial_second_leading,
    nonstationaryPolynomial_fourth_leading]

theorem nonstationarySourceNumerator_zero : nonstationarySourceNumerator.eval 0 = -384 := by
  have hz (n k : ℕ) : (nonstationaryPolynomial n (k+1)).eval 0=0 := nonstationaryWeightStep_zero _ _
  have h20 : (nonstationaryPolynomial 2 0).eval 0=1 := by norm_num [nonstationaryPolynomial]
  norm_num only [nonstationarySourceNumerator,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_X,h20,
    hz 2 0,hz 2 1,hz 4 0,hz 4 1,hz 4 2,hz 4 3]

theorem nonstationarySourceWeight_one : nonstationaryWeight nonstationarySourceNumerator 8 1/5=(86/625:ℂ) := by
  norm_num [nonstationaryWeight,nonstationarySourceNumerator_one]

end
end RHTower.D4BMJointSource
