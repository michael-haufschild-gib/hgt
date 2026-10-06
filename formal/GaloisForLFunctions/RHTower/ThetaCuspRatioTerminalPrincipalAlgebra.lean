import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalKineticJets
import Mathlib.Algebra.Polynomial.Coeff

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def hankel {R : Type*} [CommRing R] (a b c d e : R) : R :=
  a*c*e-a*d^2-b^2*e+2*b*c*d-c^3

def direction {R : Type*} [CommRing R] (F N : Fin 5 → R) : R :=
  N 0*F 2*F 4+F 0*N 2*F 4+F 0*F 2*N 4-
    N 0*(F 3)^2-2*F 0*F 3*N 3-2*F 1*N 1*F 4-(F 1)^2*N 4+
    2*(N 1*F 2*F 3+F 1*N 2*F 3+F 1*F 2*N 3)-3*(F 2)^2*N 2

def leadingRows {R : Type*} [CommRing R] (A B T : R) : Fin 5 → R :=
  ![A+B,A*T^2,A*T^4,A*T^6,A*T^8]

def nextRows {R : Type*} [CommRing R] (C D E T : R) : Fin 5 → R :=
  ![9*C+D,23*C*T^2+E,45*C*T^4,75*C*T^6,113*C*T^8]

-- The exceptional second moment remains in B. Both next exceptional moments
-- are retained in D and E; neither contributes to the kernel pairing.
theorem leading_determinant {R : Type*} [CommRing R] (A B T : R) :
    hankel (leadingRows A B T 0) (leadingRows A B T 1)
      (leadingRows A B T 2) (leadingRows A B T 3) (leadingRows A B T 4)=0 := by
  simp [hankel,leadingRows]
  ring

theorem principal_direction {R : Type*} [CommRing R] (A B C D E T : R) :
    direction (leadingRows A B T) (nextRows C D E T)=8*A*B*C*T^12 := by
  simp [direction,leadingRows,nextRows]
  ring

theorem principal_direction_source (Y T D E : ℂ) :
    direction (leadingRows (-12*Y*(T+Y)*T) (8*Y^2*T) T)
      (nextRows (-6*Y*(T+Y)) D E T)=4608*Y^4*(T+Y)^2*T^14 := by
  rw [principal_direction]
  ring

def principalMinor : Poly := -(4608:Poly)*12^18*y^4*(t+y)^2*t^14
def principalSlope : Poly := (221184:Poly)*12^18*y^5*(t+y)^2*t^15

-- Algebraic response of the displayed polynomials; this does not assert
-- their identification with homogeneous components of the native source.
theorem principal_slope_response :
    24*y^2*(t+y)*pderiv Coord.K principalMinor-
      144*y*(t+y)*principalMinor=principalSlope := by
  simp [principalMinor,principalSlope,y,t,pderiv_X]
  ring

def deficitCoeff (j : ℕ) : ℕ :=
  (15:ℕ).choose (2*j+1)*7^(14-2*j)+(15:ℕ).choose (2*j)*7^(15-2*j)

def deficitShape {R : Type*} [CommRing R] (d : R) : R :=
  ∑ j ∈ Finset.range 8,(deficitCoeff j:R)*d^j

-- Positive coordinates for this principal model, despite its negative
-- ordinary sixth power coefficient.
theorem principal_odd_part {R : Type*} [CommRing R] (d : R) :
    (1+d)*(7+d)^15-(1-d)*(7-d)^15=2*d*deficitShape (d^2) := by
  norm_num [deficitShape,deficitCoeff,Finset.sum_range_succ,Nat.choose]
  ring

theorem deficitShape_pos {d : ℝ} (hd : 0≤d) : 0<deficitShape d := by
  have hn (j : ℕ) (_hj : j ∈ Finset.range 8) : 0≤(deficitCoeff j:ℝ)*d^j := by
    positivity
  have h := Finset.single_le_sum hn (show 0 ∈ Finset.range 8 by decide)
  have hc : 0<(deficitCoeff 0:ℝ)*d^0 := by
    norm_num [deficitCoeff]
  exact lt_of_lt_of_le hc h

def principalSurplusShape (e : ℝ) : ℝ := e*deficitShape (1-e)

theorem principalSurplusShape_pos {e : ℝ} (he : 0<e) (he1 : e≤1) :
    0<principalSurplusShape e := by
  exact mul_pos he (deficitShape_pos (by linarith))

-- Exact negative sixth coefficient of the same positive interval polynomial.
def principalSurplusPolynomial : Polynomial ℝ :=
  Polynomial.X*∑ j ∈ Finset.range 8,
    Polynomial.C (deficitCoeff j:ℝ)*(1-Polynomial.X)^j

theorem principalSurplusPolynomial_eval (e : ℝ) :
    principalSurplusPolynomial.eval e=principalSurplusShape e := by
  simp [principalSurplusPolynomial,principalSurplusShape,deficitShape,
    Polynomial.eval_finsetSum]

theorem principalSurplusPolynomial_coeff_six :
    principalSurplusPolynomial.coeff 6= -54718272 := by
  unfold principalSurplusPolynomial
  rw [show 6=5+1 by rfl,Polynomial.coeff_X_mul]
  have hpow (j : ℕ) : (1-Polynomial.X:Polynomial ℝ)^j=
      Polynomial.C ((-1:ℝ)^j)*(Polynomial.X+Polynomial.C (-1))^j := by
    have he : (1-Polynomial.X:Polynomial ℝ)=
        Polynomial.C (-1)*(Polynomial.X+Polynomial.C (-1)) := by simp; ring
    rw [he,mul_pow]
    simp
  simp_rw [hpow]
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  norm_num [deficitCoeff,Finset.sum_range_succ,Nat.choose]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
