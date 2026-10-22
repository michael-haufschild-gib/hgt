import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalAffineJets
import Mathlib.Algebra.Polynomial.Derivative

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def amplitudePoly : ℕ → Polynomial ℂ
  | 0 => 2
  | n+1 => Polynomial.X*(amplitudePoly n).derivative+
      (Polynomial.X+Polynomial.C (9/4:ℂ))*amplitudePoly n+
      Polynomial.C (3*(5/4:ℂ)^n)

def liftT : Polynomial ℂ →+* Poly := Polynomial.eval₂RingHom C t

@[simp] theorem liftT_C (c : ℂ) : liftT (Polynomial.C c)=C c := by simp [liftT]
@[simp] theorem liftT_X : liftT Polynomial.X=t := by simp [liftT]

theorem liftT_derivative (P : Polynomial ℂ) :
    liftT P.derivative=pderiv Coord.J (liftT P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | monomial n c =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial,Polynomial.derivative_C_mul_X_pow]
    simp only [map_mul,map_pow,liftT_C,liftT_X,pderiv_C_mul,pderiv_pow]
    simp [t,map_natCast]
    ring

theorem liftT_amplitudePoly (n : ℕ) : liftT (amplitudePoly n)=amplitude n := by
  induction n with
  | zero => simp [amplitudePoly,amplitude,map_ofNat]
  | succ n ih =>
    simp only [amplitudePoly,map_add,map_mul,liftT_X,liftT_C,liftT_derivative,ih,
      amplitude]

theorem amplitudePoly_coeff_succ (n j : ℕ) :
    (amplitudePoly (n+1)).coeff (j+1)=
      ((j:ℂ)+13/4)*(amplitudePoly n).coeff (j+1)+(amplitudePoly n).coeff j := by
  simp only [amplitudePoly,add_mul,Polynomial.coeff_add,Polynomial.coeff_X_mul,
    Polynomial.coeff_derivative,Polynomial.coeff_C_mul,Polynomial.coeff_C,
    Nat.add_one_ne_zero,if_false]
  ring

theorem amplitudePoly_coeff_above (n j : ℕ) (hj : n<j) :
    (amplitudePoly n).coeff j=0 := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => omega
    | succ j => simp [amplitudePoly]
  | succ n ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [amplitudePoly_coeff_succ,ih (j+1) (by omega),ih j (by omega)]
      ring

theorem amplitudePoly_coeff_top (n : ℕ) : (amplitudePoly n).coeff n=2 := by
  induction n with
  | zero => simp [amplitudePoly]
  | succ n ih =>
    rw [amplitudePoly_coeff_succ,amplitudePoly_coeff_above n (n+1) (by omega),ih]
    ring

def amplitudeNext (n : ℕ) : ℂ := (n:ℂ)^2+(7/2)*(n:ℂ)+3
def amplitudeThird (n : ℕ) : ℂ :=
  (n:ℂ)*((n:ℂ)-1)*((n:ℂ)-2)*((n:ℂ)-3)/4+
    (31/12)*(n:ℂ)*((n:ℂ)-1)*((n:ℂ)-2)+
    (105/16)*(n:ℂ)*((n:ℂ)-1)+(15/4)*(n:ℂ)

-- The next two formulas begin after their genuine seed exceptions.
theorem amplitudePoly_coeff_next (n : ℕ) :
    (amplitudePoly (n+1)).coeff n=amplitudeNext (n+1) := by
  induction n with
  | zero => norm_num [amplitudePoly,amplitudeNext]
  | succ n ih =>
    rw [amplitudePoly_coeff_succ,amplitudePoly_coeff_top,ih]
    unfold amplitudeNext
    push_cast
    ring

theorem amplitudePoly_coeff_third (n : ℕ) :
    (amplitudePoly (n+2)).coeff n=amplitudeThird (n+2) := by
  induction n with
  | zero => norm_num [amplitudePoly,amplitudeThird,add_mul]
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,amplitudePoly_coeff_succ]
    rw [show n+2=(n+1)+1 by omega,amplitudePoly_coeff_next]
    rw [show n+1+1=n+2 by omega,ih]
    unfold amplitudeNext amplitudeThird
    push_cast
    ring

theorem native_jet_amplitudePoly (n : ℕ) :
    pull (integerJet n)=C ((12:ℂ)^n)*
      (y*liftT (amplitudePoly n)-C (3*(5/4:ℂ)^n)) := by
  rw [liftT_amplitudePoly,native_jet_affine]

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
