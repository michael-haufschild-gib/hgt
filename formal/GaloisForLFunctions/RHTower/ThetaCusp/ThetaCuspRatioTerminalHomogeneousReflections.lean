import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalCrossHeads
import GaloisForLFunctions.QuantumAlg.Util.Polynomial.Basic

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

def homogenizeAt (d : ℕ) (P : Polynomial ℂ) (T : ℂ) : Polynomial ℂ :=
  (P.comp (Polynomial.C T*Polynomial.X)).reflect d

theorem homogenizeAt_coeff (d : ℕ) (P : Polynomial ℂ) (T : ℂ) (j : ℕ)
    (hj : j≤d) :
    (homogenizeAt d P T).coeff j=P.coeff (d-j)*T^(d-j) := by
  rw [homogenizeAt,Polynomial.coeff_reflect,Polynomial.revAt_le hj,
    Polynomial.comp_C_mul_X_coeff]

theorem homogenizeAt_eval (d : ℕ) (P : Polynomial ℂ) (T h : ℂ)
    (hP : P.natDegree≤d) (hh : h≠0) :
    (homogenizeAt d P T).eval h=h^d*P.eval (T/h) := by
  have hd : (P.comp (Polynomial.C T*Polynomial.X)).natDegree≤d := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hj),zero_mul]
  rw [homogenizeAt,QuantumAlg.eval_reflect hd hh]
  simp only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,div_eq_mul_inv]

def terminalPoint (Y T : ℂ) : Coord → ℂ
  | .U => 0
  | .K => Y
  | .J => T

theorem eval_liftT (v : Coord → ℂ) (P : Polynomial ℂ) :
    eval v (liftT P)=P.eval (v .J) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,Polynomial.eval_add,hP,hQ]
  | monomial n c =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp only [map_mul,map_pow,liftT_C,liftT_X,eval_C,t,eval_X,
      Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_X]

def reflectionHomogeneous (n : ℕ) (Y T : ℂ) : Polynomial ℂ :=
  Polynomial.C (Y^2)*homogenizeAt (n-1) (amplitudeSelf n) T-
    Polynomial.C (6*Y)*homogenizeAt n (amplitudeCross n) T

theorem reflectionHomogeneous_eval {n : ℕ} (he : Even n) (hn : 2≤n)
    (Y T h : ℂ) (hh : h≠0) :
    (reflectionHomogeneous n Y T).eval h=
      h^(n+1)*eval (terminalPoint (Y/h) (T/h)) (reflection n) := by
  simp only [reflectionHomogeneous,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  rw [homogenizeAt_eval _ _ _ _ (amplitudeSelf_degree (by omega)) hh,
    homogenizeAt_eval _ _ _ _ (amplitudeCross_degree n) hh,
    reflection_affine he (by omega)]
  simp only [map_sub,map_mul,map_pow,map_ofNat,eval_liftT,y,eval_X,terminalPoint]
  have hp : h^(n+1)=h^(n-1)*h^2 := by rw [←pow_add]; congr 1; omega
  have hp1 : h^n=h^(n-1)*h := by rw [←pow_succ]; congr 1; omega
  rw [hp,hp1]
  field_simp [hh]

theorem reflectionHomogeneous_zero {n : ℕ} (he : Even n) (hn : 2≤n) (Y T : ℂ) :
    (reflectionHomogeneous n Y T).coeff 0=
      -12*Y*(T+Y)*T^(n-1)+(if n=2 then 8*Y^2*T else 0) := by
  rw [reflectionHomogeneous,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul,homogenizeAt_coeff _ _ _ _ (by omega),
    homogenizeAt_coeff _ _ _ _ (by omega)]
  simp only [Nat.sub_zero,amplitudeSelf_next_even he hn,amplitudeCross_top]
  by_cases hn2 : n=2
  · subst n
    norm_num
    ring
  · simp only [if_neg hn2,add_zero]
    have hp : T^n=T^(n-1)*T := by rw [←pow_succ]; congr 1; omega
    rw [hp]
    ring

theorem reflectionHomogeneous_one {n : ℕ} (he : Even n) (hn : 2≤n) (Y T : ℂ) :
    (reflectionHomogeneous n Y T).coeff 1=
      -6*Y*(T+Y)*T^(n-2)*((n:ℂ)*((n:ℂ)+1)+3)+
        (if n=2 then 24*Y^2 else 0)+(if n=4 then 48*Y^2*T^2 else 0) := by
  have hK : (amplitudeCross n).coeff (n-1)=(n:ℂ)*((n:ℂ)+1)+3 := by
    simpa only [Nat.sub_add_cancel (show 1≤n by omega)] using amplitudeCross_next (n-1)
  rw [reflectionHomogeneous,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul,homogenizeAt_coeff _ _ _ _ (by omega),
    homogenizeAt_coeff _ _ _ _ (by omega)]
  rw [show n-1-1=n-2 by omega,amplitudeSelf_second_even he hn,hK]
  by_cases hn2 : n=2
  · subst n
    norm_num
    ring
  · by_cases hn4 : n=4
    · subst n
      norm_num
      ring
    · simp only [if_neg hn2,if_neg hn4,add_zero]
      have hp : T^(n-1)=T^(n-2)*T := by rw [←pow_succ]; congr 1; omega
      rw [hp]
      ring

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
