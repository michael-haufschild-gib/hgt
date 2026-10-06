import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalHomogeneousReflections

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open MvPolynomial

theorem liftT_pderiv_y (P : Polynomial ℂ) : pderiv Coord.K (liftT P)=0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,hP,hQ,add_zero]
  | monomial n c =>
    rw [←Polynomial.C_mul_X_pow_eq_monomial]
    simp [t]

theorem reflection_pderiv_y {n : ℕ} (he : Even n) (hn : 0<n) :
    pderiv Coord.K (reflection n)=
      2*y*liftT (amplitudeSelf n)-6*liftT (amplitudeCross n) := by
  rw [reflection_affine he hn]
  simp [liftT_pderiv_y,y]
  ring

theorem reflection_pderiv_t {n : ℕ} (he : Even n) (hn : 0<n) :
    pderiv Coord.J (reflection n)=
      y^2*liftT (amplitudeSelf n).derivative-6*y*liftT (amplitudeCross n).derivative := by
  rw [reflection_affine he hn]
  simp [←liftT_derivative,y]

def reflectionYHomogeneous (n : ℕ) (Y T : ℂ) : Polynomial ℂ :=
  Polynomial.C (2*Y)*homogenizeAt (n-1) (amplitudeSelf n) T-
    Polynomial.C 6*homogenizeAt n (amplitudeCross n) T

def reflectionTHomogeneous (n : ℕ) (Y T : ℂ) : Polynomial ℂ :=
  Polynomial.C (Y^2)*homogenizeAt (n-2) (amplitudeSelf n).derivative T-
    Polynomial.C (6*Y)*homogenizeAt (n-1) (amplitudeCross n).derivative T

theorem reflectionYHomogeneous_eval {n : ℕ} (he : Even n) (hn : 2≤n)
    (Y T h : ℂ) (hh : h≠0) :
    (reflectionYHomogeneous n Y T).eval h=
      h^n*eval (terminalPoint (Y/h) (T/h)) (pderiv Coord.K (reflection n)) := by
  simp only [reflectionYHomogeneous,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  rw [homogenizeAt_eval _ _ _ _ (amplitudeSelf_degree (by omega)) hh,
    homogenizeAt_eval _ _ _ _ (amplitudeCross_degree n) hh,reflection_pderiv_y he (by omega)]
  simp only [map_sub,map_mul,map_ofNat,eval_liftT,y,eval_X,terminalPoint]
  have hp : h^n=h^(n-1)*h := by rw [←pow_succ]; congr 1; omega
  rw [hp]
  field_simp [hh]

theorem reflectionTHomogeneous_eval {n : ℕ} (he : Even n) (hn : 2≤n)
    (Y T h : ℂ) (hh : h≠0) :
    (reflectionTHomogeneous n Y T).eval h=
      h^n*eval (terminalPoint (Y/h) (T/h)) (pderiv Coord.J (reflection n)) := by
  have hH : (amplitudeSelf n).derivative.natDegree≤n-2 := by
    have := (Polynomial.natDegree_derivative_le (amplitudeSelf n)).trans
      (Nat.sub_le_sub_right (amplitudeSelf_degree (show 0<n by omega)) 1)
    simpa only [Nat.sub_sub] using this
  have hK := (Polynomial.natDegree_derivative_le (amplitudeCross n)).trans
    (Nat.sub_le_sub_right (amplitudeCross_degree n) 1)
  simp only [reflectionTHomogeneous,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
  rw [homogenizeAt_eval _ _ _ _ hH hh,homogenizeAt_eval _ _ _ _ hK hh,
    reflection_pderiv_t he (by omega)]
  simp only [map_sub,map_mul,map_pow,map_ofNat,eval_liftT,y,eval_X,terminalPoint]
  have hp : h^n=h^(n-2)*h^2 := by rw [←pow_add]; congr 1; omega
  have hp1 : h^(n-1)=h^(n-2)*h := by rw [←pow_succ]; congr 1; omega
  rw [hp,hp1]
  field_simp [hh]

theorem reflectionYHomogeneous_zero {n : ℕ} (he : Even n) (hn : 2≤n) (Y T : ℂ) :
    (reflectionYHomogeneous n Y T).coeff 0=
      -12*(T+2*Y)*T^(n-1)+(if n=2 then 16*Y*T else 0) := by
  rw [reflectionYHomogeneous,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
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

theorem reflectionYHomogeneous_one {n : ℕ} (he : Even n) (hn : 2≤n) (Y T : ℂ) :
    (reflectionYHomogeneous n Y T).coeff 1=
      -6*(T+2*Y)*T^(n-2)*((n:ℂ)*((n:ℂ)+1)+3)+
        (if n=2 then 48*Y else 0)+(if n=4 then 96*Y*T^2 else 0) := by
  have hK : (amplitudeCross n).coeff (n-1)=(n:ℂ)*((n:ℂ)+1)+3 := by
    simpa only [Nat.sub_add_cancel (show 1≤n by omega)] using amplitudeCross_next (n-1)
  rw [reflectionYHomogeneous,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
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

theorem reflectionTHomogeneous_zero {n : ℕ} (he : Even n) (hn : 2≤n) (Y T : ℂ) :
    (reflectionTHomogeneous n Y T).coeff 0=
      Y^2*(-12+(if n=2 then 8 else 0))*((n:ℂ)-1)*T^(n-2)-
        12*Y*(n:ℂ)*T^(n-1) := by
  rw [reflectionTHomogeneous,Polynomial.coeff_sub,Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul,homogenizeAt_coeff _ _ _ _ (by omega),
    homogenizeAt_coeff _ _ _ _ (by omega)]
  simp only [Nat.sub_zero,Polynomial.coeff_derivative]
  rw [show n-2+1=n-1 by omega,show n-1+1=n by omega,
    amplitudeSelf_next_even he hn,amplitudeCross_top,Nat.cast_sub (show 1≤n by omega)]
  simp only [Nat.cast_one,Nat.cast_sub hn,Nat.cast_ofNat]
  ring

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
