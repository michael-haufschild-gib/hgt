import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalActualCoefficient

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
set_option autoImplicit false
open Polynomial ThetaRatioInfinity

def absorbedDeficitShape {R : Type*} [CommRing R] (t : R) : R :=
  t*deficitShape (1-t)-(deficitCoeff 7:R)*t^7*(1-t)

theorem absorbedDeficitShape_split {R : Type*} [CommRing R] (t : R) :
    absorbedDeficitShape t=t*((deficitCoeff 0:R)+
      ((deficitCoeff 1:R)-(deficitCoeff 7:R))*(1-t)+
      (∑ j ∈ Finset.range 6,(deficitCoeff (j+2):R)*(1-t)^(j+2))+
      (deficitCoeff 7:R)*(1-t)^2*(∑ j ∈ Finset.range 6,t^j)) := by
  norm_num [absorbedDeficitShape,deficitShape,Finset.sum_range_succ]
  ring

theorem absorbedDeficitShape_pos {t : ℝ} (ht : 0<t) (ht1 : t≤1) :
    0<absorbedDeficitShape t := by
  rw [absorbedDeficitShape_split]
  have hD : 0≤1-t := sub_nonneg.mpr ht1
  have hd0 : 0<(deficitCoeff 0:ℝ) := by norm_num [deficitCoeff,Nat.choose]
  have hd17 : 0≤(deficitCoeff 1:ℝ)-(deficitCoeff 7:ℝ) := by
    norm_num [deficitCoeff,Nat.choose]
  have hs : 0≤∑ j ∈ Finset.range 6,(deficitCoeff (j+2):ℝ)*(1-t)^(j+2) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _)
  have hg : 0≤∑ j ∈ Finset.range 6,t^j :=
    Finset.sum_nonneg fun j _ => pow_nonneg ht.le j
  have hm : 0≤(deficitCoeff 7:ℝ)*(1-t)^2*(∑ j ∈ Finset.range 6,t^j) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hg
  exact mul_pos ht (add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hd0 (mul_nonneg hd17 hD)) hs) hm)

theorem principalSurplusPolynomial_coeff_eight :
    principalSurplusPolynomial.coeff 8= -(deficitCoeff 7:ℝ) := by
  unfold principalSurplusPolynomial
  rw [show 8=7+1 by rfl,Polynomial.coeff_X_mul]
  have hpow (j : ℕ) : (1-Polynomial.X:Polynomial ℝ)^j=
      Polynomial.C ((-1:ℝ)^j)*(Polynomial.X+Polynomial.C (-1))^j := by
    have he : (1-Polynomial.X:Polynomial ℝ)=
        Polynomial.C (-1)*(Polynomial.X+Polynomial.C (-1)) := by simp; ring
    rw [he,mul_pow]
    simp
  simp_rw [hpow]
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  norm_num [Finset.sum_range_succ,Nat.choose]

theorem principalReducedSurplusPolynomial_coeff_eight :
    principalReducedSurplusPolynomial.coeff 8=
      -(73728*(12:ℝ)^18/(6:ℝ)^15/36)*(deficitCoeff 7:ℝ)*36^8 := by
  rw [principalReducedSurplusPolynomial,coeff_C_mul,comp_C_mul_X_coeff,
    principalSurplusPolynomial_coeff_eight]
  ring

theorem principalAbsorbedSurplus_eval (e : ℝ) :
    (absorbEighth principalReducedSurplusPolynomial (1/36)).eval e=
      (73728*(12:ℝ)^18/(6:ℝ)^15/36)*absorbedDeficitShape (36*e) := by
  simp only [absorbEighth,eval_add,eval_sub,eval_mul,eval_C,eval_pow,eval_X]
  rw [principalReducedSurplusPolynomial_eval,principalReducedSurplusPolynomial_coeff_eight]
  unfold principalReducedSurplus absorbedDeficitShape
  ring

theorem principalAbsorbedSurplus_pos {e : ℝ} (he : 0<e) (he1 : e≤1/36) :
    0<(absorbEighth principalReducedSurplusPolynomial (1/36)).eval e := by
  rw [principalAbsorbedSurplus_eval]
  exact mul_pos (by positivity) (absorbedDeficitShape_pos (by linarith) (by linarith))

theorem map_absorbEighth {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : Polynomial R) (M : R) :
    (absorbEighth P M).map f=absorbEighth (P.map f) (f M) := by
  simp [absorbEighth,Polynomial.coeff_map]

def gradedAbsorbedFamily (z : ℂ) : TerminalFamily :=
  absorbEighth (Bivariate.swap (gradedReducedRead z)) (C (1/36)*(1-X)^2)

def gradedAbsorbedPrincipal (z : ℂ) : Polynomial ℂ :=
  (gradedAbsorbedFamily z).map (evalRingHom (0:ℂ))

theorem gradedReducedRead_swap_zero (z : ℂ) :
    (Bivariate.swap (gradedReducedRead z)).map (evalRingHom (0:ℂ))=
      principalReducedSurplusPolynomial.map Complex.ofRealHom := by
  ext n
  rw [coeff_map]
  change (gradedSurplusSlice z n).eval 0=_
  rw [gradedSurplusSlice_zero,gradedReducedRead_zero]

theorem gradedAbsorbedPrincipal_eq (z : ℂ) :
    gradedAbsorbedPrincipal z=
      (absorbEighth principalReducedSurplusPolynomial (1/36)).map Complex.ofRealHom := by
  rw [gradedAbsorbedPrincipal,gradedAbsorbedFamily,map_absorbEighth,
    gradedReducedRead_swap_zero,map_absorbEighth]
  simp

theorem gradedAbsorbedPrincipal_pos (z : ℂ) {e : ℝ} (he : 0<e) (he1 : e≤1/36) :
    0<((gradedAbsorbedPrincipal z).eval (e:ℂ)).re := by
  rw [gradedAbsorbedPrincipal_eq]
  change 0<((absorbEighth principalReducedSurplusPolynomial (1/36)).map Complex.ofRealHom |>.eval
    (Complex.ofRealHom e)).re
  rw [eval_map_apply,Complex.ofRealHom_eq_coe,Complex.ofReal_re]
  exact principalAbsorbedSurplus_pos he he1

theorem gradedAbsorbedPrincipal_coeff_six (z : ℂ) :
    (gradedAbsorbedPrincipal z).coeff 6= -(8192/3)*189994*(12:ℂ)^18 := by
  rw [gradedAbsorbedPrincipal_eq,coeff_map,absorbEighth_coeff_six,
    principalReducedSurplusPolynomial_coeff_six]
  norm_num

theorem terminalAbsorptionMass (h : ℂ) (hh : h≠0) :
    h^2*(9*(boundaryA 9 (inverseClockK h)+(boundaryB (inverseClockK h))^2/4))=
      (1-h)^2/36 := by
  unfold boundaryA boundaryMass boundaryB inverseClockK
  simp only [sub_self,mul_zero,zero_div,sub_zero]
  field_simp [hh]
  ring


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
