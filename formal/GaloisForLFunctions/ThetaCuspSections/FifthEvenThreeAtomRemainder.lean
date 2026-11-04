import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralBound

/-!
# Remaining pairs and the three-atom tail in fifth even coordinates

The common positive factor is `4q² exp(x-2q)`. After dividing the moment of
order `k` by `q^k`, the two remaining unequal pairs have weights `18 exp(-8q)`
and `72 exp(-11q)`. The reflected tail is expressed in the same Gaussian
coordinates. Shifted polynomial coefficients and stationary exponential bounds
give a total entry budget of `147/20000` on `q ≥ 5`; the infinite tail
contributes at most `1/10000`.
-/

noncomputable section
open Matrix _root_.RHTower _root_.RHTower.ThetaCuspThreeAtomCauchyTail
namespace GaloisForLFunctions.ThetaCuspSections.FifthRemainder
open FifthLeadingPair

/-- Common factor in the radial atom-pair formulas. -/
def sourceUnit (x : ℝ) : ℝ :=
  4*(thetaCuspSingleAtomReflectionScale 1 x)^2*
    Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)

/-- A normalized radial pair in Gaussian polynomial coordinates. -/
def pairGram (a b q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j =>
    (thetaPairRadialEvenPolynomial (a*q^2) (i.val+j.val)).eval (b*q)/q^(i.val+j.val))

/-- The unequal pairs involving the third atom. -/
def omittedPairGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (18*Real.exp (-8*q)) • pairGram 9 10 q+
    (72*Real.exp (-11*q)) • pairGram 36 13 q

/-- The signed reflected tail beyond the first three atoms, in the same coordinates. -/
def tailGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => (-1 : ℝ)^(i.val+j.val)*
    (thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspThreeAtomReflectionJet (2*(i.val+j.val)) x)/
        (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(i.val+j.val)))

/-- All remaining signed terms after retaining the leading pairs and pure atoms. -/
def remainderGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  omittedPairGram (thetaCuspSingleAtomReflectionScale 1 x)+tailGram x

open _root_.RHTower
private theorem exp_one_lower : (8/3 : ℝ) ≤ Real.exp 1 := by
  linarith only [Real.exp_one_gt_d9]
private theorem exp_three_lower : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith only [hp]
private theorem exp_neg_three_multiple (n : ℕ) {t : ℝ} (ht : (n : ℝ)*3 ≤ t) :
    Real.exp (-t) ≤ 1/(20 : ℝ)^n := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) exp_three_lower n
  rw [← Real.exp_nat_mul] at hp
  have hh := hp.trans (Real.exp_le_exp.mpr ht)
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) hh
/-- Stationary exponential bounds give a rational majorant for every shifted monomial. -/
theorem shifted_power_bound (n : ℕ) {c y : ℝ} (hc : 0 < c) (hy : 0 ≤ y) :
    y^n*Real.exp (-c*y) ≤ (3*(n : ℝ)/(8*c))^n := by
  by_cases hn : n=0
  · subst n
    simp only [pow_zero,one_mul]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hy)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp := _root_.RHTower.pow_mul_exp_neg_le_stationary_radius n
    (a := (n : ℝ)/c) (t := y) (div_pos hn0 hc) hy
  have heq : (n : ℝ)/((n : ℝ)/c)=c := by field_simp [hn0.ne', hc.ne']
  rw [heq] at hp
  have hi : Real.exp (-1 : ℝ) ≤ 3/8 := by
    rw [Real.exp_neg,inv_eq_one_div]
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8/3) exp_one_lower
    norm_num at hh
    simpa only [one_div] using hh
  have hin : Real.exp (-(n : ℝ)) ≤ (3/8 : ℝ)^n := by
    rw [show -(n : ℝ)=(n : ℝ)*(-1) by ring,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hi n
  calc
    _ ≤ ((n : ℝ)/c)^n*Real.exp (-(n : ℝ)) := by simpa only [neg_mul] using hp
    _ ≤ ((n : ℝ)/c)^n*(3/8 : ℝ)^n := mul_le_mul_of_nonneg_left hin (by positivity)
    _ = (3*(n : ℝ)/(8*c))^n := by
      rw [← mul_pow]
      congr 1
      ring
/-- The quadratic mass factor has its exponentially weighted maximum at the ray endpoint. -/
theorem quadratic_ray_bound {q c : ℝ} (hq : 5 ≤ q) (hc : 2/5 ≤ c) :
    q^2*Real.exp (-c*q) ≤ 25*Real.exp (-5*c) := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hp : q^2*Real.exp (-((2/5)*q)) ≤ 25*Real.exp (-2) := by
    have h := _root_.RHTower.pow_mul_exp_neg_le_stationary_radius 2
      (a := 5) (t := q) (by norm_num) hq0
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have he : Real.exp (-(c-2/5)*q) ≤ Real.exp (-(c-2/5)*5) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hq)]
  calc
    _ = (q^2*Real.exp (-((2/5)*q)))*Real.exp (-(c-2/5)*q) := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ (25*Real.exp (-2))*Real.exp (-(c-2/5)*5) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring
private def tailWeight (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |gaussianBasis i u| * |gaussianBasis j v| *
    (((2*(u.val+v.val)).factorial : ℝ)*(80/9)^(u.val+v.val)*(8000*100)/20^17)
private theorem tailWeight_symm (i j : Fin 5) : tailWeight i j=tailWeight j i := by
  unfold tailWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Nat.add_comm u.val v.val]
  ring
private theorem tail_bound_0_0 : tailWeight 0 0 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_1 : tailWeight 0 1 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_2 : tailWeight 0 2 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_3 : tailWeight 0 3 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_0_4 : tailWeight 0 4 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_1 : tailWeight 1 1 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_2 : tailWeight 1 2 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_3 : tailWeight 1 3 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_1_4 : tailWeight 1 4 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_2 : tailWeight 2 2 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_3 : tailWeight 2 3 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_2_4 : tailWeight 2 4 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_3_3 : tailWeight 3 3 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_3_4 : tailWeight 3 4 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_bound_4_4 : tailWeight 4 4 ≤ 1/10000 := by
  norm_num [tailWeight,gaussianBasis,Fin.sum_univ_succ]
private theorem tail_basis_bound (i j : Fin 5) : tailWeight i j ≤ 1/10000 := by
  fin_cases i <;> fin_cases j
  · exact tail_bound_0_0
  · exact tail_bound_0_1
  · exact tail_bound_0_2
  · exact tail_bound_0_3
  · exact tail_bound_0_4
  · rw [tailWeight_symm]; exact tail_bound_0_1
  · exact tail_bound_1_1
  · exact tail_bound_1_2
  · exact tail_bound_1_3
  · exact tail_bound_1_4
  · rw [tailWeight_symm]; exact tail_bound_0_2
  · rw [tailWeight_symm]; exact tail_bound_1_2
  · exact tail_bound_2_2
  · exact tail_bound_2_3
  · exact tail_bound_2_4
  · rw [tailWeight_symm]; exact tail_bound_0_3
  · rw [tailWeight_symm]; exact tail_bound_1_3
  · rw [tailWeight_symm]; exact tail_bound_2_3
  · exact tail_bound_3_3
  · exact tail_bound_3_4
  · rw [tailWeight_symm]; exact tail_bound_0_4
  · rw [tailWeight_symm]; exact tail_bound_1_4
  · rw [tailWeight_symm]; exact tail_bound_2_4
  · rw [tailWeight_symm]; exact tail_bound_3_4
  · exact tail_bound_4_4
private theorem weighted_first_mass_bound {q : ℝ} (hq : 5 ≤ q) :
    (2*q-3)^2*Real.exp (-(529/50)*q) ≤ 100/(20 : ℝ)^17 := by
  have hp : (2*q-3)^2 ≤ 4*q^2 := by nlinarith only [hq]
  have hf := quadratic_ray_bound hq (by norm_num : (2/5 : ℝ) ≤ 529/50)
  have he : Real.exp (-5*(529/50 : ℝ)) ≤ 1/(20 : ℝ)^17 := by
    simpa only [neg_mul] using exp_neg_three_multiple 17
      (t := 5*(529/50)) (by norm_num)
  calc
    _ ≤ 4*(q^2*Real.exp (-(529/50)*q)) := by
      nlinarith only [mul_le_mul_of_nonneg_right hp (Real.exp_pos (-(529/50)*q)).le]
    _ ≤ 100*Real.exp (-5*(529/50)) := by nlinarith only [hf]
    _ ≤ _ := by nlinarith only [he]
private theorem normalized_tail_moment_bound {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : ℕ) :
    |(-1 : ℝ)^k*(thetaCuspNativeReflectionJet (2*k) x-
      thetaCuspThreeAtomReflectionJet (2*k) x)/
      (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^k)| ≤
    ((2*k).factorial : ℝ)*(80/9)^k*(8000*100)/(20 : ℝ)^17 := by
  set q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 < q := by linarith only [hq]
  have hK : 0 < sourceUnit x := by
    change 0 < 4*q^2*Real.exp (x-2*q)
    positivity
  have hD : 0 < sourceUnit x*q^k := mul_pos hK (pow_pos hq0 _)
  have hmass := _root_.RHTower.ThetaCuspOddFourCentralBound.sourceTerm_one_sq x
  change thetaCuspSourceTerm x 1^2=sourceUnit x*(2*q-3)^2 at hmass
  have ht := _root_.RHTower.ThetaCuspThreeAtomCauchyTail.native_threeAtom_cauchy_error (2*k)
    (show 3 ≤ thetaCuspSingleAtomReflectionScale 1 x by linarith only [hq])
  have hb := weighted_first_mass_bound hq
  have hden : (9/80 : ℝ)^k ≤ (3/20 : ℝ)^(2*k)*q^k := by
    rw [pow_mul (3/20 : ℝ) 2 k,← mul_pow]
    apply pow_le_pow_left₀ (by norm_num)
    norm_num
    linarith only [hq]
  have hn : 0 ≤ ((2*k).factorial : ℝ)*8000*(100/(20 : ℝ)^17) := by positivity
  calc
    _ = |thetaCuspNativeReflectionJet (2*k) x-thetaCuspThreeAtomReflectionJet (2*k) x|/
        (sourceUnit x*q^k) := by
      rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,abs_of_pos hD]
    _ ≤ (((2*k).factorial : ℝ)*(8000*thetaCuspSourceTerm x 1^2*
        Real.exp (-(529/50)*q))/(3/20)^(2*k))/(sourceUnit x*q^k) :=
      div_le_div_of_nonneg_right ht hD.le
    _ = (((2*k).factorial : ℝ)*8000*((2*q-3)^2*Real.exp (-(529/50)*q)))/
        ((3/20)^(2*k)*q^k) := by
      rw [hmass]
      field_simp [hK.ne', hq0.ne']
    _ ≤ (((2*k).factorial : ℝ)*8000*(100/(20 : ℝ)^17))/
        ((3/20)^(2*k)*q^k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (((2*k).factorial : ℝ)*8000*(100/(20 : ℝ)^17))/(9/80 : ℝ)^k :=
      div_le_div_of_nonneg_left hn (by positivity) hden
    _ = _ := by
      rw [div_eq_mul_inv,← inv_pow]
      norm_num
      ring
/-- Entrywise moment bounds pass through the absolute Gaussian coordinate weights. -/
theorem gaussian_entry_majorant (A : Matrix (Fin 5) (Fin 5) ℝ)
    (m : ℕ → ℝ) (hA : ∀ u v, |A u v| ≤ m (u.val+v.val)) (i j : Fin 5) :
    |gaussianGram A i j| ≤ ∑ u : Fin 5, ∑ v : Fin 5,
      |gaussianBasis i u| * |gaussianBasis j v| * m (u.val+v.val) := by
  unfold gaussianGram
  calc
    _ ≤ ∑ u : Fin 5, |∑ v : Fin 5, gaussianBasis i u*gaussianBasis j v*A u v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : Fin 5, ∑ v : Fin 5, |gaussianBasis i u*gaussianBasis j v*A u v| :=
      Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      rw [abs_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left (hA u v) (by positivity)
/-- The entire reflected tail beyond three atoms fits a uniform entry reserve on the scale-five ray. -/
theorem tailGram_bound {x : ℝ} (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin 5) : |tailGram x i j| ≤ 1/10000 := by
  have h := gaussian_entry_majorant
    (fun u v => (-1 : ℝ)^(u.val+v.val)*
      (thetaCuspNativeReflectionJet (2*(u.val+v.val)) x-
        thetaCuspThreeAtomReflectionJet (2*(u.val+v.val)) x)/
          (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(u.val+v.val)))
    (fun k => ((2*k).factorial : ℝ)*(80/9)^k*(8000*100)/(20 : ℝ)^17)
    (fun u v => normalized_tail_moment_bound hq (u.val+v.val)) i j
  exact h.trans (tail_basis_bound i j)

private theorem exp_neg_three_multiple_add_one (n : ℕ) {t : ℝ}
    (ht : (n : ℝ)*3+1 ≤ t) : Real.exp (-t) ≤ (3/8)/(20 : ℝ)^n := by
  have he : Real.exp (-1 : ℝ) ≤ 3/8 := by
    rw [Real.exp_neg,inv_eq_one_div]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8/3) exp_one_lower
    norm_num at h
    simpa only [one_div] using h
  have hm := exp_neg_three_multiple n (t := (n : ℝ)*3) le_rfl
  calc
    _ ≤ Real.exp (-((n : ℝ)*3)-1) := Real.exp_le_exp.mpr (by linarith only [ht])
    _ = Real.exp (-((n : ℝ)*3))*Real.exp (-1) := by rw [sub_eq_add_neg,Real.exp_add]
    _ ≤ (1/(20 : ℝ)^n)*(3/8) := mul_le_mul hm he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

private theorem shifted_polynomial_bound {q c : ℝ} (hq : 5 ≤ q) (hc : 0 < c)
    (a : Fin 19 → ℝ) :
    Real.exp (-c*q)* |∑ j : Fin 19, (q-5)^j.val*a j| ≤
      Real.exp (-5*c)*(∑ j : Fin 19, |a j| *(3*(j.val : ℝ)/(8*c))^j.val) := by
  have hy : 0 ≤ q-5 := sub_nonneg.mpr hq
  have hb : Real.exp (-c*(q-5))* |∑ j : Fin 19, (q-5)^j.val*a j| ≤
      ∑ j : Fin 19, |a j| *(3*(j.val : ℝ)/(8*c))^j.val := by
    calc
      _ ≤ Real.exp (-c*(q-5))*(∑ j : Fin 19, |(q-5)^j.val*a j|) :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.exp_pos _).le
      _ = ∑ j : Fin 19, |a j| *((q-5)^j.val*Real.exp (-c*(q-5))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul,abs_of_nonneg (pow_nonneg hy _)]
        ring
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (shifted_power_bound j.val hc hy) (abs_nonneg _)
  calc
    _ = Real.exp (-5*c)*(Real.exp (-c*(q-5))* |∑ j : Fin 19, (q-5)^j.val*a j|) := by
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le

private theorem normalized_shifted_bound {q c : ℝ} (hq : 5 ≤ q) (hc : 0 < c)
    (a : Fin 19 → ℝ) :
    Real.exp (-c*q)* |(∑ j : Fin 19, (q-5)^j.val*a j)/q^8| ≤
      Real.exp (-5*c)*(∑ j : Fin 19, |a j| *(3*(j.val : ℝ)/(8*c))^j.val)/5^8 := by
  have hq0 : 0 < q := by linarith only [hq]
  have hpow : (5 : ℝ)^8 ≤ q^8 := pow_le_pow_left₀ (by norm_num) hq 8
  have hmajor : 0 ≤ Real.exp (-5*c)*(∑ j : Fin 19,
      |a j| *(3*(j.val : ℝ)/(8*c))^j.val) := by positivity
  calc
    _ = (Real.exp (-c*q)* |∑ j : Fin 19, (q-5)^j.val*a j|)/q^8 := by
      rw [abs_div,abs_of_pos (pow_pos hq0 8)]
      ring
    _ ≤ (Real.exp (-5*c)*(∑ j : Fin 19,
        |a j| *(3*(j.val : ℝ)/(8*c))^j.val))/q^8 :=
      div_le_div_of_nonneg_right (shifted_polynomial_bound hq hc a) (pow_pos hq0 8).le
    _ ≤ _ := div_le_div_of_nonneg_left hmajor (by norm_num) hpow

private theorem radial_div_eq_weighted {q : ℝ} (hq : 0 < q) (k : ℕ) (hk : k ≤ 8)
    (p : ℝ) : p/q^k=(q^(8-k)*p)/q^8 := by
  have hp : q^(8-k)*q^k=q^8 := by rw [← pow_add,Nat.sub_add_cancel hk]
  field_simp [hq.ne']
  nlinarith only [congrArg (fun t : ℝ => t*p) hp]

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)


-- Coefficients of `q^(8-k) P_k(9q²,10q)` in powers of `q-5`.
private def thirdCoeffs0 : ℕ → ℝ
  | 0 => 237890625
  | 1 => 497812500
  | 2 => 468000000
  | 3 => 260325000
  | 4 => 94893750
  | 5 => 23688000
  | 6 => 4101300
  | 7 => 486360
  | 8 => 37809
  | 9 => 1740
  | 10 => 36
  | _ => 0

private def thirdCoeffs1 : ℕ → ℝ
  | 0 => -300890625000
  | 1 => -688837500000
  | 2 => -716295000000
  | 3 => -446601000000
  | 4 => -185510550000
  | 5 => -53906160000
  | 6 => -11181828000
  | 7 => -1655774400
  | 8 => -171529320
  | 9 => -11839776
  | 10 => -490080
  | 11 => -9216
  | _ => 0

private def thirdCoeffs2 : ℕ → ℝ
  | 0 => 332030287500000
  | 1 => 835288747500000
  | 2 => 962988274500000
  | 3 => 672746520300000
  | 4 => 317178122700000
  | 5 => 106316048052000
  | 6 => 25978716607200
  | 7 => 4662627054240
  | 8 => 610028980416
  | 9 => 56738908800
  | 10 => 3561087744
  | 11 => 135413760
  | 12 => 2359296
  | _ => 0

private def thirdCoeffs3 : ℕ → ℝ
  | 0 => -311298225870000000
  | 1 => -866772863448000000
  | 2 => -1113583726966800000
  | 3 => -874035654477600000
  | 4 => -467585030410320000
  | 5 => -180040364075366400
  | 6 => -51331057361151360
  | 7 => -10971774485965056
  | 8 => -1758129802705920
  | 9 => -208592770446336
  | 10 => -17810691532800
  | 11 => -1036394496000
  | 12 => -36836474880
  | 13 => -603979776
  | _ => 0

private def thirdCoeffs4 : ℕ → ℝ
  | 0 => 237814295869944000000
  | 1 => 742092974088916800000
  | 2 => 1073061575917958400000
  | 3 => 953157772221075840000
  | 4 => 581112240807043776000
  | 5 => 257265106002700884480
  | 6 => 85296216166417591296
  | 7 => 21516834575433308160
  | 8 => 4150203864743706624
  | 9 => 609130985631744000
  | 10 => 66970355582386176
  | 11 => 5348578295808000
  | 12 => 293337978372096
  | 13 => 9889162199040
  | 14 => 154618822656
  | _ => 0

private def thirdCoeffs5 : ℕ → ℝ
  | 0 => -137058235573061548800000
  | 1 => -491628861779810496000000
  | 2 => -816652945640343943680000
  | 3 => -834271172538592960512000
  | 4 => -586681167308107759564800
  | 5 => -301042747626828025614336
  | 6 => -116507900437377794703360
  | 7 => -34646075399806695161856
  | 8 => -7984534957505141145600
  | 9 => -1426527304040998502400
  | 10 => -196020498970259619840
  | 11 => -20348960753206689792
  | 12 => -1545116601349570560
  | 13 => -81026679752884224
  | 14 => -2624396816547840
  | 15 => -39582418599936
  | _ => 0

private def thirdCoeffs6 : ℕ → ℝ
  | 0 => 49121881333598616898560000
  | 1 => 218056434095920414276608000
  | 2 => 439183324643714263536230400
  | 3 => 537231208117119409409925120
  | 4 => 449165781864704590455422976
  | 5 => 273182036965078375843921920
  | 6 => 125360403054256346527432704
  | 7 => 44363194187120548740464640
  | 8 => 12254236845009071236448256
  | 9 => 2654040211757240856084480
  | 10 => 449623754908808990687232
  | 11 => 58999747114198169026560
  | 12 => 5882321963735152852992
  | 13 => 430988318140708945920
  | 14 => 21894510172717449216
  | 15 => 689261849220218880
  | 16 => 10133099161583616
  | _ => 0

private def thirdCoeffs7 : ℕ → ℝ
  | 0 => -2100463883929708946829312000
  | 1 => -33404931160631880684876595200
  | 2 => -114516663112931786887277936640
  | 3 => -199730993944336837884332015616
  | 4 => -220659322356062752900310630400
  | 5 => -170483961580798248037627723776
  | 6 => -97248919078760174301963878400
  | 7 => -42297853382158029705314304000
  | 8 => -14300113109778902979371335680
  | 9 => -3797032729295627785441640448
  | 10 => -794445250436080415790858240
  | 11 => -130550047772985892030906368
  | 12 => -16673708891502387658752000
  | 13 => -1622719444972889752731648
  | 14 => -116346464024173058457600
  | 15 => -5796329471434549100544
  | 16 => -179288301165619445760
  | 17 => -2594073385365405696
  | _ => 0

private def thirdCoeffs8 : ℕ → ℝ
  | 0 => -6532365853480986146987104665600
  | 1 => -24170203911787833786444886179840
  | 2 => -33105631557030501659828053868544
  | 3 => -11786281056534319147238275153920
  | 4 => 25306166114904227031368790441984
  | 5 => 46348152524385902154844660039680
  | 6 => 41807886478480174002532396302336
  | 7 => 25376079118411828032933451530240
  | 8 => 11324657630221270153273181995008
  | 9 => 3862921394044419341457461084160
  | 10 => 1026189643692821039140577476608
  | 11 => 213869556446766871969718599680
  | 12 => 34928465268180624767805554688
  | 13 => 4428711475449359262453596160
  | 14 => 427709272765976704091947008
  | 15 => 30430338545182499143680000
  | 16 => 1504679296814276746936320
  | 17 => 46209093904642426798080
  | 18 => 664082786653543858176
  | _ => 0
private def thirdCoeffs : ℕ → ℕ → ℝ
  | 0 => thirdCoeffs0
  | 1 => thirdCoeffs1
  | 2 => thirdCoeffs2
  | 3 => thirdCoeffs3
  | 4 => thirdCoeffs4
  | 5 => thirdCoeffs5
  | 6 => thirdCoeffs6
  | 7 => thirdCoeffs7
  | 8 => thirdCoeffs8
  | _ => fun _ => 0

private theorem third_polynomial_0 (y : ℝ) : (5+y)^(8-0)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 0).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs0 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs0, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_1 (y : ℝ) : (5+y)^(8-1)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 1).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs1 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs1, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_2 (y : ℝ) : (5+y)^(8-2)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 2).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs2 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs2, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_3 (y : ℝ) : (5+y)^(8-3)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 3).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs3 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs3, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_4 (y : ℝ) : (5+y)^(8-4)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 4).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs4 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs4, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_5 (y : ℝ) : (5+y)^(8-5)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 5).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs5 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs5, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_6 (y : ℝ) : (5+y)^(8-6)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 6).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs6 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs6, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_7 (y : ℝ) : (5+y)^(8-7)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 7).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs7 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs7, Fin.sum_univ_succ]
  ring

private theorem third_polynomial_8 (y : ℝ) : (5+y)^(8-8)*((thetaPairRadialEvenPolynomial (9*(5+y)^2) 8).eval (10*(5+y))) = ∑ j : Fin 19, y^j.val*thirdCoeffs8 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [thirdCoeffs8, Fin.sum_univ_succ]
  ring

-- Monomial stationary bounds, with `exp(-40) ≤ 3/(8·20^13)`.
private def thirdMajorant (k : ℕ) : ℝ :=
  (3/8)*18*(∑ j : Fin 19, |thirdCoeffs k j.val| *(3*(j.val : ℝ)/(8*8))^j.val)/
    (20^13*5^8)

private theorem third_majorant_0 : thirdMajorant 0 = 32369061440899830019507083 / 576460752303423488000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs0, Fin.sum_univ_succ]

private theorem third_majorant_1 : thirdMajorant 1 = 663416944871236205356387634067 / 9223372036854775808000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs1, Fin.sum_univ_succ]

private theorem third_majorant_2 : thirdMajorant 2 = 46450285029226244556639937674099 / 576460752303423488000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs2, Fin.sum_univ_succ]

private theorem third_majorant_3 : thirdMajorant 3 = 44368639221487729584124029526831521 / 576460752303423488000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs3, Fin.sum_univ_succ]

private theorem third_majorant_4 : thirdMajorant 4 = 1085387473528487725825406067335195373 / 18014398509481984000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs4, Fin.sum_univ_succ]

private theorem third_majorant_5 : thirdMajorant 5 = 1296641787366057650962769003132341050183 / 36028797018963968000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs5, Fin.sum_univ_succ]

private theorem third_majorant_6 : thirdMajorant 6 = 6225399902896554274015439241156138967161 / 450359962737049600000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs6, Fin.sum_univ_succ]

private theorem third_majorant_7 : thirdMajorant 7 = 2704927450731506441211039339262639412174157 / 2251799813685248000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs7, Fin.sum_univ_succ]

private theorem third_majorant_8 : thirdMajorant 8 = 60049063568849870047428611878258925871477093 / 35184372088832000000000000000000000 := by
  norm_num [thirdMajorant, thirdCoeffs, thirdCoeffs8, Fin.sum_univ_succ]

private def thirdEnvelope : ℕ → ℝ
  | 0 => 32369061440899830019507083 / 576460752303423488000000000000000000000
  | 1 => 663416944871236205356387634067 / 9223372036854775808000000000000000000000
  | 2 => 46450285029226244556639937674099 / 576460752303423488000000000000000000000
  | 3 => 44368639221487729584124029526831521 / 576460752303423488000000000000000000000
  | 4 => 1085387473528487725825406067335195373 / 18014398509481984000000000000000000000
  | 5 => 1296641787366057650962769003132341050183 / 36028797018963968000000000000000000000
  | 6 => 6225399902896554274015439241156138967161 / 450359962737049600000000000000000000
  | 7 => 2704927450731506441211039339262639412174157 / 2251799813685248000000000000000000000
  | 8 => 60049063568849870047428611878258925871477093 / 35184372088832000000000000000000000
  | _ => 0

private theorem third_majorant_eq (k : ℕ) (hk : k ≤ 8) :
    thirdMajorant k=thirdEnvelope k := by
  interval_cases k
  · exact third_majorant_0
  · exact third_majorant_1
  · exact third_majorant_2
  · exact third_majorant_3
  · exact third_majorant_4
  · exact third_majorant_5
  · exact third_majorant_6
  · exact third_majorant_7
  · exact third_majorant_8

private def thirdWeight (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |gaussianBasis i u| * |gaussianBasis j v| *
    thirdEnvelope (u.val+v.val)
private theorem thirdWeight_symm (i j : Fin 5) : thirdWeight i j=thirdWeight j i := by
  unfold thirdWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Nat.add_comm u.val v.val]
  ring

private theorem third_bound_0_0 : thirdWeight 0 0 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_0_1 : thirdWeight 0 1 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_0_2 : thirdWeight 0 2 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_0_3 : thirdWeight 0 3 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_0_4 : thirdWeight 0 4 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_1_1 : thirdWeight 1 1 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_1_2 : thirdWeight 1 2 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_1_3 : thirdWeight 1 3 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_1_4 : thirdWeight 1 4 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_2_2 : thirdWeight 2 2 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_2_3 : thirdWeight 2 3 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_2_4 : thirdWeight 2 4 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_3_3 : thirdWeight 3 3 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_3_4 : thirdWeight 3 4 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_bound_4_4 : thirdWeight 4 4 ≤ 1/160 := by
  norm_num [thirdWeight,thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem third_basis_bound (i j : Fin 5) : thirdWeight i j ≤ 1/160 := by
  fin_cases i <;> fin_cases j
  · exact third_bound_0_0
  · exact third_bound_0_1
  · exact third_bound_0_2
  · exact third_bound_0_3
  · exact third_bound_0_4
  · rw [thirdWeight_symm]; exact third_bound_0_1
  · exact third_bound_1_1
  · exact third_bound_1_2
  · exact third_bound_1_3
  · exact third_bound_1_4
  · rw [thirdWeight_symm]; exact third_bound_0_2
  · rw [thirdWeight_symm]; exact third_bound_1_2
  · exact third_bound_2_2
  · exact third_bound_2_3
  · exact third_bound_2_4
  · rw [thirdWeight_symm]; exact third_bound_0_3
  · rw [thirdWeight_symm]; exact third_bound_1_3
  · rw [thirdWeight_symm]; exact third_bound_2_3
  · exact third_bound_3_3
  · exact third_bound_3_4
  · rw [thirdWeight_symm]; exact third_bound_0_4
  · rw [thirdWeight_symm]; exact third_bound_1_4
  · rw [thirdWeight_symm]; exact third_bound_2_4
  · rw [thirdWeight_symm]; exact third_bound_3_4
  · exact third_bound_4_4

-- Coefficients of `q^(8-k) P_k(36q²,13q)` in powers of `q-5`.
private def second_thirdCoeffs0 : ℕ → ℝ
  | 0 => 1257421875
  | 1 => 2543906250
  | 2 => 2315812500
  | 3 => 1249200000
  | 4 => 442181250
  | 5 => 107320500
  | 6 => 18087300
  | 7 => 2090160
  | 8 => 158499
  | 9 => 7122
  | 10 => 144
  | _ => 0

private def second_thirdCoeffs1 : ℕ → ℝ
  | 0 => -565546875000
  | 1 => -1269435937500
  | 2 => -1295113125000
  | 3 => -792743250000
  | 4 => -323476050000
  | 5 => -92390025000
  | 6 => -18847542000
  | 7 => -2746189200
  | 8 => -280077240
  | 9 => -19041756
  | 10 => -776712
  | 11 => -14400
  | _ => 0

private def second_thirdCoeffs2 : ℕ → ℝ
  | 0 => 131649731250000
  | 1 => 353034693750000
  | 2 => 430385406000000
  | 3 => 315820747050000
  | 4 => 155522958150000
  | 5 => 54187836714000
  | 6 => 13706714490000
  | 7 => 2537458824720
  | 8 => 341357769216
  | 9 => 32556376512
  | 10 => 2090158128
  | 11 => 81127200
  | 12 => 1440000
  | _ => 0

private def second_thirdCoeffs3 : ℕ → ℝ
  | 0 => 10999822875000000
  | 1 => 9490399671000000
  | 2 => -14634736222800000
  | 3 => -32184730398000000
  | 4 => -28055703019440000
  | 5 => -14871845648856000
  | 6 => -5367738821383680
  | 7 => -1380945007194816
  | 8 => -257478760016832
  | 9 => -34691627320320
  | 10 => -3302819502720
  | 11 => -211248792000
  | 12 => -8158800000
  | 13 => -144000000
  | _ => 0

private def second_thirdCoeffs4 : ℕ → ℝ
  | 0 => -7524488336112000000
  | 1 => -24557271455695200000
  | 2 => -33890387107634400000
  | 3 => -26302633004034240000
  | 4 => -12519804573239712000
  | 5 => -3547631158674973440
  | 6 => -395895055361965824
  | 7 => 121184929740721152
  | 8 => 69718532726366208
  | 9 => 17456930889300480
  | 10 => 2748451840465920
  | 11 => 287724278016000
  | 12 => 19594053600000
  | 13 => 790536000000
  | 14 => 14400000000
  | _ => 0

private def second_thirdCoeffs5 : ℕ → ℝ
  | 0 => -4164424953383952000000
  | 1 => -9431428477232290560000
  | 2 => -8020409946120106368000
  | 3 => -2045915045859663590400
  | 4 => 1701978751809145697280
  | 5 => 1896833581091497626624
  | 6 => 915614559500230683648
  | 7 => 267286173341520706560
  | 8 => 48089350334268856320
  | 9 => 4196762763474554880
  | 10 => -268589454783805440
  | 11 => -137587881776640000
  | 12 => -20221629792000000
  | 13 => -1637840880000000
  | 14 => -73524000000000
  | 15 => -1440000000000
  | _ => 0

private def second_thirdCoeffs6 : ℕ → ℝ
  | 0 => -770973959241883937280000
  | 1 => 221125802630653169664000
  | 2 => 3481645169378479378329600
  | 3 => 5139957752498408543232000
  | 4 => 3796191159459087209127936
  | 5 => 1658637822848656354516992
  | 6 => 418969823385835469733888
  | 7 => 36882768541710774312960
  | 8 => -13627112076832204431360
  | 9 => -6059607100700604887040
  | 10 => -1157037595104451399680
  | 11 => -114414852539460096000
  | 12 => -2246444069376000000
  | 13 => 891198209280000000
  | 14 => 117341496000000000
  | 15 => 6499920000000000
  | 16 => 144000000000000
  | _ => 0

private def second_thirdCoeffs7 : ℕ → ℝ
  | 0 => 670909130254926976880640000
  | 1 => 3092364307924362090070425600
  | 2 => 5059274000064747343531376640
  | 3 => 4205570999704077535936856064
  | 4 => 1884156209542525217197129728
  | 5 => 320904431967297485884784640
  | 6 => -121385628318783869304176640
  | 7 => -95082439176828111304458240
  | 8 => -29062483935533213090365440
  | 9 => -4667496043925956824760320
  | 10 => -219758786564309905735680
  | 11 => 67962121100704217088000
  | 12 => 15902097708890265600000
  | 13 => 1436721448458240000000
  | 14 => 26907651264000000000
  | 15 => -6104381280000000000
  | 16 => -534792000000000000
  | 17 => -14400000000000000
  | _ => 0

private def second_thirdCoeffs8 : ℕ → ℝ
  | 0 => 952876234919502070667963596800
  | 1 => 2788991687304837221144839127040
  | 2 => 3095013137372593866547403882496
  | 3 => 1406560214972164962827639980032
  | 4 => -179596844589747144820590968832
  | 5 => -568476000591023632985440911360
  | 6 => -325103700866866214321814896640
  | 7 => -96116675434143726281891512320
  | 8 => -13251209667010145620929085440
  | 9 => 862699588953376986503577600
  | 10 => 736750437844740746762649600
  | 11 => 137448252138417295196160000
  | 12 => 9941184433066358784000000
  | 13 => -535631184057876480000000
  | 14 => -166412079951360000000000
  | 15 => -11559726182400000000000
  | 16 => 11910960000000000000
  | 17 => 38964000000000000000
  | 18 => 1440000000000000000
  | _ => 0
private def second_thirdCoeffs : ℕ → ℕ → ℝ
  | 0 => second_thirdCoeffs0
  | 1 => second_thirdCoeffs1
  | 2 => second_thirdCoeffs2
  | 3 => second_thirdCoeffs3
  | 4 => second_thirdCoeffs4
  | 5 => second_thirdCoeffs5
  | 6 => second_thirdCoeffs6
  | 7 => second_thirdCoeffs7
  | 8 => second_thirdCoeffs8
  | _ => fun _ => 0

private theorem second_third_polynomial_0 (y : ℝ) : (5+y)^(8-0)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 0).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs0 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs0, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_1 (y : ℝ) : (5+y)^(8-1)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 1).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs1 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs1, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_2 (y : ℝ) : (5+y)^(8-2)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 2).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs2 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs2, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_3 (y : ℝ) : (5+y)^(8-3)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 3).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs3 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs3, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_4 (y : ℝ) : (5+y)^(8-4)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 4).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs4 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs4, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_5 (y : ℝ) : (5+y)^(8-5)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 5).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs5 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs5, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_6 (y : ℝ) : (5+y)^(8-6)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 6).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs6 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs6, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_7 (y : ℝ) : (5+y)^(8-7)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 7).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs7 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs7, Fin.sum_univ_succ]
  ring

private theorem second_third_polynomial_8 (y : ℝ) : (5+y)^(8-8)*((thetaPairRadialEvenPolynomial (36*(5+y)^2) 8).eval (13*(5+y))) = ∑ j : Fin 19, y^j.val*second_thirdCoeffs8 j.val := by
  norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow]
  norm_num [second_thirdCoeffs8, Fin.sum_univ_succ]
  ring

-- Monomial stationary bounds, with `exp(-55) ≤ 3/(8·20^18)`.
private def second_thirdMajorant (k : ℕ) : ℝ :=
  (3/8)*72*(∑ j : Fin 19, |second_thirdCoeffs k j.val| *(3*(j.val : ℝ)/(8*11))^j.val)/
    (20^18*5^8)

private theorem second_third_majorant_0 : second_thirdMajorant 0 = 63747616132534423104224945451 / 178240624646017358233600000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs0, Fin.sum_univ_succ]

private theorem second_third_majorant_1 : second_thirdMajorant 1 = 57883288968640816897358988641349 / 356481249292034716467200000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs1, Fin.sum_univ_succ]

private theorem second_third_majorant_2 : second_thirdMajorant 2 = 3322962090049792587355416191021787393 / 86268462328672401385062400000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs2, Fin.sum_univ_succ]

private theorem second_third_majorant_3 : second_thirdMajorant 3 = 1144783620893338735659252054179391648621 / 379581234246158566094274560000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs3, Fin.sum_univ_succ]

private theorem second_third_majorant_4 : second_thirdMajorant 4 = 94154393885234874520980275811660202650576279 / 41753935767077442270370201600000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs4, Fin.sum_univ_succ]

private theorem second_third_majorant_5 : second_thirdMajorant 5 = 1096310590013174168545653420839066081289462357363 / 918586586875703729948144435200000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs5, Fin.sum_univ_succ]

private theorem second_third_majorant_6 : second_thirdMajorant 6 = 4272302275166383448161829923408327593050661088535973 / 20208904911265482058859177574400000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs6, Fin.sum_univ_succ]

private theorem second_third_majorant_7 : second_thirdMajorant 7 = 94375194521868622957557076825968611321956340087698895349 / 444595908047840605294901906636800000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs7, Fin.sum_univ_succ]

private theorem second_third_majorant_8 : second_thirdMajorant 8 = 548822552418764954208381001627700566258156298096614194848391 / 1956221995410498663297568389201920000000000000000000000000 := by
  norm_num [second_thirdMajorant, second_thirdCoeffs, second_thirdCoeffs8, Fin.sum_univ_succ]

private def second_thirdEnvelope : ℕ → ℝ
  | 0 => 63747616132534423104224945451 / 178240624646017358233600000000000000000000000000
  | 1 => 57883288968640816897358988641349 / 356481249292034716467200000000000000000000000000
  | 2 => 3322962090049792587355416191021787393 / 86268462328672401385062400000000000000000000000000
  | 3 => 1144783620893338735659252054179391648621 / 379581234246158566094274560000000000000000000000000
  | 4 => 94154393885234874520980275811660202650576279 / 41753935767077442270370201600000000000000000000000000
  | 5 => 1096310590013174168545653420839066081289462357363 / 918586586875703729948144435200000000000000000000000000
  | 6 => 4272302275166383448161829923408327593050661088535973 / 20208904911265482058859177574400000000000000000000000000
  | 7 => 94375194521868622957557076825968611321956340087698895349 / 444595908047840605294901906636800000000000000000000000000
  | 8 => 548822552418764954208381001627700566258156298096614194848391 / 1956221995410498663297568389201920000000000000000000000000
  | _ => 0

private theorem second_third_majorant_eq (k : ℕ) (hk : k ≤ 8) :
    second_thirdMajorant k=second_thirdEnvelope k := by
  interval_cases k
  · exact second_third_majorant_0
  · exact second_third_majorant_1
  · exact second_third_majorant_2
  · exact second_third_majorant_3
  · exact second_third_majorant_4
  · exact second_third_majorant_5
  · exact second_third_majorant_6
  · exact second_third_majorant_7
  · exact second_third_majorant_8

private def second_thirdWeight (i j : Fin 5) : ℝ :=
  ∑ u : Fin 5, ∑ v : Fin 5, |gaussianBasis i u| * |gaussianBasis j v| *
    second_thirdEnvelope (u.val+v.val)
private theorem second_thirdWeight_symm (i j : Fin 5) : second_thirdWeight i j=second_thirdWeight j i := by
  unfold second_thirdWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [Nat.add_comm u.val v.val]
  ring

private theorem second_third_bound_0_0 : second_thirdWeight 0 0 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_0_1 : second_thirdWeight 0 1 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_0_2 : second_thirdWeight 0 2 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_0_3 : second_thirdWeight 0 3 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_0_4 : second_thirdWeight 0 4 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_1_1 : second_thirdWeight 1 1 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_1_2 : second_thirdWeight 1 2 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_1_3 : second_thirdWeight 1 3 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_1_4 : second_thirdWeight 1 4 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_2_2 : second_thirdWeight 2 2 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_2_3 : second_thirdWeight 2 3 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_2_4 : second_thirdWeight 2 4 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_3_3 : second_thirdWeight 3 3 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_3_4 : second_thirdWeight 3 4 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_bound_4_4 : second_thirdWeight 4 4 ≤ 1/1000 := by
  norm_num [second_thirdWeight,second_thirdEnvelope,gaussianBasis,Fin.sum_univ_succ]

private theorem second_third_basis_bound (i j : Fin 5) : second_thirdWeight i j ≤ 1/1000 := by
  fin_cases i <;> fin_cases j
  · exact second_third_bound_0_0
  · exact second_third_bound_0_1
  · exact second_third_bound_0_2
  · exact second_third_bound_0_3
  · exact second_third_bound_0_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_0_1
  · exact second_third_bound_1_1
  · exact second_third_bound_1_2
  · exact second_third_bound_1_3
  · exact second_third_bound_1_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_0_2
  · rw [second_thirdWeight_symm]; exact second_third_bound_1_2
  · exact second_third_bound_2_2
  · exact second_third_bound_2_3
  · exact second_third_bound_2_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_0_3
  · rw [second_thirdWeight_symm]; exact second_third_bound_1_3
  · rw [second_thirdWeight_symm]; exact second_third_bound_2_3
  · exact second_third_bound_3_3
  · exact second_third_bound_3_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_0_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_1_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_2_4
  · rw [second_thirdWeight_symm]; exact second_third_bound_3_4
  · exact second_third_bound_4_4

private theorem third_polynomial (k : ℕ) (hk : k ≤ 8) (q : ℝ) :
    q^(8-k)*(thetaPairRadialEvenPolynomial (9*q^2) k).eval (10*q) =
      ∑ j : Fin 19, (q-5)^j.val*thirdCoeffs k j.val := by
  have he : 5+(q-5)=q := by ring
  interval_cases k
  · simpa only [he,thirdCoeffs] using third_polynomial_0 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_1 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_2 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_3 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_4 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_5 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_6 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_7 (q-5)
  · simpa only [he,thirdCoeffs] using third_polynomial_8 (q-5)

private theorem third_moment_bound {q : ℝ} (hq : 5 ≤ q)
    (k : ℕ) (hk : k ≤ 8) :
    |(18*Real.exp (-8*q))*((thetaPairRadialEvenPolynomial (9*q^2) k).eval (10*q)/q^k)| ≤
      thirdMajorant k := by
  have hq0 : 0 < q := by linarith only [hq]
  have hp := normalized_shifted_bound hq (by norm_num : (0 : ℝ) < 8)
    (fun j : Fin 19 => thirdCoeffs k j.val)
  rw [← third_polynomial k hk q,← radial_div_eq_weighted hq0 k hk] at hp
  have he : Real.exp (-5*(8 : ℝ)) ≤ (3/8)/(20 : ℝ)^13 := by
    simpa only [neg_mul] using exp_neg_three_multiple_add_one 13 (t := 5*8) (by norm_num)
  have hm : 0 ≤ ∑ j : Fin 19, |thirdCoeffs k j.val| *
      (3*(j.val : ℝ)/(8*8))^j.val := by positivity
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hm)
    (by norm_num : (0 : ℝ) ≤ 5^8)
  calc
    _ = 18*(Real.exp (-8*q)* |(thetaPairRadialEvenPolynomial (9*q^2) k).eval (10*q)/q^k|) := by
      rw [abs_mul,abs_of_pos (by positivity : 0 < (18 : ℝ)*Real.exp (-8*q))]
      ring
    _ ≤ 18*(((3/8)/(20 : ℝ)^13)*(∑ j : Fin 19,
        |thirdCoeffs k j.val| *(3*(j.val : ℝ)/(8*8))^j.val)/5^8) :=
      mul_le_mul_of_nonneg_left (hp.trans hb) (by norm_num)
    _ = _ := by unfold thirdMajorant; ring

/-- The ordered atom pairs (1,3) and (3,1) fit a uniform Gaussian entry reserve on the scale-five ray. -/
theorem third_pairGram_bound {q : ℝ} (hq : 5 ≤ q) (i j : Fin 5) :
    |((18*Real.exp (-8*q)) • pairGram 9 10 q) i j| ≤ 1/160 := by
  let A : Matrix (Fin 5) (Fin 5) ℝ := fun u v =>
    (18*Real.exp (-8*q))*
      ((thetaPairRadialEvenPolynomial (9*q^2) (u.val+v.val)).eval (10*q)/q^(u.val+v.val))
  have hA : ∀ u v, |A u v| ≤ thirdEnvelope (u.val+v.val) := by
    intro u v
    have hk : u.val+v.val ≤ 8 := by omega
    exact (third_moment_bound hq (u.val+v.val) hk).trans_eq
      (third_majorant_eq (u.val+v.val) hk)
  have he : (18*Real.exp (-8*q)) • pairGram 9 10 q = gaussianGram A := by
    unfold pairGram A
    exact (gaussianGram_smul _ _).symm
  rw [he]
  exact (gaussian_entry_majorant A thirdEnvelope hA i j).trans (third_basis_bound i j)

private theorem second_third_polynomial (k : ℕ) (hk : k ≤ 8) (q : ℝ) :
    q^(8-k)*(thetaPairRadialEvenPolynomial (36*q^2) k).eval (13*q) =
      ∑ j : Fin 19, (q-5)^j.val*second_thirdCoeffs k j.val := by
  have he : 5+(q-5)=q := by ring
  interval_cases k
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_0 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_1 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_2 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_3 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_4 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_5 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_6 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_7 (q-5)
  · simpa only [he,second_thirdCoeffs] using second_third_polynomial_8 (q-5)

private theorem second_third_moment_bound {q : ℝ} (hq : 5 ≤ q)
    (k : ℕ) (hk : k ≤ 8) :
    |(72*Real.exp (-11*q))*((thetaPairRadialEvenPolynomial (36*q^2) k).eval (13*q)/q^k)| ≤
      second_thirdMajorant k := by
  have hq0 : 0 < q := by linarith only [hq]
  have hp := normalized_shifted_bound hq (by norm_num : (0 : ℝ) < 11)
    (fun j : Fin 19 => second_thirdCoeffs k j.val)
  rw [← second_third_polynomial k hk q,← radial_div_eq_weighted hq0 k hk] at hp
  have he : Real.exp (-5*(11 : ℝ)) ≤ (3/8)/(20 : ℝ)^18 := by
    simpa only [neg_mul] using exp_neg_three_multiple_add_one 18 (t := 5*11) (by norm_num)
  have hm : 0 ≤ ∑ j : Fin 19, |second_thirdCoeffs k j.val| *
      (3*(j.val : ℝ)/(8*11))^j.val := by positivity
  have hb := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hm)
    (by norm_num : (0 : ℝ) ≤ 5^8)
  calc
    _ = 72*(Real.exp (-11*q)* |(thetaPairRadialEvenPolynomial (36*q^2) k).eval (13*q)/q^k|) := by
      rw [abs_mul,abs_of_pos (by positivity : 0 < (72 : ℝ)*Real.exp (-11*q))]
      ring
    _ ≤ 72*(((3/8)/(20 : ℝ)^18)*(∑ j : Fin 19,
        |second_thirdCoeffs k j.val| *(3*(j.val : ℝ)/(8*11))^j.val)/5^8) :=
      mul_le_mul_of_nonneg_left (hp.trans hb) (by norm_num)
    _ = _ := by unfold second_thirdMajorant; ring

/-- The ordered atom pairs (2,3) and (3,2) fit a uniform Gaussian entry reserve on the scale-five ray. -/
theorem second_third_pairGram_bound {q : ℝ} (hq : 5 ≤ q) (i j : Fin 5) :
    |((72*Real.exp (-11*q)) • pairGram 36 13 q) i j| ≤ 1/1000 := by
  let A : Matrix (Fin 5) (Fin 5) ℝ := fun u v =>
    (72*Real.exp (-11*q))*
      ((thetaPairRadialEvenPolynomial (36*q^2) (u.val+v.val)).eval (13*q)/q^(u.val+v.val))
  have hA : ∀ u v, |A u v| ≤ second_thirdEnvelope (u.val+v.val) := by
    intro u v
    have hk : u.val+v.val ≤ 8 := by omega
    exact (second_third_moment_bound hq (u.val+v.val) hk).trans_eq
      (second_third_majorant_eq (u.val+v.val) hk)
  have he : (72*Real.exp (-11*q)) • pairGram 36 13 q = gaussianGram A := by
    unfold pairGram A
    exact (gaussianGram_smul _ _).symm
  rw [he]
  exact (gaussian_entry_majorant A second_thirdEnvelope hA i j).trans (second_third_basis_bound i j)

/-- All omitted unequal pairs and the infinite tail fit one uniform entry budget. -/
theorem remainderGram_bound {x : ℝ} (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (i j : Fin 5) : |remainderGram x i j| ≤ 147/20000 := by
  have h1 := third_pairGram_bound hq i j
  have h2 := second_third_pairGram_bound hq i j
  have ht := tailGram_bound hq i j
  unfold remainderGram omittedPairGram
  simp only [Matrix.add_apply]
  calc
    _ ≤ |((18*Real.exp (-8*thetaCuspSingleAtomReflectionScale 1 x)) •
        pairGram 9 10 (thetaCuspSingleAtomReflectionScale 1 x)) i j+
      ((72*Real.exp (-11*thetaCuspSingleAtomReflectionScale 1 x)) •
        pairGram 36 13 (thetaCuspSingleAtomReflectionScale 1 x)) i j|+|tailGram x i j| :=
      abs_add_le _ _
    _ ≤ (|((18*Real.exp (-8*thetaCuspSingleAtomReflectionScale 1 x)) •
        pairGram 9 10 (thetaCuspSingleAtomReflectionScale 1 x)) i j|+
      |((72*Real.exp (-11*thetaCuspSingleAtomReflectionScale 1 x)) •
        pairGram 36 13 (thetaCuspSingleAtomReflectionScale 1 x)) i j|)+|tailGram x i j| :=
      _root_.add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith only [h1,h2,ht]

end GaloisForLFunctions.ThetaCuspSections.FifthRemainder
