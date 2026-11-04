import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralBound

/-!
# Remaining pairs and the three-atom tail in fifth even coordinates

The common positive factor is `4q² exp(x-2q)`. After dividing the moment of
order `k` by `q^k`, the two remaining unequal pairs have weights `18 exp(-8q)`
and `72 exp(-11q)`. The reflected tail is expressed in the same Gaussian
coordinates, so its entry bounds can be compared with the leading-pair reserve.
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
private theorem gaussian_entry_majorant (A : Matrix (Fin 5) (Fin 5) ℝ)
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
end GaloisForLFunctions.ThetaCuspSections.FifthRemainder
