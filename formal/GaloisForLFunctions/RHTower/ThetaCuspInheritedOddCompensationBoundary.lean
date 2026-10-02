import GaloisForLFunctions.RHTower.ThetaCuspDeepTailAffineAllOrder
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomSourceApproximation
import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCooling
import GaloisForLFunctions.RHTower.ThetaCuspOddCompensationCoefficient
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveFirstAtomJets
import GaloisForLFunctions.RHTower.ThetaCuspFinitePrimeFluxSplit
import GaloisForLFunctions.RHTower.ThetaCuspPairRadialRecurrence
import GaloisForLFunctions.RHTower.ThetaCuspSignedPoissonAtoms
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact source capacity for inherited odd compensation

At the center with Gaussian scale seven, an explicit seventh-degree odd
polynomial has positive complete-source energy. The canonical rank-three
compensation makes this same energy negative. No nonnegative scalar
correction on the new diagonal restores global positive semidefiniteness.
The exact quotient of native energy by the adverse compensation source
is the sharp positive capacity in this direction, strictly below the
canonical inherited coefficient.
-/
namespace RHTower.ThetaCuspInheritedOddCompensation
noncomputable section

private theorem gaussian_jet_bound (n m N : ℕ) {x K : ℝ}
    (hK : 0 ≤ K)
    (hbound : 2*(N : ℝ)+1/2+2*thetaCuspSingleAtomReflectionScale 1 x ≤ K)
    (hnm : n+m ≤ N) :
    |thetaCuspGaussianScaleJet n m x| ≤ K^n*thetaCuspGaussianScaleMoment m x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hq : 0 ≤ q := by dsimp [q, thetaCuspSingleAtomReflectionScale]; positivity
  have he : 0 ≤ e := (Real.exp_pos _).le
  change |thetaCuspGaussianScaleJet n m x| ≤ K^n*(e*q^m)
  induction n generalizing m with
  | zero => simp [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment, e, q,
      abs_of_nonneg (show 0 ≤ e*q^m by positivity)]
  | succ n ih =>
      have hlo := ih m (by omega)
      have hhi := ih (m+1) (by omega)
      have hmN : (m : ℝ) ≤ N := by exact_mod_cast (show m ≤ N by omega)
      have hb : 2*(m : ℝ)+1/2+2*q ≤ K := by dsimp [q]; linarith
      calc
        |thetaCuspGaussianScaleJet (n+1) m x| ≤
            |(2*(m : ℝ)+1/2)*thetaCuspGaussianScaleJet n m x|+
              |2*thetaCuspGaussianScaleJet n (m+1) x| := by
          simpa only [thetaCuspGaussianScaleJet, sub_zero, zero_sub, abs_neg] using
            (abs_sub_le ((2*(m : ℝ)+1/2)*thetaCuspGaussianScaleJet n m x) 0
              (2*thetaCuspGaussianScaleJet n (m+1) x))
        _ = (2*(m : ℝ)+1/2)*|thetaCuspGaussianScaleJet n m x|+
              2*|thetaCuspGaussianScaleJet n (m+1) x| := by
          rw [abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2*(m : ℝ)+1/2)]
          norm_num
        _ ≤ (2*(m : ℝ)+1/2)*(K^n*(e*q^m))+2*(K^n*(e*q^(m+1))) :=
          add_le_add (mul_le_mul_of_nonneg_left hlo (by positivity))
            (mul_le_mul_of_nonneg_left hhi (by norm_num))
        _ = (2*(m : ℝ)+1/2+2*q)*(K^n*(e*q^m)) := by rw [pow_succ]; ring
        _ ≤ K*(K^n*(e*q^m)) := mul_le_mul_of_nonneg_right hb (by positivity)
        _ = K^(n+1)*(e*q^m) := by ring

private theorem first_derivative_bound {n : ℕ} (hn : n ≤ 14) {x K : ℝ}
    (hq : 9/2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hK : 2*thetaCuspSingleAtomReflectionScale 1 x+65/2 ≤ K) :
    |iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 1) x| ≤
      2*K^n*thetaCuspSourceTerm x 1 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let e := Real.exp (x/2-q)
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hK0 : 0 ≤ K := by dsimp [q] at hq0; linarith
  have he : 0 ≤ e := (Real.exp_pos _).le
  have h2 := gaussian_jet_bound n 2 16 (x := x) hK0 (by norm_num; linarith) (by omega)
  have h1 := gaussian_jet_bound n 1 16 (x := x) hK0 (by norm_num; linarith) (by omega)
  change |thetaCuspGaussianScaleJet n 2 x| ≤ K^n*(e*q^2) at h2
  change |thetaCuspGaussianScaleJet n 1 x| ≤ K^n*(e*q^1) at h1
  have hs : 4*q^2+6*q ≤ 2*(4*q^2-6*q) := by
    have hp := mul_nonneg hq0 (show 0 ≤ 2*q-9 by dsimp [q]; linarith)
    nlinarith only [hp]
  rw [iteratedDeriv_firstAtom_eq_gaussianScaleJets]
  calc
    |4*thetaCuspGaussianScaleJet n 2 x-6*thetaCuspGaussianScaleJet n 1 x| ≤
        4*|thetaCuspGaussianScaleJet n 2 x|+6*|thetaCuspGaussianScaleJet n 1 x| := by
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] using
        (abs_sub_le (4*thetaCuspGaussianScaleJet n 2 x) 0
          (6*thetaCuspGaussianScaleJet n 1 x))
    _ ≤ 4*(K^n*(e*q^2))+6*(K^n*(e*q^1)) :=
      add_le_add (mul_le_mul_of_nonneg_left h2 (by norm_num))
        (mul_le_mul_of_nonneg_left h1 (by norm_num))
    _ = K^n*e*(4*q^2+6*q) := by ring
    _ ≤ K^n*e*(2*(4*q^2-6*q)) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = 2*K^n*thetaCuspSourceTerm x 1 := by
      rw [thetaCuspSourceTerm_one_eq_scale_profile]
      dsimp [q, e]
      ring

private theorem deep_derivative_bound {n : ℕ} (hn : n ≤ 14) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      125^n*thetaCuspDeepTailErrorScale x := by
  have hx := regimeOne_pos_of_six_le (x := x) (by rw [hq]; norm_num)
  by_cases hn0 : n = 0
  · subst n
    have h := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le
      (n := 0) (by norm_num) (x := x) (by rw [hq]; norm_num)
    simpa only [pow_zero, one_mul] using h
  · have hnr : (n : ℝ) ≤ 14 := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hb := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_affine n
      (by omega) hx (by rw [hq]; linarith)
    rw [hq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) (by linarith) n)
      (by unfold thetaCuspDeepTailErrorScale; positivity))

private theorem compensation_upper {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) (hx : 2/5 ≤ x) :
    thetaCuspCenterCompensationSource x ≤
      -(229/55 : ℝ)*thetaCuspSourceTerm x 1^2 := by
  have hx0 : 0 < x := by linarith
  let f := thetaCuspSourceTerm x 1
  let R := thetaCuspLikelihoodSourceRemainder x
  have hf : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx0 (by norm_num)
  have hF : 0 < thetaCuspFullSource x := thetaCuspFullSource_pos_all x
  have hR := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
    (n := 0) (by norm_num) (x := x) (by rw [hq])).1
  have hD := (thetaCuspLikelihoodSourceRemainder_signed_bounds_of_seven_le
    (n := 1) (by norm_num) (x := x) (by rw [hq])).1
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at hR
  simp only [pow_one, neg_one_mul, iteratedDeriv_one] at hD
  have hzero := thetaCuspFullSource_derivative_sub_first_eq 0 hx0
  have hone := thetaCuspFullSource_derivative_sub_first_eq 1 hx0
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.cast_one, Nat.reduceSub, one_mul, iteratedDeriv_zero,
    iteratedDeriv_one, add_zero, zero_add] at hzero hone
  have hslope : deriv (fun y : ℝ => thetaCuspSourceTerm y 1) x = -(197/22 : ℝ)*f := by
    have hd := iteratedDeriv_firstAtom_eq_gaussianScaleJets 1 x
    rw [iteratedDeriv_one] at hd
    rw [hd]
    dsimp only [thetaCuspGaussianScaleJet, thetaCuspGaussianScaleMoment, f]
    rw [thetaCuspSourceTerm_one_eq_scale_profile, hq]
    ring
  have hmass : f ≤ thetaCuspFullSource x := by
    have hp := mul_nonneg hf.le hR
    dsimp [f] at hp ⊢
    linarith only [hzero, hp]
  have hs : deriv thetaCuspFullSource x ≤ -(197/22 : ℝ)*thetaCuspFullSource x := by
    have hp : f*deriv thetaCuspLikelihoodSourceRemainder x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hf.le (by linarith only [hD])
    rw [hslope] at hone
    change thetaCuspFullSource x-f = f*R at hzero
    change deriv thetaCuspFullSource x-(-(197/22 : ℝ)*f) =
      f*deriv thetaCuspLikelihoodSourceRemainder x+(-(197/22 : ℝ)*f)*R at hone
    nlinarith only [hone, hzero, hp]
  have hprod := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 2*x*thetaCuspFullSource x by positivity)
  have hxprod := mul_le_mul_of_nonneg_right hx (sq_nonneg (thetaCuspFullSource x))
  have hsq := mul_self_le_mul_self hf.le hmass
  unfold thetaCuspCenterCompensationSource
  change 3*thetaCuspFullSource x^2+2*x*thetaCuspFullSource x*deriv thetaCuspFullSource x ≤
    -(229/55 : ℝ)*f^2
  nlinarith only [hprod, hxprod, hsq]

private theorem shifted_scale (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 1 (x+Real.log 2) =
      4*thetaCuspSingleAtomReflectionScale 1 x := by
  have he : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2=Real.log 2+Real.log 2 by ring, Real.exp_add,
      Real.exp_log (by norm_num : (0 : ℝ)<2)]
    norm_num
  unfold thetaCuspSingleAtomReflectionScale
  rw [show (2 : ℝ)*(x+Real.log 2)=2*x+2*Real.log 2 by ring, Real.exp_add, he]
  norm_num
  ring

private theorem second_shift (x : ℝ) :
    thetaCuspSourceTerm x 2 = (2 : ℝ)^(-(1/2 : ℝ))*thetaCuspSourceTerm (x+Real.log 2) 1 := by
  have h := invSqrt_mul_thetaCuspSourceTerm_shift (q:=2) (by norm_num) 1 x
  simpa only [Nat.mul_one, Nat.cast_ofNat] using h.symm

private theorem second_derivative_bound {n : ℕ} (hn : n ≤ 14) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |iteratedDeriv n (fun y : ℝ => thetaCuspSourceTerm y 2) x| ≤
      2*90^n*thetaCuspSourceTerm x 2 := by
  have hf : (fun y : ℝ => thetaCuspSourceTerm y 2) =
      fun y => (2 : ℝ)^(-(1/2 : ℝ))*thetaCuspSourceTerm (y+Real.log 2) 1 :=
    funext second_shift
  have hb := first_derivative_bound hn (x := x+Real.log 2) (K := 90)
    (by rw [shifted_scale, hq]; norm_num) (by rw [shifted_scale, hq]; norm_num)
  rw [hf, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_add_const n (fun y : ℝ => thetaCuspSourceTerm y 1) (Real.log 2), abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by norm_num) _), second_shift]
  calc
    _ ≤ (2 : ℝ)^(-(1/2 : ℝ))*(2*90^n*thetaCuspSourceTerm (x+Real.log 2) 1) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by ring

private theorem second_mass (x : ℝ)
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    thetaCuspSourceTerm x 2 = (212/11 : ℝ)*Real.exp (-21)*thetaCuspSourceTerm x 1 := by
  have he : Real.exp (2*x) = Real.exp x^2 := by
    rw [show (2 : ℝ)*x=x+x by ring, Real.exp_add, pow_two]
  have hq' : Real.pi*Real.exp x^2=7 := by
    simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one, he] using hq
  have hexp : Real.exp (-28)=Real.exp (-21)*Real.exp (-7) := by
    rw [← Real.exp_add]; norm_num
  rw [thetaCuspSourceTerm_eq_scaleForm, thetaCuspSourceTerm_eq_scaleForm]
  rw [show Real.exp (x/2)*2*Real.pi*Real.exp x^2 = Real.exp (x/2)*2*(Real.pi*Real.exp x^2) by ring, hq']
  norm_num only [Nat.cast_ofNat, Nat.cast_one, one_pow, mul_one]
  rw [hexp]
  ring

private theorem retained_derivative_bound {n : ℕ} (hn : n ≤ 14) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |iteratedDeriv n thetaCuspTwoAtomSource x| ≤
      (2*48^n+40*Real.exp (-21)*90^n)*thetaCuspSourceTerm x 1 := by
  have hx := regimeOne_pos_of_six_le (x := x) (by rw [hq]; norm_num)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0<(1:ℕ))
  have h1 := first_derivative_bound hn (x := x) (K := 48)
    (by rw [hq]; norm_num) (by rw [hq]; norm_num)
  have h2 := second_derivative_bound hn hq
  have hd (k : ℕ) : ContDiffAt ℝ n (fun y => thetaCuspSourceTerm y k) x :=
    (contDiff_thetaCuspSourceAtom k).contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  unfold thetaCuspTwoAtomSource
  rw [iteratedDeriv_fun_add (hd 1) (hd 2)]
  apply (abs_add_le _ _).trans
  apply (add_le_add h1 h2).trans
  rw [second_mass x hq]
  nlinarith [mul_nonneg (Real.exp_pos (-21)).le
    (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤90) n) hf.le)]

private theorem source_error_bound {n : ℕ} (hn : n ≤ 14) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |iteratedDeriv n thetaCuspFullSource x-iteratedDeriv n thetaCuspTwoAtomSource x| ≤
      2*173^n*thetaCuspDeepTailErrorScale x*thetaCuspSourceTerm x 1 := by
  have hx := regimeOne_pos_of_six_le (x := x) (by rw [hq]; norm_num)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0<(1:ℕ))
  have hdelta : 0 ≤ thetaCuspDeepTailErrorScale x := by
    unfold thetaCuspDeepTailErrorScale; positivity
  rw [thetaCuspFullSource_derivative_sub_two_eq n hx]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        (2*48^i*thetaCuspSourceTerm x 1)*(125^(n-i)*thetaCuspDeepTailErrorScale x) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have ha := first_derivative_bound (hi'.trans hn) (x := x) (K := 48)
        (by rw [hq]; norm_num) (by rw [hq]; norm_num)
      have hb := deep_derivative_bound ((Nat.sub_le n i).trans hn) hq
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)) hb
        (abs_nonneg _) (by positivity)
    _ = 2*(48+125 : ℝ)^n*thetaCuspDeepTailErrorScale x*thetaCuspSourceTerm x 1 := by
      simp only [add_pow, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by norm_num


private theorem product_error_bound {a b c d A B C D : ℝ}
    (ha : |a-c| ≤ A) (hb : |b-d| ≤ B) (hc : |c| ≤ C) (hd : |d| ≤ D) :
    |a*b-c*d| ≤ A*D+C*B+A*B := by
  have hA := (abs_nonneg (a-c)).trans ha
  have hC := (abs_nonneg c).trans hc
  rw [show a*b-c*d=(a-c)*d+c*(b-d)+(a-c)*(b-d) by ring]
  calc
    _ ≤ |(a-c)*d+c*(b-d)|+|(a-c)*(b-d)| := abs_add_le _ _
    _ ≤ (|(a-c)*d|+|c*(b-d)|)+|(a-c)*(b-d)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ A*D+C*B+A*B := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul ha hd (abs_nonneg _) hA)
        (mul_le_mul hc hb (abs_nonneg _) hC)) (mul_le_mul ha hb (abs_nonneg _) hA)

private theorem reflected_error_bound {n : ℕ} (hn : n ≤ 14) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x = 7) :
    |thetaCuspNativeReflectionJet n x-thetaCuspTwoAtomReflectionJet n x| ≤
      thetaCuspSourceTerm x 1^2 *
        (8*221^n*thetaCuspDeepTailErrorScale x+
         160*Real.exp (-21)*263^n*thetaCuspDeepTailErrorScale x+
         4*346^n*thetaCuspDeepTailErrorScale x^2) := by
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  let z := Real.exp (-21)
  rw [thetaCuspNativeReflectionJet_eq, thetaCuspTwoAtomReflectionJet_eq,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        ((2*173^i*δ*f)*((2*48^(n-i)+40*z*90^(n-i))*f)+
         ((2*48^i+40*z*90^i)*f)*(2*173^(n-i)*δ*f)+
         (2*173^i*δ*f)*(2*173^(n-i)*δ*f)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have hm : n-i ≤ 14 := (Nat.sub_le n i).trans hn
      have hp := product_error_bound (source_error_bound (hi'.trans hn) hq)
        (source_error_bound hm hq) (retained_derivative_bound (hi'.trans hn) hq)
        (retained_derivative_bound hm hq)
      have he (a b c d : ℝ) :
          (n.choose i : ℝ)*a*((-1:ℝ)^(n-i)*b)-
          (n.choose i : ℝ)*c*((-1:ℝ)^(n-i)*d) =
            (n.choose i : ℝ)*(-1:ℝ)^(n-i)*(a*b-c*d) := by ring
      rw [he, abs_mul, abs_mul]
      simp only [abs_of_nonneg (Nat.cast_nonneg (n.choose i) : (0:ℝ) ≤ (n.choose i : ℝ)), abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = f^2*((4*(173+48 : ℝ)^n+4*(48+173 : ℝ)^n)*δ+
        (80*z*(173+90 : ℝ)^n+80*z*(90+173 : ℝ)^n)*δ+
        4*(173+173 : ℝ)^n*δ^2) := by
      simp only [add_pow, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by norm_num only; dsimp [f, δ, z]; ring


private theorem exp_three_lower : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

private theorem second_decay_bound : Real.exp (-21 : ℝ) ≤ 1/1000000000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 7
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hp])

private theorem deep_decay_bound {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    thetaCuspDeepTailErrorScale x ≤ 1/1000000000000000000000 := by
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) exp_three_lower 12
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he : (1000000000000000 : ℝ) ≤ Real.exp (182/5) :=
    (show (1000000000000000 : ℝ) ≤ Real.exp 36 by linarith).trans
      (Real.exp_le_exp.mpr (by norm_num))
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1000000000000000) he
  unfold thetaCuspDeepTailErrorScale
  rw [hq]
  norm_num only
  rw [Real.exp_neg]
  simp only [one_div] at hi
  linarith only [hi]

/-- Positive center whose first Gaussian atom has scale seven. -/
noncomputable def witnessCenter : ℝ := Real.log (7/Real.pi)/2

private theorem witness_scale : thetaCuspSingleAtomReflectionScale 1 witnessCenter=7 := by
  unfold thetaCuspSingleAtomReflectionScale witnessCenter
  norm_num only [Nat.cast_one, one_pow, mul_one]
  rw [show (2:ℝ)*(Real.log (7/Real.pi)/2)=Real.log (7/Real.pi) by ring,
    Real.exp_log (by positivity)]
  field_simp

private theorem witness_center_lower : (2/5 : ℝ) ≤ witnessCenter := by
  have he1 : Real.exp 1 ≤ (2719/1000 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have he4 := pow_le_pow_left₀ (Real.exp_pos 1).le he1 4
  rw [← Real.exp_nat_mul] at he4
  norm_num at he4
  have he5 : Real.exp (4/5 : ℝ)^5=Real.exp 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp (4/5 : ℝ) ≤ 49/22 := by
    by_contra hc
    have hc' : (49/22 : ℝ) ≤ Real.exp (4/5) := le_of_lt (lt_of_not_ge hc)
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤49/22) hc' 5
    rw [he5] at hh
    norm_num at hh
    linarith
  have hp : Real.pi ≤ 22/7 := by linarith [Real.pi_lt_d4]
  have hq : Real.exp (4/5 : ℝ) ≤ 7/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    have hh := mul_le_mul he hp Real.pi_pos.le (by norm_num : (0:ℝ)≤49/22)
    norm_num at hh
    linarith only [hh]
  have hlog : (4/5 : ℝ) ≤ Real.log (7/Real.pi) := by
    apply Real.exp_le_exp.mp
    rwa [Real.exp_log (by positivity : (0:ℝ)<7/Real.pi)]
  unfold witnessCenter
  linarith only [hlog]


/-- Central seventh-degree odd direction, normalized at its fifth-degree coefficient. -/
def witnessVector : Fin 4 → ℝ := ![107472/7, -(2737/10), 1, -(1/1120)]

private noncomputable def witnessMajorant (r : ℝ) : ℝ :=
  (107472/7)*r+(2737/10)*r^3+r^5+r^7/1120

private theorem weighted_error_collapse (f δ z : ℝ) :
    (∑ i : Fin 4, ∑ j : Fin 4, |witnessVector i| *|witnessVector j| *
      (f^2*(8*221^(2*(i.val+j.val+1))*δ+
        160*z*263^(2*(i.val+j.val+1))*δ+
        4*346^(2*(i.val+j.val+1))*δ^2))) =
      f^2*(8*δ*witnessMajorant 221^2+160*z*δ*witnessMajorant 263^2+
        4*δ^2*witnessMajorant 346^2) := by
  norm_num [Fin.sum_univ_succ, witnessVector, witnessMajorant]
  ring

private theorem scalar_error_bound {δ z : ℝ} (hd : 0 ≤ δ) (_hz : 0 ≤ z)
    (hdU : δ ≤ 1/1000000000000000000000) (hzU : z ≤ 1/1000000000) :
    8*δ*witnessMajorant 221^2+160*z*δ*witnessMajorant 263^2+
      4*δ^2*witnessMajorant 346^2 ≤ 10000000 := by
  have hprod := mul_le_mul hzU hdU hd (by norm_num : (0:ℝ)≤1/1000000000)
  have hsq := mul_self_le_mul_self hd hdU
  norm_num [witnessMajorant] at *
  nlinarith only [hdU, hprod, hsq]

/-- Complete native signed reflected energy of the explicit odd direction. -/
noncomputable def sourceEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, witnessVector i*
    ((-1:ℝ)^(i.val+j.val+1)*thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x)*witnessVector j

private noncomputable def retainedEnergy (x : ℝ) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, witnessVector i*
    ((-1:ℝ)^(i.val+j.val+1)*thetaCuspTwoAtomReflectionJet (2*(i.val+j.val+1)) x)*witnessVector j

private theorem energy_error_bound {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    |sourceEnergy x-retainedEnergy x| ≤ 10000000*thetaCuspSourceTerm x 1^2 := by
  let δ := thetaCuspDeepTailErrorScale x
  let z := Real.exp (-21)
  let f := thetaCuspSourceTerm x 1
  have hd : 0 ≤ δ := by dsimp [δ, thetaCuspDeepTailErrorScale]; positivity
  have hz : 0 ≤ z := (Real.exp_pos _).le
  unfold sourceEnergy retainedEnergy
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 4, ∑ j : Fin 4, |witnessVector i| *|witnessVector j| *
        (f^2*(8*221^(2*(i.val+j.val+1))*δ+
          160*z*263^(2*(i.val+j.val+1))*δ+
          4*346^(2*(i.val+j.val+1))*δ^2)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_sub_distrib]
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      have hn : 2*(i.val+j.val+1) ≤ 14 := by omega
      have hb := reflected_error_bound hn hq
      have he (a b : ℝ) : witnessVector i*((-1:ℝ)^(i.val+j.val+1)*a)*witnessVector j-
          witnessVector i*((-1:ℝ)^(i.val+j.val+1)*b)*witnessVector j =
        witnessVector i*witnessVector j*(-1:ℝ)^(i.val+j.val+1)*(a-b) := by ring
      rw [he]
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]
      exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = f^2*(8*δ*witnessMajorant 221^2+160*z*δ*witnessMajorant 263^2+
        4*δ^2*witnessMajorant 346^2) := weighted_error_collapse f δ z
    _ ≤ f^2*10000000 := mul_le_mul_of_nonneg_left
      (scalar_error_bound hd hz (deep_decay_bound hq) second_decay_bound) (sq_nonneg _)
    _ = _ := by ring


open HTGeometry.SignedPoisson

private theorem signed_pair_radial (a b k : ℕ) (x : ℝ) :
    (-1:ℝ)^k*thetaCuspAtomPairReflectionJet (2*k) a b x =
      4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x) := by
  unfold thetaCuspAtomPairReflectionJet
  rw [thetaCuspAtomPairEvenJet_eq_radial]
  have he : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℝ)^k*(-1:ℝ)^k)*
      (4*(thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x)*
        Real.exp (x-thetaCuspSingleAtomReflectionScale a x-thetaCuspSingleAtomReflectionScale b x)*
        (thetaPairRadialEvenPolynomial
          (thetaCuspSingleAtomReflectionScale a x*thetaCuspSingleAtomReflectionScale b x) k).eval
          (thetaCuspSingleAtomReflectionScale a x+thetaCuspSingleAtomReflectionScale b x)) := by ring
    _ = _ := by rw [he, one_mul]

private theorem retained_moment (k : ℕ) {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    (-1:ℝ)^k*thetaCuspTwoAtomReflectionJet (2*k) x =
      196*Real.exp (x-14)*((thetaPairRadialEvenPolynomial 49 k).eval 14+
        8*Real.exp (-21)*(thetaPairRadialEvenPolynomial 196 k).eval 35+
        16*Real.exp (-21)^2*(thetaPairRadialEvenPolynomial 784 k).eval 56) := by
  have hq2 : thetaCuspSingleAtomReflectionScale 2 x=28 := by
    have he : thetaCuspSingleAtomReflectionScale 2 x=4*thetaCuspSingleAtomReflectionScale 1 x := by
      unfold thetaCuspSingleAtomReflectionScale; norm_num; ring
    rw [he, hq]; norm_num
  have he35 : Real.exp (x-35)=Real.exp (x-14)*Real.exp (-21) := by
    rw [← Real.exp_add]; congr 1; ring
  have he56 : Real.exp (x-56)=Real.exp (x-14)*Real.exp (-21)^2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [thetaCuspTwoAtomReflectionJet_eq_pairs]
  simp only [mul_add, signed_pair_radial, hq, hq2]
  norm_num only
  rw [show x-7-7=x-14 by ring, show x-7-28=x-35 by ring,
    show x-28-7=x-35 by ring, show x-28-28=x-56 by ring, he35, he56]
  ring

private noncomputable def directionEnergy (a s : ℝ) : ℝ :=
  let A : ℝ := 56-168*7
  let B : ℝ := 784-3360*7+6720*7^2
  let C : ℝ := 2304-10752*7+26880*7^2-53760*7^3
  let R := fun k => (thetaPairRadialEvenPolynomial a k).eval s
  R 7+2*A*R 6+(A^2+2*B)*R 5+2*(C+A*B)*R 4+
    (B^2+2*A*C)*R 3+2*B*C*R 2+C^2*R 1

private theorem retained_core_upper {z : ℝ} (hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    directionEnergy 49 14+8*z*directionEnergy 196 35+16*z^2*directionEnergy 784 56 <
      4000000000*(121*1120^2) := by
  norm_num [directionEnergy, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  nlinarith [sq_nonneg z, mul_self_le_mul_self hz hzU]

private theorem retained_energy_eq {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    retainedEnergy x = (196*Real.exp (x-14)/1120^2)*
      (directionEnergy 49 14+8*Real.exp (-21)*directionEnergy 196 35+
        16*Real.exp (-21)^2*directionEnergy 784 56) := by
  unfold retainedEnergy
  simp only [retained_moment _ hq]
  norm_num [Fin.sum_univ_succ, witnessVector, directionEnergy]
  ring

private theorem first_mass_square {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    thetaCuspSourceTerm x 1^2=196*121*Real.exp (x-14) := by
  rw [thetaCuspSourceTerm_one_eq_scale_profile, hq, mul_pow]
  rw [pow_two, ← Real.exp_add, show (x/2-7)+(x/2-7)=x-14 by ring]
  ring

private theorem retained_energy_upper {x : ℝ}
    (hq : thetaCuspSingleAtomReflectionScale 1 x=7) :
    retainedEnergy x < 4000000000*thetaCuspSourceTerm x 1^2 := by
  have hb := retained_core_upper (Real.exp_pos (-21)).le second_decay_bound
  have hm := mul_lt_mul_of_pos_left hb
    (show 0 < 196*Real.exp (x-14)/1120^2 by positivity)
  rw [retained_energy_eq hq, first_mass_square hq]
  nlinarith only [hm]

/-- The canonical inherited correction has a negative complete-source direction. -/
theorem inherited_direction_negative :
    sourceEnergy witnessCenter+
      thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hq := witness_scale
  have he := retained_energy_upper hq
  have herr := (le_abs_self (sourceEnergy witnessCenter-retainedEnergy witnessCenter)).trans
    (energy_error_bound hq)
  have hg := compensation_upper hq witness_center_lower
  have hc := thetaCuspNativeOddCompensationCoefficient_bounds
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (show (0:ℝ)<witnessCenter by linarith [witness_center_lower]) (by norm_num : 0<(1:ℕ))
  have hfs : 0 < thetaCuspSourceTerm witnessCenter 1^2 := sq_pos_of_pos hf
  have hgneg : thetaCuspCenterCompensationSource witnessCenter < 0 := by nlinarith only [hg, hfs]
  have hm := mul_lt_mul_of_neg_right hc.1 hgneg
  nlinarith only [he, herr, hg, hm, hfs]


private theorem retained_core_lower {z : ℝ} (_hz : 0 ≤ z) (hzU : z ≤ 1/1000000000) :
    20000000*(121*1120^2) <
      directionEnergy 49 14+8*z*directionEnergy 196 35+16*z^2*directionEnergy 784 56 := by
  norm_num [directionEnergy, thetaPairRadialEvenPolynomial, thetaPairRadialEvenStep,
    Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  nlinarith [sq_nonneg z, mul_self_le_mul_self _hz hzU]

/-- The original complete source is strictly positive in the obstructing direction. -/
theorem source_direction_positive : 0 < sourceEnergy witnessCenter := by
  have hq := witness_scale
  have hb := retained_core_lower (Real.exp_pos (-21)).le second_decay_bound
  have hm := mul_lt_mul_of_pos_left hb
    (show 0 < 196*Real.exp (witnessCenter-14)/1120^2 by positivity)
  have he : 20000000*thetaCuspSourceTerm witnessCenter 1^2 < retainedEnergy witnessCenter := by
    rw [retained_energy_eq hq, first_mass_square hq]
    nlinarith only [hm]
  have herr := (neg_le_abs (sourceEnergy witnessCenter-retainedEnergy witnessCenter)).trans
    (energy_error_bound hq)
  have hfs : 0 < thetaCuspSourceTerm witnessCenter 1^2 := by
    apply sq_pos_of_pos
    exact thetaCuspSourceTerm_pos_of_pos_of_nat_pos
      (show (0:ℝ)<witnessCenter by linarith [witness_center_lower]) (by norm_num)
  nlinarith only [he, herr, hfs]

/-- Adding any nonnegative correction on the new diagonal preserves the negative direction. -/
theorem inherited_extension_direction_negative {C : ℝ} (hC : 0 ≤ C) :
    sourceEnergy witnessCenter+
      thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource witnessCenter+
      C*thetaCuspCenterCompensationSource witnessCenter*(witnessVector 3)^2 < 0 := by
  have hg := compensation_upper witness_scale witness_center_lower
  have hg0 : thetaCuspCenterCompensationSource witnessCenter ≤ 0 := by
    nlinarith [sq_nonneg (thetaCuspSourceTerm witnessCenter 1)]
  have hn := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hC hg0)
    (sq_nonneg (witnessVector 3))
  linarith only [inherited_direction_negative, hn]


private theorem witness_compensation_negative :
    thetaCuspCenterCompensationSource witnessCenter < 0 := by
  have hg := compensation_upper witness_scale witness_center_lower
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos
    (show (0:ℝ)<witnessCenter by linarith [witness_center_lower]) (by norm_num : 0<(1:ℕ))
  nlinarith only [hg, sq_pos_of_pos hf]

/-- Exact capacity of the complete source in the central seventh-degree direction. -/
noncomputable def correctionBudget : ℝ :=
  sourceEnergy witnessCenter / (-thetaCuspCenterCompensationSource witnessCenter)

/-- The complete source admits a positive correction interval, strictly below the inherited load. -/
theorem correction_budget_bounds :
    0 < correctionBudget ∧ correctionBudget < thetaCuspNativeOddCompensationCoefficient := by
  have hg := neg_pos.mpr witness_compensation_negative
  constructor
  · exact div_pos source_direction_positive hg
  · unfold correctionBudget
    apply (div_lt_iff₀ hg).2
    linarith only [inherited_direction_negative]

/-- This actual-source budget is the sharp sign boundary in the obstructing direction. -/
theorem source_direction_positive_iff (C : ℝ) :
    (0 < sourceEnergy witnessCenter+C*thetaCuspCenterCompensationSource witnessCenter) ↔
      C < correctionBudget := by
  unfold correctionBudget
  rw [lt_div_iff₀ (neg_pos.mpr witness_compensation_negative)]
  constructor <;> intro h <;> nlinarith only [h]

/-- Native odd block with the canonical old diagonal and one new scalar diagonal correction. -/
noncomputable def inheritedMatrix (C x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (-1:ℝ)^(i.val+j.val+1)*thetaCuspNativeReflectionJet (2*(i.val+j.val+1)) x+
    (if i.val=2 ∧ j.val=2 then thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x else 0)+
    (if i.val=3 ∧ j.val=3 then C*thetaCuspCenterCompensationSource x else 0)

private theorem inherited_matrix_witness (C x : ℝ) :
    dotProduct witnessVector ((inheritedMatrix C x).mulVec witnessVector) =
      sourceEnergy x+thetaCuspNativeOddCompensationCoefficient*thetaCuspCenterCompensationSource x+
        C*thetaCuspCenterCompensationSource x*(witnessVector 3)^2 := by
  rw [show witnessVector 3=-(1/1120 : ℝ) from rfl]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, inheritedMatrix, witnessVector, sourceEnergy]
  ring

/-- No nonnegative scalar on the new diagonal extends the inherited correction globally. -/
theorem not_exists_global_inherited_posSemidef :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (inheritedMatrix C x).PosSemidef := by
  rintro ⟨C, hC, hM⟩
  have hx : 0 ≤ witnessCenter := by linarith [witness_center_lower]
  have hpos := (hM witnessCenter hx).dotProduct_mulVec_nonneg witnessVector
  simp only [star_trivial] at hpos
  rw [inherited_matrix_witness] at hpos
  exact (not_lt_of_ge hpos) (inherited_extension_direction_negative hC)


end
end RHTower.ThetaCuspInheritedOddCompensation
