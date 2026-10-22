import GaloisForLFunctions.HTGeometry.TwoAtomAffineEvenFour
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomMiddleProfiles
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.HTGeometry.TwoAtomInnerErrorBudget
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspInnerSourceReserves
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomMiddleCoolingTwelve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomReflectedTwelve
/-!
# Complete inner reflection error through derivative twelve

The exact retained/deep partition identity carries every source atom. All seven
first-atom moments and all thirteen partition derivatives are bounded before
the reflected convolution is normalized. Both linear tail products and the
quadratic tail product enter the proved four-coordinate absorption budget.
-/
namespace HTGeometry
noncomputable section

private theorem sixth_polynomial_bound {q : ℝ} (hq : 37/10 ≤ q) :
    |twoAtomAffineEvenMoment6 q 0| ≤ 20000000000*(2*q-3)^(2 : ℕ)*q^(6 : ℕ) := by
  obtain ⟨v,hv,rfl⟩ := exists_nonneg_add_of_le hq
  have hp : 0 ≤ 20000000000*(2*(37/10+v)-3)^(2 : ℕ)*(37/10+v)^(6 : ℕ)+
      twoAtomAffineEvenMoment6 (37/10+v) 0 := by
    unfold twoAtomAffineEvenMoment6
    ring_nf
    positivity
  have hm : 0 ≤ 20000000000*(2*(37/10+v)-3)^(2 : ℕ)*(37/10+v)^(6 : ℕ)-
      twoAtomAffineEvenMoment6 (37/10+v) 0 := by
    unfold twoAtomAffineEvenMoment6
    ring_nf
    positivity
  exact abs_le.mpr ⟨by linarith only [hp],by linarith only [hm]⟩
end
end HTGeometry

namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
/-- The sixth signed first-atom moment admits an absolute middle-scale bound. -/
theorem thetaCuspFirstAtomScaledEvenJet_six_abs_le_inner {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspFirstAtomScaledEvenJet 6 x| ≤ 20000000000 := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hqp : 0 < q := by dsimp [q]; linarith
  have hd : 0 < (2*q-3)^(2 : ℕ)*q^(6 : ℕ) := by
    apply mul_pos (pow_pos (by dsimp [q]; linarith) _) (pow_pos hqp _)
  have hden : 0 < 36-q*48+q^(2 : ℕ)*16 := by
    have hh : 0 < (4*q-6)^(2 : ℕ) := pow_pos (by dsimp [q]; linarith) _
    nlinarith only [hh]
  have heq : thetaCuspFirstAtomScaledEvenJet 6 x =
      HTGeometry.twoAtomAffineEvenMoment6 q 0/((2*q-3)^(2 : ℕ)*q^(6 : ℕ)) := by
    unfold thetaCuspFirstAtomScaledEvenJet
    norm_num only [Nat.reduceMul]
    rw [thetaCuspFirstAtomReflectionJet_12,thetaCuspSourceTerm_one_eq_scale_profile]
    unfold HTGeometry.twoAtomAffineEvenMoment6
    dsimp only
    field_simp [Real.exp_ne_zero, hqp.ne', hden.ne', show 2*q-3 ≠ 0 by dsimp [q]; linarith,q]
    <;> ring_nf
    <;> field_simp [hden.ne',q]
    <;> ring
  rw [heq,abs_div,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hp := HTGeometry.sixth_polynomial_bound hq
  change |HTGeometry.twoAtomAffineEvenMoment6 q 0| ≤ _ at hp
  nlinarith only [hp]

private theorem exp_ten_22000 : (22000 : ℝ) ≤ Real.exp 10 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith only [hp]

/-- Exponential decay is retained in the denominator of every error moment. -/
theorem thetaCuspDeepTailErrorScale_le_innerDenominator {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailErrorScale x ≤
      1/HTGeometry.innerErrorDenominator (thetaCuspSingleAtomReflectionScale 1 x) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let T : ℝ := ∑ j ∈ Finset.range 11, (8*(q-37/10))^j/(j.factorial : ℝ)
  have hT : 1 ≤ T := by
    have hv : 0 ≤ 8*(q-37/10) := by dsimp [q]; linarith
    have h := Finset.single_le_sum
      (f := fun j : ℕ => (8*(q-37/10))^j/(j.factorial : ℝ))
      (fun j hj => by positivity) (by simp : 0 ∈ Finset.range 11)
    simpa only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one] using h
  have hTp : 0 < T := by linarith
  have hpoly : T ≤ Real.exp (8*(q-37/10)) :=
    Real.sum_le_exp_of_nonneg (by dsimp [q]; linarith : 0 ≤ 8*(q-37/10)) 11
  have h := mul_le_mul exp_ten_22000 hpoly (by linarith : 0 ≤ T) (Real.exp_pos 10).le
  rw [← Real.exp_add,show (10 : ℝ)+8*(q-37/10)=8*(q-49/20) by ring] at h
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-8*(q-49/20))).le
  have he : Real.exp (8*(q-49/20))*Real.exp (-8*(q-49/20)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [he] at hmul
  rw [HTGeometry.innerErrorDenominator_eq]
  change Real.exp (-8*(q-49/20))/1000000 ≤ 1/(22000000000*T)
  apply (le_div_iff₀ (by positivity : 0 < (22000000000 : ℝ)*T)).mpr
  nlinarith only [hmul]

private theorem inner_c_nonneg (n : ℕ) : 0 ≤ HTGeometry.innerDeepCoefficient n := by
  unfold HTGeometry.innerDeepCoefficient
  split <;> norm_num
private theorem inner_alpha_nonneg (n : ℕ) : 0 ≤ HTGeometry.innerPartitionKeptCoefficient n := by
  unfold HTGeometry.innerPartitionKeptCoefficient
  positivity
private theorem inner_beta_nonneg (n : ℕ) : 0 ≤ HTGeometry.innerPartitionDeepCoefficient n := by
  unfold HTGeometry.innerPartitionDeepCoefficient
  exact mul_nonneg (inner_c_nonneg n) (by positivity)
private theorem inner_K_nonneg (n : ℕ) : 0 ≤ HTGeometry.innerPartitionErrorCoefficient n := by
  unfold HTGeometry.innerPartitionErrorCoefficient
  apply Finset.sum_nonneg
  intro i hi
  have ha := inner_alpha_nonneg i
  have hb := inner_alpha_nonneg (n-i)
  have hc := inner_beta_nonneg i
  have hd := inner_beta_nonneg (n-i)
  positivity

private theorem deep_derivative_bound {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      HTGeometry.innerPartitionDeepCoefficient n*
        thetaCuspSingleAtomReflectionScale 1 x^n*thetaCuspDeepTailErrorScale x := by
  by_cases hn5 : n ≤ 5
  · have h := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le (by omega : n ≤ 10) hq
    simpa only [HTGeometry.innerPartitionDeepCoefficient,HTGeometry.innerDeepCoefficient,
      if_pos hn5,one_mul,mul_pow] using h
  · have h := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_inner_transport
      (by omega : 6 ≤ n) hn hq hqu
    simpa only [HTGeometry.innerPartitionDeepCoefficient,HTGeometry.innerDeepCoefficient,
      if_neg hn5,mul_pow,mul_assoc] using h

private theorem kept_derivative_bound {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspTwoAtomLikelihoodPartition x| ≤
      HTGeometry.innerPartitionKeptCoefficient n*thetaCuspSingleAtomReflectionScale 1 x^n := by
  have h := abs_iteratedDeriv_thetaCuspTwoAtomLikelihoodPartition_le_middle_twelve hn hq
  have he : (0 : ℝ)^n*thetaCuspSingleAtomReflectionScale 1 x^n = 0^n := by
    rw [← mul_pow,zero_mul]
  apply h.trans_eq
  unfold HTGeometry.innerPartitionKeptCoefficient
  rw [add_mul,he,mul_pow]
  ring

private theorem inner_first_moment_bound {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) (k : Fin 7) :
    |thetaCuspFirstAtomReflectionJet (2*k.val) x| ≤
      HTGeometry.innerFirstMomentCeiling k.val*thetaCuspSourceTerm x 1^(2 : ℕ)*
        thetaCuspSingleAtomReflectionScale 1 x^k.val := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k.val := by positivity
  have hs : |thetaCuspFirstAtomScaledEvenJet k.val x| ≤ HTGeometry.innerFirstMomentCeiling k.val := by
    have hb := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq (by linarith : thetaCuspSingleAtomReflectionScale 1 x ≤ 7)
    fin_cases k
    · norm_num [thetaCuspFirstAtomScaledEvenJet,thetaCuspFirstAtomReflectionJet_zero,
        HTGeometry.innerFirstMomentCeiling,div_self (pow_ne_zero 2 hf.ne')]
    · exact hb.1
    · exact hb.2.1
    · exact hb.2.2.1
    · exact hb.2.2.2.1
    · exact hb.2.2.2.2
    · exact thetaCuspFirstAtomScaledEvenJet_six_abs_le_inner hq
  simp only [thetaCuspFirstAtomScaledEvenJet,abs_div,abs_mul,abs_pow,abs_neg,
    abs_one,one_pow,one_mul,abs_of_pos hd] at hs
  have hh := (div_le_iff₀ hd).mp hs
  nlinarith only [hh]


private theorem deep_scale_uniform {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    thetaCuspDeepTailErrorScale x ≤ 1/22000000000 := by
  have hD := HTGeometry.innerErrorDenominator_lower hq
  exact (thetaCuspDeepTailErrorScale_le_innerDenominator hq).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 22000000000) hD)

/-- Complete relative reflected error, including the quadratic deep product. -/
theorem abs_thetaCuspTwoAtomReflectionErrorJet_le_inner {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    |thetaCuspTwoAtomReflectionErrorJet n x| ≤
      thetaCuspSingleAtomReflectionScale 1 x^n*
        HTGeometry.innerPartitionErrorCoefficient n*thetaCuspDeepTailErrorScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := thetaCuspDeepTailErrorScale x
  let a := HTGeometry.innerPartitionKeptCoefficient
  let b := HTGeometry.innerPartitionDeepCoefficient
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := by dsimp [ε,thetaCuspDeepTailErrorScale]; positivity
  have heU : ε ≤ 1/22000000000 := deep_scale_uniform hq
  have he2 : ε^(2 : ℕ) ≤ ε/22000000000 := by
    have h := mul_le_mul_of_nonneg_left heU he
    nlinarith only [h]
  rw [thetaCuspTwoAtomReflectionErrorJet_eq n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  unfold HTGeometry.innerPartitionErrorCoefficient
  rw [Finset.mul_sum,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hi12 : i ≤ 12 := hin.trans hn
  have hj12 : n-i ≤ 12 := (Nat.sub_le n i).trans hn
  have hai : 0 ≤ a i := inner_alpha_nonneg i
  have haj : 0 ≤ a (n-i) := inner_alpha_nonneg (n-i)
  have hbi : 0 ≤ b i := inner_beta_nonneg i
  have hbj : 0 ≤ b (n-i) := inner_beta_nonneg (n-i)
  have hp : q^i*q^(n-i) = q^n := by rw [← pow_add]; congr 1; omega
  have hZi := kept_derivative_bound hi12 hq
  have hZj := kept_derivative_bound hj12 hq
  have hDi := deep_derivative_bound hi12 hq hqu
  have hDj := deep_derivative_bound hj12 hq hqu
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,mul_one,
    abs_of_nonneg (show (0 : ℝ) ≤ (n.choose i : ℝ) from Nat.cast_nonneg _)]
  have hab : |iteratedDeriv i thetaCuspTwoAtomLikelihoodPartition x*
        iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x+
      iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
        iteratedDeriv (n-i) thetaCuspTwoAtomLikelihoodPartition x+
      iteratedDeriv i thetaCuspDeepLikelihoodRemainder x*
        iteratedDeriv (n-i) thetaCuspDeepLikelihoodRemainder x| ≤
      (a i*q^i)*(b (n-i)*q^(n-i)*ε)+(b i*q^i*ε)*(a (n-i)*q^(n-i))+
        (b i*q^i*ε)*(b (n-i)*q^(n-i)*ε) := by
    apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    simp only [abs_mul]
    exact add_le_add (add_le_add
      (mul_le_mul hZi hDj (abs_nonneg _) (by positivity))
      (mul_le_mul hDi hZj (abs_nonneg _) (by positivity)))
      (mul_le_mul hDi hDj (abs_nonneg _) (by positivity))
  have hpoly : (a i*q^i)*(b (n-i)*q^(n-i)*ε)+(b i*q^i*ε)*(a (n-i)*q^(n-i))+
        (b i*q^i*ε)*(b (n-i)*q^(n-i)*ε) =
      q^n*(a i*b (n-i)+b i*a (n-i))*ε+q^n*b i*b (n-i)*ε^(2 : ℕ) := by
    calc
      _ = (q^i*q^(n-i))*(a i*b (n-i)+b i*a (n-i))*ε+
        (q^i*q^(n-i))*b i*b (n-i)*ε^(2 : ℕ) := by ring
      _ = _ := by rw [hp]
  have hquad := mul_le_mul_of_nonneg_left he2
    (show 0 ≤ q^n*b i*b (n-i) by positivity)
  have hbound : (a i*q^i)*(b (n-i)*q^(n-i)*ε)+(b i*q^i*ε)*(a (n-i)*q^(n-i))+
      (b i*q^i*ε)*(b (n-i)*q^(n-i)*ε) ≤
      q^n*(a i*b (n-i)+b i*a (n-i)+b i*b (n-i)/22000000000)*ε := by
    rw [hpoly]
    nlinarith only [hquad]
  have hterm := hab.trans hbound
  have hfinal := mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg (n.choose i))
  convert hfinal using 1 <;> dsimp [a,b,q,ε] <;> ring


private theorem sum_range_even_only (f : ℕ → ℝ) (ho : ∀ j, f (2*j+1) = 0) (k : ℕ) :
    (∑ i ∈ Finset.range (2*k+1), f i) = ∑ j ∈ Finset.range (k+1), f (2*j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,ho k,add_zero,ih,Finset.sum_range_succ]
    rw [show 2*k+1+1 = 2*(k+1) by omega]
    simp only [Finset.sum_range_succ]

/-- The complete source error fits all seven inner budgets, without omitting any atom or matrix entry. -/
theorem abs_thetaCuspNativeReflectionJet_sub_two_le_inner_budget {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) (k : Fin 7) :
    |thetaCuspNativeReflectionJet (2*k.val) x-thetaCuspTwoAtomReflectionJet (2*k.val) x| ≤
      thetaCuspSourceTerm x 1^(2 : ℕ)*(8*thetaCuspSingleAtomReflectionScale 1 x)^k.val*
        HTGeometry.innerEvenErrorBound k.val (thetaCuspSingleAtomReflectionScale 1 x) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := thetaCuspDeepTailErrorScale x
  let f := thetaCuspSourceTerm x 1
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := by dsimp [ε,thetaCuspDeepTailErrorScale]; positivity
  let summand := fun i : ℕ => ((2*k.val).choose i : ℝ)*|thetaCuspFirstAtomReflectionJet i x| *
    (q^(2*k.val-i)*HTGeometry.innerPartitionErrorCoefficient (2*k.val-i)*ε)
  have ho (j : ℕ) : summand (2*j+1) = 0 := by
    dsimp [summand]
    rw [thetaCuspFirstAtomReflectionJet_odd_zero (by exact ⟨j,by omega⟩) x]
    simp
  have herr : |thetaCuspNativeReflectionJet (2*k.val) x-thetaCuspTwoAtomReflectionJet (2*k.val) x| ≤
      ∑ i ∈ Finset.range (2*k.val+1), summand i := by
    rw [thetaCuspNativeReflectionJet_sub_two_eq_factored (2*k.val)
      (thetaCusp_pos_of_thirtySevenTenths_le hq)]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    simp only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ ((2*k.val).choose i : ℝ) from Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (abs_thetaCuspTwoAtomReflectionErrorJet_le_inner (by omega : 2*k.val-i ≤ 12) hq hqu)
      (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
  rw [sum_range_even_only summand ho k.val] at herr
  have hpoly : (∑ r ∈ Finset.range (k.val+1), summand (2*r)) ≤
      f^(2 : ℕ)*(8*q)^k.val*HTGeometry.innerEvenErrorPolynomial k.val q*ε := by
    unfold HTGeometry.innerEvenErrorPolynomial
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    have hrk : r ≤ k.val := by have := Finset.mem_range.mp hr; omega
    have hr7 : r < 7 := by omega
    have hdiff : 2*k.val-2*r = 2*(k.val-r) := by omega
    have hb := inner_first_moment_bound hq hqu (⟨r,hr7⟩ : Fin 7)
    have hK := inner_K_nonneg (2*(k.val-r))
    have hp : q^r*q^(2*(k.val-r)) = q^k.val*q^(k.val-r) := by
      rw [← pow_add,← pow_add]
      congr 1
      omega
    dsimp [summand]
    rw [hdiff]
    calc
      _ ≤ ((2*k.val).choose (2*r) : ℝ)*
          (HTGeometry.innerFirstMomentCeiling r*f^(2 : ℕ)*q^r)*
          (q^(2*(k.val-r))*HTGeometry.innerPartitionErrorCoefficient (2*(k.val-r))*ε) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
          (by positivity)
      _ = ((((2*k.val).choose (2*r) : ℝ)*HTGeometry.innerFirstMomentCeiling r)*f^(2 : ℕ)*
            HTGeometry.innerPartitionErrorCoefficient (2*(k.val-r))*ε)*
          (q^r*q^(2*(k.val-r))) := by ring
      _ = _ := by
        rw [hp,mul_pow]
        field_simp
  have hP : 0 ≤ HTGeometry.innerEvenErrorPolynomial k.val q := by
    unfold HTGeometry.innerEvenErrorPolynomial
    apply Finset.sum_nonneg
    intro r hr
    have hM : 0 ≤ HTGeometry.innerFirstMomentCeiling r := by
      unfold HTGeometry.innerFirstMomentCeiling
      split <;> norm_num
    have hK := inner_K_nonneg (2*(k.val-r))
    positivity
  have hscale := mul_le_mul_of_nonneg_left (thetaCuspDeepTailErrorScale_le_innerDenominator hq)
    (show 0 ≤ f^(2 : ℕ)*(8*q)^k.val*HTGeometry.innerEvenErrorPolynomial k.val q by positivity)
  apply herr.trans (hpoly.trans ?_)
  rw [HTGeometry.innerEvenErrorBound_eq]
  convert hscale using 1 <;> dsimp [q,ε,f] <;> ring

end
end RHTower
