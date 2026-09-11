import GaloisForLFunctions.RHTower.ThetaCuspInnerReflectionError
import GaloisForLFunctions.HTGeometry.TwoAtomMiddleErrorBudget
/-! # Complete middle reflection-error admission

The retained/deep partition identity includes both mixed products and the
quadratic deep product. Total derivative order twelve bounds the full convolution
by twice the inner error polynomial, uniformly on the complete scale ray.
-/
namespace RHTower
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
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
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      HTGeometry.middlePartitionDeepCoefficient n*
        thetaCuspSingleAtomReflectionScale 1 x^n*thetaCuspDeepTailErrorScale x := by
  have h := abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le_hybrid hn hq
  simpa only [HTGeometry.middlePartitionDeepCoefficient,HTGeometry.middleDeepCoefficient,
    thetaCuspDeepDerivativeBoundTwelve,mul_pow,mul_assoc] using h

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
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |thetaCuspFirstAtomReflectionJet (2*k.val) x| ≤
      HTGeometry.innerFirstMomentCeiling k.val*thetaCuspSourceTerm x 1^2*
        thetaCuspSingleAtomReflectionScale 1 x^k.val := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have hd : 0 < thetaCuspSourceTerm x 1^2*thetaCuspSingleAtomReflectionScale 1 x^k.val := by positivity
  have hs : |thetaCuspFirstAtomScaledEvenJet k.val x| ≤ HTGeometry.innerFirstMomentCeiling k.val := by
    have hb : |thetaCuspFirstAtomScaledEvenJet 1 x| ≤ 11 ∧
        |thetaCuspFirstAtomScaledEvenJet 2 x| ≤ 310 ∧
        |thetaCuspFirstAtomScaledEvenJet 3 x| ≤ 14000 ∧
        |thetaCuspFirstAtomScaledEvenJet 4 x| ≤ 800000 ∧
        |thetaCuspFirstAtomScaledEvenJet 5 x| ≤ 55000000 := by
      by_cases h7 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7
      · exact thetaCuspFirstAtomScaledEvenJet_bounds_middle hq h7
      · have ht := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le (by linarith : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x)
        exact ⟨ht.1.trans (by norm_num),ht.2.1.trans (by norm_num),ht.2.2.1.trans (by norm_num),
          ht.2.2.2.1.trans (by norm_num),ht.2.2.2.2.trans (by norm_num)⟩
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
theorem abs_thetaCuspTwoAtomReflectionErrorJet_le_middle_coefficients {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspTwoAtomReflectionErrorJet n x| ≤
      thetaCuspSingleAtomReflectionScale 1 x^n*
        HTGeometry.middlePartitionErrorCoefficient n*thetaCuspDeepTailErrorScale x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let ε := thetaCuspDeepTailErrorScale x
  let a := HTGeometry.innerPartitionKeptCoefficient
  let b := HTGeometry.middlePartitionDeepCoefficient
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have he : 0 ≤ ε := by dsimp [ε,thetaCuspDeepTailErrorScale]; positivity
  have heU : ε ≤ 1/22000000000 := deep_scale_uniform hq
  have he2 : ε^2 ≤ ε/22000000000 := by
    have h := mul_le_mul_of_nonneg_left heU he
    nlinarith only [h]
  rw [thetaCuspTwoAtomReflectionErrorJet_eq n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  unfold HTGeometry.middlePartitionErrorCoefficient
  rw [Finset.mul_sum,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
  have hi12 : i ≤ 12 := hin.trans hn
  have hj12 : n-i ≤ 12 := (Nat.sub_le n i).trans hn
  have hai : 0 ≤ a i := inner_alpha_nonneg i
  have haj : 0 ≤ a (n-i) := inner_alpha_nonneg (n-i)
  have hbi : 0 ≤ b i := HTGeometry.middlePartitionDeepCoefficient_nonneg i
  have hbj : 0 ≤ b (n-i) := HTGeometry.middlePartitionDeepCoefficient_nonneg (n-i)
  have hp : q^i*q^(n-i) = q^n := by rw [← pow_add]; congr 1; omega
  have hZi := kept_derivative_bound hi12 hq
  have hZj := kept_derivative_bound hj12 hq
  have hDi := deep_derivative_bound hi12 hq
  have hDj := deep_derivative_bound hj12 hq
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
      q^n*(a i*b (n-i)+b i*a (n-i))*ε+q^n*b i*b (n-i)*ε^2 := by
    calc
      _ = (q^i*q^(n-i))*(a i*b (n-i)+b i*a (n-i))*ε+
        (q^i*q^(n-i))*b i*b (n-i)*ε^2 := by ring
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


/-- The full relative convolution is bounded by twice the earlier exact coefficient polynomial. -/
theorem abs_thetaCuspTwoAtomReflectionErrorJet_le_two_inner {n : ℕ} (hn : n ≤ 12) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspTwoAtomReflectionErrorJet n x| ≤
      2*(thetaCuspSingleAtomReflectionScale 1 x^n*
        HTGeometry.innerPartitionErrorCoefficient n*thetaCuspDeepTailErrorScale x) := by
  have hq0 : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
  have he : 0 ≤ thetaCuspDeepTailErrorScale x := by unfold thetaCuspDeepTailErrorScale; positivity
  have hk := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HTGeometry.middlePartitionErrorCoefficient_le_two_inner hn) (pow_nonneg hq0 n)) he
  calc
    _ ≤ thetaCuspSingleAtomReflectionScale 1 x^n*HTGeometry.middlePartitionErrorCoefficient n*thetaCuspDeepTailErrorScale x :=
      abs_thetaCuspTwoAtomReflectionErrorJet_le_middle_coefficients hn hq
    _ ≤ thetaCuspSingleAtomReflectionScale 1 x^n*(2*HTGeometry.innerPartitionErrorCoefficient n)*thetaCuspDeepTailErrorScale x := hk
    _ = _ := by ring

private theorem sum_range_even_only (f : ℕ → ℝ) (ho : ∀ j, f (2*j+1) = 0) (k : ℕ) :
    (∑ i ∈ Finset.range (2*k+1), f i) = ∑ j ∈ Finset.range (k+1), f (2*j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2*(k+1)+1 = (2*k+1)+1+1 by omega,Finset.sum_range_succ,
      Finset.sum_range_succ,ho k,add_zero,ih,Finset.sum_range_succ]
    rw [show 2*k+1+1 = 2*(k+1) by omega]
    simp only [Finset.sum_range_succ]

/-- All seven complete-source errors obey twice the inner polynomial on the entire scale ray. -/
theorem abs_thetaCuspNativeReflectionJet_sub_two_le_middle_budget {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) (k : Fin 7) :
    |thetaCuspNativeReflectionJet (2*k.val) x-thetaCuspTwoAtomReflectionJet (2*k.val) x| ≤
      thetaCuspSourceTerm x 1^2*(8*thetaCuspSingleAtomReflectionScale 1 x)^k.val*
        HTGeometry.middleEvenErrorBound k.val (thetaCuspSingleAtomReflectionScale 1 x) := by
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
      2*(∑ i ∈ Finset.range (2*k.val+1), summand i) := by
    rw [thetaCuspNativeReflectionJet_sub_two_eq_factored (2*k.val)
      (thetaCusp_pos_of_thirtySevenTenths_le hq)]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simp only [abs_mul,abs_of_nonneg (show (0 : ℝ) ≤ ((2*k.val).choose i : ℝ) from Nat.cast_nonneg _)]
    have hm := mul_le_mul_of_nonneg_left
      (abs_thetaCuspTwoAtomReflectionErrorJet_le_two_inner (by omega : 2*k.val-i ≤ 12) hq)
      (mul_nonneg (Nat.cast_nonneg ((2*k.val).choose i)) (abs_nonneg (thetaCuspFirstAtomReflectionJet i x)))
    convert hm using 1 <;> dsimp [summand] <;> ring
  rw [sum_range_even_only summand ho k.val] at herr
  have hpoly : (∑ r ∈ Finset.range (k.val+1), summand (2*r)) ≤
      f^2*(8*q)^k.val*HTGeometry.innerEvenErrorPolynomial k.val q*ε := by
    unfold HTGeometry.innerEvenErrorPolynomial
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro r hr
    have hrk : r ≤ k.val := by have := Finset.mem_range.mp hr; omega
    have hr7 : r < 7 := by omega
    have hdiff : 2*k.val-2*r = 2*(k.val-r) := by omega
    have hb := inner_first_moment_bound hq (⟨r,hr7⟩ : Fin 7)
    have hK := inner_K_nonneg (2*(k.val-r))
    have hp : q^r*q^(2*(k.val-r)) = q^k.val*q^(k.val-r) := by
      rw [← pow_add,← pow_add]
      congr 1
      omega
    dsimp [summand]
    rw [hdiff]
    calc
      _ ≤ ((2*k.val).choose (2*r) : ℝ)*
          (HTGeometry.innerFirstMomentCeiling r*f^2*q^r)*
          (q^(2*(k.val-r))*HTGeometry.innerPartitionErrorCoefficient (2*(k.val-r))*ε) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
          (by positivity)
      _ = ((((2*k.val).choose (2*r) : ℝ)*HTGeometry.innerFirstMomentCeiling r)*f^2*
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
    (show 0 ≤ f^2*(8*q)^k.val*HTGeometry.innerEvenErrorPolynomial k.val q by positivity)
  have hsingle : (∑ r ∈ Finset.range (k.val+1), summand (2*r)) ≤
      f^2*(8*q)^k.val*HTGeometry.innerEvenErrorBound k.val q := by
    apply hpoly.trans
    rw [HTGeometry.innerEvenErrorBound_eq]
    convert hscale using 1 <;> dsimp [q,ε,f] <;> ring
  have hall := herr.trans (mul_le_mul_of_nonneg_left hsingle (by norm_num : (0 : ℝ) ≤ 2))
  calc
    _ ≤ 2*(f^2*(8*q)^k.val*HTGeometry.innerEvenErrorBound k.val q) := hall
    _ = _ := by
      dsimp [HTGeometry.middleEvenErrorBound,q,f]
      ring

end
end RHTower
