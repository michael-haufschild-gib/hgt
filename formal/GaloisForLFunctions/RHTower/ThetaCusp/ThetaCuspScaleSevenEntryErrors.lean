import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFactoredReflectionBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFirstAtomScaleSevenProfiles
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspScaleSevenLikelihood

/-! # Explicit errors for all five Gaussian-normalized odd-block entries on scale seven -/
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

private theorem first_raw_bound {k : ℕ} {x C : ℝ} (hx : 0 < x)
    (hb : |thetaCuspFirstAtomScaledEvenJet k x| ≤ C) :
    |thetaCuspFirstAtomReflectionJet (2*k) x| ≤
      C*thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  unfold thetaCuspFirstAtomScaledEvenJet at hb
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
      thetaCuspSingleAtomReflectionScale 1 x^k)] at hb
  have h := (div_le_iff₀ (by positivity : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
    thetaCuspSingleAtomReflectionScale 1 x^k)).mp hb
  nlinarith only [h]

private theorem scaled_error_eq (k : ℕ) {x : ℝ} (hx : 0 < x) :
    |thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x| =
      |thetaCuspNativeReflectionJet (2*k) x-thetaCuspFirstAtomReflectionJet (2*k) x| /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k) := by
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale; positivity
  have he : thetaCuspNativeScaledEvenJet k x-thetaCuspFirstAtomScaledEvenJet k x =
      (-1 : ℝ)^k*(thetaCuspNativeReflectionJet (2*k) x-thetaCuspFirstAtomReflectionJet (2*k) x) /
        (thetaCuspSourceTerm x 1^(2 : ℕ)*thetaCuspSingleAtomReflectionScale 1 x^k) := by
    unfold thetaCuspNativeScaledEvenJet thetaCuspFirstAtomScaledEvenJet
    ring
  rw [he, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : 0 < thetaCuspSourceTerm x 1^(2 : ℕ)*
      thetaCuspSingleAtomReflectionScale 1 x^k)]

/-- Explicit normalized order-2 error on the complete physical scale-seven ray. -/
theorem thetaCuspNativeScaledEvenJet_1_error_le_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet 1 x-thetaCuspFirstAtomScaledEvenJet 1 x| ≤ (1/75000 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hep : 0 < ε := regimeOneLikelihoodScale_pos x
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le hq
  have he := abs_thetaCuspNativeReflectionJet_sub_first_le_factored (n := 2) (by norm_num) hq
  have b1 := first_raw_bound (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(6*q)^(0 : ℕ)*ε+(12*q)^(0 : ℕ)*ε^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 2 x-thetaCuspFirstAtomReflectionJet 2 x| ≤
      f^(2 : ℕ)*q^(1 : ℕ)*((1 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (9 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ))) := by
    dsimp [q, f, ε] at *
    nlinarith only [he, t1]
  rw [scaled_error_eq 1 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(1 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (9 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ)) ≤ (1/75000 : ℝ) := by
    have p0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
    have s0 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 0) (by norm_num) hq
    have p1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
    have s1 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 1) (by norm_num) hq
    dsimp [q, ε]
    nlinarith only [p0, s0, p1, s1]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(1 : ℕ))
  change |thetaCuspNativeReflectionJet 2 x-thetaCuspFirstAtomReflectionJet 2 x| ≤
    (1/75000 : ℝ)*(f^(2 : ℕ)*q^(1 : ℕ))
  linarith only [hb, hm]

/-- Explicit normalized order-4 error on the complete physical scale-seven ray. -/
theorem thetaCuspNativeScaledEvenJet_2_error_le_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet 2 x-thetaCuspFirstAtomScaledEvenJet 2 x| ≤ (1/250 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hep : 0 < ε := regimeOneLikelihoodScale_pos x
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le hq
  have he := abs_thetaCuspNativeReflectionJet_sub_first_le_factored (n := 4) (by norm_num) hq
  have b1 := first_raw_bound (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(6*q)^(2 : ℕ)*ε+(12*q)^(2 : ℕ)*ε^(2 : ℕ) by positivity)
  have b2 := first_raw_bound (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(6*q)^(0 : ℕ)*ε+(12*q)^(0 : ℕ)*ε^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 4 x-thetaCuspFirstAtomReflectionJet 4 x| ≤
      f^(2 : ℕ)*q^(2 : ℕ)*((1 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (54 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (210 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ))) := by
    dsimp [q, f, ε] at *
    nlinarith only [he, t1, t2]
  rw [scaled_error_eq 2 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(2 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (54 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (210 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ)) ≤ (1/250 : ℝ) := by
    have p0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
    have s0 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 0) (by norm_num) hq
    have p1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
    have s1 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 1) (by norm_num) hq
    have p2 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 2) (by norm_num) hq
    have s2 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 2) (by norm_num) hq
    dsimp [q, ε]
    nlinarith only [p0, s0, p1, s1, p2, s2]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(2 : ℕ))
  change |thetaCuspNativeReflectionJet 4 x-thetaCuspFirstAtomReflectionJet 4 x| ≤
    (1/250 : ℝ)*(f^(2 : ℕ)*q^(2 : ℕ))
  linarith only [hb, hm]

/-- Explicit normalized order-6 error on the complete physical scale-seven ray. -/
theorem thetaCuspNativeScaledEvenJet_3_error_le_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet 3 x-thetaCuspFirstAtomScaledEvenJet 3 x| ≤ (5/4 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hep : 0 < ε := regimeOneLikelihoodScale_pos x
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le hq
  have he := abs_thetaCuspNativeReflectionJet_sub_first_le_factored (n := 6) (by norm_num) hq
  have b1 := first_raw_bound (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(6*q)^(4 : ℕ)*ε+(12*q)^(4 : ℕ)*ε^(2 : ℕ) by positivity)
  have b2 := first_raw_bound (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(6*q)^(2 : ℕ)*ε+(12*q)^(2 : ℕ)*ε^(2 : ℕ) by positivity)
  have b3 := first_raw_bound (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(6*q)^(0 : ℕ)*ε+(12*q)^(0 : ℕ)*ε^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 6 x-thetaCuspFirstAtomReflectionJet 6 x| ≤
      f^(2 : ℕ)*q^(3 : ℕ)*((1 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (135 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (3150 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (8500 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ))) := by
    dsimp [q, f, ε] at *
    nlinarith only [he, t1, t2, t3]
  rw [scaled_error_eq 3 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(3 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (135 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (3150 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (8500 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ)) ≤ (5/4 : ℝ) := by
    have p0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
    have s0 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 0) (by norm_num) hq
    have p1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
    have s1 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 1) (by norm_num) hq
    have p2 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 2) (by norm_num) hq
    have s2 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 2) (by norm_num) hq
    have p3 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 3) (by norm_num) hq
    have s3 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 3) (by norm_num) hq
    dsimp [q, ε]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(3 : ℕ))
  change |thetaCuspNativeReflectionJet 6 x-thetaCuspFirstAtomReflectionJet 6 x| ≤
    (5/4 : ℝ)*(f^(2 : ℕ)*q^(3 : ℕ))
  linarith only [hb, hm]

/-- Explicit normalized order-8 error on the complete physical scale-seven ray. -/
theorem thetaCuspNativeScaledEvenJet_4_error_le_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet 4 x-thetaCuspFirstAtomScaledEvenJet 4 x| ≤ (450 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hep : 0 < ε := regimeOneLikelihoodScale_pos x
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le hq
  have he := abs_thetaCuspNativeReflectionJet_sub_first_le_factored (n := 8) (by norm_num) hq
  have b1 := first_raw_bound (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(6*q)^(6 : ℕ)*ε+(12*q)^(6 : ℕ)*ε^(2 : ℕ) by positivity)
  have b2 := first_raw_bound (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(6*q)^(4 : ℕ)*ε+(12*q)^(4 : ℕ)*ε^(2 : ℕ) by positivity)
  have b3 := first_raw_bound (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(6*q)^(2 : ℕ)*ε+(12*q)^(2 : ℕ)*ε^(2 : ℕ) by positivity)
  have b4 := first_raw_bound (k := 4) hx h4
  have t4 := mul_le_mul_of_nonneg_right b4
    (show 0 ≤ 2*(6*q)^(0 : ℕ)*ε+(12*q)^(0 : ℕ)*ε^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 7) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 8 x-thetaCuspFirstAtomReflectionJet 8 x| ≤
      f^(2 : ℕ)*q^(4 : ℕ)*((1 : ℝ)*q^(4 : ℕ)*(2*(1679616 : ℝ)*ε+(429981696 : ℝ)*ε^(2 : ℕ)) + (252 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (14700 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (238000 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (500000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ))) := by
    dsimp [q, f, ε] at *
    nlinarith only [he, t1, t2, t3, t4]
  rw [scaled_error_eq 4 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(4 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(4 : ℕ)*(2*(1679616 : ℝ)*ε+(429981696 : ℝ)*ε^(2 : ℕ)) + (252 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (14700 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (238000 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (500000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ)) ≤ (450 : ℝ) := by
    have p0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
    have s0 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 0) (by norm_num) hq
    have p1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
    have s1 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 1) (by norm_num) hq
    have p2 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 2) (by norm_num) hq
    have s2 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 2) (by norm_num) hq
    have p3 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 3) (by norm_num) hq
    have s3 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 3) (by norm_num) hq
    have p4 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 4) (by norm_num) hq
    have s4 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 4) (by norm_num) hq
    dsimp [q, ε]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3, p4, s4]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(4 : ℕ))
  change |thetaCuspNativeReflectionJet 8 x-thetaCuspFirstAtomReflectionJet 8 x| ≤
    (450 : ℝ)*(f^(2 : ℕ)*q^(4 : ℕ))
  linarith only [hb, hm]

/-- Explicit normalized order-10 error on the complete physical scale-seven ray. -/
theorem thetaCuspNativeScaledEvenJet_5_error_le_of_seven_le {x : ℝ}
    (hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspNativeScaledEvenJet 5 x-thetaCuspFirstAtomScaledEvenJet 5 x| ≤ (175000 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let ε := regimeOneLikelihoodScale x
  have hx := regimeOne_pos_of_six_le (x := x) (by linarith)
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hep : 0 < ε := regimeOneLikelihoodScale_pos x
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_of_seven_le hq
  have he := abs_thetaCuspNativeReflectionJet_sub_first_le_factored (n := 10) (by norm_num) hq
  have b1 := first_raw_bound (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(6*q)^(8 : ℕ)*ε+(12*q)^(8 : ℕ)*ε^(2 : ℕ) by positivity)
  have b2 := first_raw_bound (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(6*q)^(6 : ℕ)*ε+(12*q)^(6 : ℕ)*ε^(2 : ℕ) by positivity)
  have b3 := first_raw_bound (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(6*q)^(4 : ℕ)*ε+(12*q)^(4 : ℕ)*ε^(2 : ℕ) by positivity)
  have b4 := first_raw_bound (k := 4) hx h4
  have t4 := mul_le_mul_of_nonneg_right b4
    (show 0 ≤ 2*(6*q)^(2 : ℕ)*ε+(12*q)^(2 : ℕ)*ε^(2 : ℕ) by positivity)
  have b5 := first_raw_bound (k := 5) hx h5
  have t5 := mul_le_mul_of_nonneg_right b5
    (show 0 ≤ 2*(6*q)^(0 : ℕ)*ε+(12*q)^(0 : ℕ)*ε^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 7) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 9) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 10 x-thetaCuspFirstAtomReflectionJet 10 x| ≤
      f^(2 : ℕ)*q^(5 : ℕ)*((1 : ℝ)*q^(5 : ℕ)*(2*(60466176 : ℝ)*ε+(61917364224 : ℝ)*ε^(2 : ℕ)) + (405 : ℝ)*q^(4 : ℕ)*(2*(1679616 : ℝ)*ε+(429981696 : ℝ)*ε^(2 : ℕ)) + (44100 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (1785000 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (22500000 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (40000000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ))) := by
    dsimp [q, f, ε] at *
    nlinarith only [he, t1, t2, t3, t4, t5]
  rw [scaled_error_eq 5 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(5 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(5 : ℕ)*(2*(60466176 : ℝ)*ε+(61917364224 : ℝ)*ε^(2 : ℕ)) + (405 : ℝ)*q^(4 : ℕ)*(2*(1679616 : ℝ)*ε+(429981696 : ℝ)*ε^(2 : ℕ)) + (44100 : ℝ)*q^(3 : ℕ)*(2*(46656 : ℝ)*ε+(2985984 : ℝ)*ε^(2 : ℕ)) + (1785000 : ℝ)*q^(2 : ℕ)*(2*(1296 : ℝ)*ε+(20736 : ℝ)*ε^(2 : ℕ)) + (22500000 : ℝ)*q^(1 : ℕ)*(2*(36 : ℝ)*ε+(144 : ℝ)*ε^(2 : ℕ)) + (40000000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*ε+(1 : ℝ)*ε^(2 : ℕ)) ≤ (175000 : ℝ) := by
    have p0 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 0) (by norm_num) hq
    have s0 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 0) (by norm_num) hq
    have p1 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 1) (by norm_num) hq
    have s1 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 1) (by norm_num) hq
    have p2 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 2) (by norm_num) hq
    have s2 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 2) (by norm_num) hq
    have p3 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 3) (by norm_num) hq
    have s3 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 3) (by norm_num) hq
    have p4 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 4) (by norm_num) hq
    have s4 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 4) (by norm_num) hq
    have p5 := pow_mul_regimeOneLikelihoodScale_le_of_seven_le (k := 5) (by norm_num) hq
    have s5 := pow_mul_regimeOneLikelihoodScale_sq_le_of_seven_le (k := 5) (by norm_num) hq
    dsimp [q, ε]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3, p4, s4, p5, s5]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(5 : ℕ))
  change |thetaCuspNativeReflectionJet 10 x-thetaCuspFirstAtomReflectionJet 10 x| ≤
    (175000 : ℝ)*(f^(2 : ℕ)*q^(5 : ℕ))
  linarith only [hb, hm]

end
end RHTower
