import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspMiddleEntryErrorTools

/-! # Complete normalized middle entry errors through order ten -/
namespace RHTower
noncomputable section
set_option maxHeartbeats 3000000

/-- Complete normalized order-2 error throughout the middle interval. -/
theorem thetaCuspNativeScaledEvenJet_1_two_error_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeScaledEvenJet 1 x-thetaCuspTwoAtomScaledEvenJet 1 x| ≤ (1/1000000 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hδ : 0 < δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq0 hq1
  have he := abs_thetaCuspNativeReflectionJet_sub_two_le_middle (n := 2) (by norm_num) hq0
  have b1 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(16*q)^(0 : ℕ)*δ+(22*q)^(0 : ℕ)*δ/50+5*(32*q)^(0 : ℕ)*δ^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 2 x-thetaCuspTwoAtomReflectionJet 2 x| ≤
      f^(2 : ℕ)*q^(1 : ℕ)*((1 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (11 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ))) := by
    dsimp [q, f, δ] at *
    nlinarith only [he, t1]
  rw [thetaCuspNativeScaledEvenJet_two_error_eq 1 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(1 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (11 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ)) ≤ (1/1000000 : ℝ) := by
    have p0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq0
    have s0 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 0) (by norm_num) hq0
    have p1 := thetaCuspDeepTailErrorScale_weighted_middle (k := 1) (by norm_num) hq0
    have s1 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 1) (by norm_num) hq0
    dsimp [q, δ]
    nlinarith only [p0, s0, p1, s1]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(1 : ℕ))
  change |thetaCuspNativeReflectionJet 2 x-thetaCuspTwoAtomReflectionJet 2 x| ≤
    (1/1000000 : ℝ)*(f^(2 : ℕ)*q^(1 : ℕ))
  nlinarith only [hb, hm]

/-- Complete normalized order-4 error throughout the middle interval. -/
theorem thetaCuspNativeScaledEvenJet_2_two_error_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeScaledEvenJet 2 x-thetaCuspTwoAtomScaledEvenJet 2 x| ≤ (1/1000 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hδ : 0 < δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq0 hq1
  have he := abs_thetaCuspNativeReflectionJet_sub_two_le_middle (n := 4) (by norm_num) hq0
  have b1 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(16*q)^(2 : ℕ)*δ+(22*q)^(2 : ℕ)*δ/50+5*(32*q)^(2 : ℕ)*δ^(2 : ℕ) by positivity)
  have b2 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(16*q)^(0 : ℕ)*δ+(22*q)^(0 : ℕ)*δ/50+5*(32*q)^(0 : ℕ)*δ^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 4 x-thetaCuspTwoAtomReflectionJet 4 x| ≤
      f^(2 : ℕ)*q^(2 : ℕ)*((1 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (66 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (310 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ))) := by
    dsimp [q, f, δ] at *
    nlinarith only [he, t1, t2]
  rw [thetaCuspNativeScaledEvenJet_two_error_eq 2 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(2 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (66 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (310 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ)) ≤ (1/1000 : ℝ) := by
    have p0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq0
    have s0 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 0) (by norm_num) hq0
    have p1 := thetaCuspDeepTailErrorScale_weighted_middle (k := 1) (by norm_num) hq0
    have s1 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 1) (by norm_num) hq0
    have p2 := thetaCuspDeepTailErrorScale_weighted_middle (k := 2) (by norm_num) hq0
    have s2 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 2) (by norm_num) hq0
    dsimp [q, δ]
    nlinarith only [p0, s0, p1, s1, p2, s2]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(2 : ℕ))
  change |thetaCuspNativeReflectionJet 4 x-thetaCuspTwoAtomReflectionJet 4 x| ≤
    (1/1000 : ℝ)*(f^(2 : ℕ)*q^(2 : ℕ))
  nlinarith only [hb, hm]

/-- Complete normalized order-6 error throughout the middle interval. -/
theorem thetaCuspNativeScaledEvenJet_3_two_error_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeScaledEvenJet 3 x-thetaCuspTwoAtomScaledEvenJet 3 x| ≤ (1 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hδ : 0 < δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq0 hq1
  have he := abs_thetaCuspNativeReflectionJet_sub_two_le_middle (n := 6) (by norm_num) hq0
  have b1 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(16*q)^(4 : ℕ)*δ+(22*q)^(4 : ℕ)*δ/50+5*(32*q)^(4 : ℕ)*δ^(2 : ℕ) by positivity)
  have b2 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(16*q)^(2 : ℕ)*δ+(22*q)^(2 : ℕ)*δ/50+5*(32*q)^(2 : ℕ)*δ^(2 : ℕ) by positivity)
  have b3 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(16*q)^(0 : ℕ)*δ+(22*q)^(0 : ℕ)*δ/50+5*(32*q)^(0 : ℕ)*δ^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 6 x-thetaCuspTwoAtomReflectionJet 6 x| ≤
      f^(2 : ℕ)*q^(3 : ℕ)*((1 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (165 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (4650 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (14000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ))) := by
    dsimp [q, f, δ] at *
    nlinarith only [he, t1, t2, t3]
  rw [thetaCuspNativeScaledEvenJet_two_error_eq 3 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(3 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (165 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (4650 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (14000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ)) ≤ (1 : ℝ) := by
    have p0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq0
    have s0 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 0) (by norm_num) hq0
    have p1 := thetaCuspDeepTailErrorScale_weighted_middle (k := 1) (by norm_num) hq0
    have s1 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 1) (by norm_num) hq0
    have p2 := thetaCuspDeepTailErrorScale_weighted_middle (k := 2) (by norm_num) hq0
    have s2 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 2) (by norm_num) hq0
    have p3 := thetaCuspDeepTailErrorScale_weighted_middle (k := 3) (by norm_num) hq0
    have s3 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 3) (by norm_num) hq0
    dsimp [q, δ]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(3 : ℕ))
  change |thetaCuspNativeReflectionJet 6 x-thetaCuspTwoAtomReflectionJet 6 x| ≤
    (1 : ℝ)*(f^(2 : ℕ)*q^(3 : ℕ))
  nlinarith only [hb, hm]

/-- Complete normalized order-8 error throughout the middle interval. -/
theorem thetaCuspNativeScaledEvenJet_4_two_error_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeScaledEvenJet 4 x-thetaCuspTwoAtomScaledEvenJet 4 x| ≤ (200 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hδ : 0 < δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq0 hq1
  have he := abs_thetaCuspNativeReflectionJet_sub_two_le_middle (n := 8) (by norm_num) hq0
  have b1 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(16*q)^(6 : ℕ)*δ+(22*q)^(6 : ℕ)*δ/50+5*(32*q)^(6 : ℕ)*δ^(2 : ℕ) by positivity)
  have b2 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(16*q)^(4 : ℕ)*δ+(22*q)^(4 : ℕ)*δ/50+5*(32*q)^(4 : ℕ)*δ^(2 : ℕ) by positivity)
  have b3 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(16*q)^(2 : ℕ)*δ+(22*q)^(2 : ℕ)*δ/50+5*(32*q)^(2 : ℕ)*δ^(2 : ℕ) by positivity)
  have b4 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 4) hx h4
  have t4 := mul_le_mul_of_nonneg_right b4
    (show 0 ≤ 2*(16*q)^(0 : ℕ)*δ+(22*q)^(0 : ℕ)*δ/50+5*(32*q)^(0 : ℕ)*δ^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 7) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 8 x-thetaCuspTwoAtomReflectionJet 8 x| ≤
      f^(2 : ℕ)*q^(4 : ℕ)*((1 : ℝ)*q^(4 : ℕ)*(2*(4294967296 : ℝ)*δ+(54875873536 : ℝ)*δ/50+5*(1099511627776 : ℝ)*δ^(2 : ℕ)) + (308 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (21700 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (392000 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (800000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ))) := by
    dsimp [q, f, δ] at *
    nlinarith only [he, t1, t2, t3, t4]
  rw [thetaCuspNativeScaledEvenJet_two_error_eq 4 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(4 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(4 : ℕ)*(2*(4294967296 : ℝ)*δ+(54875873536 : ℝ)*δ/50+5*(1099511627776 : ℝ)*δ^(2 : ℕ)) + (308 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (21700 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (392000 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (800000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ)) ≤ (200 : ℝ) := by
    have p0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq0
    have s0 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 0) (by norm_num) hq0
    have p1 := thetaCuspDeepTailErrorScale_weighted_middle (k := 1) (by norm_num) hq0
    have s1 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 1) (by norm_num) hq0
    have p2 := thetaCuspDeepTailErrorScale_weighted_middle (k := 2) (by norm_num) hq0
    have s2 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 2) (by norm_num) hq0
    have p3 := thetaCuspDeepTailErrorScale_weighted_middle (k := 3) (by norm_num) hq0
    have s3 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 3) (by norm_num) hq0
    have p4 := thetaCuspDeepTailErrorScale_weighted_middle (k := 4) (by norm_num) hq0
    have s4 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 4) (by norm_num) hq0
    dsimp [q, δ]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3, p4, s4]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(4 : ℕ))
  change |thetaCuspNativeReflectionJet 8 x-thetaCuspTwoAtomReflectionJet 8 x| ≤
    (200 : ℝ)*(f^(2 : ℕ)*q^(4 : ℕ))
  nlinarith only [hb, hm]

/-- Complete normalized order-10 error throughout the middle interval. -/
theorem thetaCuspNativeScaledEvenJet_5_two_error_le_middle {x : ℝ}
    (hq0 : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hq1 : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    |thetaCuspNativeScaledEvenJet 5 x-thetaCuspTwoAtomScaledEvenJet 5 x| ≤ (175000 : ℝ) := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let f := thetaCuspSourceTerm x 1
  let δ := thetaCuspDeepTailErrorScale x
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq0
  have hqp : 0 < q := by dsimp [q]; linarith
  have hfp : 0 < f := thetaCuspSourceTerm_pos_of_pos_of_nat_pos hx (by norm_num : 0 < (1 : ℕ))
  have hδ : 0 < δ := by unfold δ thetaCuspDeepTailErrorScale; positivity
  obtain ⟨h1,h2,h3,h4,h5⟩ := thetaCuspFirstAtomScaledEvenJet_bounds_middle hq0 hq1
  have he := abs_thetaCuspNativeReflectionJet_sub_two_le_middle (n := 10) (by norm_num) hq0
  have b1 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 1) hx h1
  have t1 := mul_le_mul_of_nonneg_right b1
    (show 0 ≤ 2*(16*q)^(8 : ℕ)*δ+(22*q)^(8 : ℕ)*δ/50+5*(32*q)^(8 : ℕ)*δ^(2 : ℕ) by positivity)
  have b2 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 2) hx h2
  have t2 := mul_le_mul_of_nonneg_right b2
    (show 0 ≤ 2*(16*q)^(6 : ℕ)*δ+(22*q)^(6 : ℕ)*δ/50+5*(32*q)^(6 : ℕ)*δ^(2 : ℕ) by positivity)
  have b3 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 3) hx h3
  have t3 := mul_le_mul_of_nonneg_right b3
    (show 0 ≤ 2*(16*q)^(4 : ℕ)*δ+(22*q)^(4 : ℕ)*δ/50+5*(32*q)^(4 : ℕ)*δ^(2 : ℕ) by positivity)
  have b4 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 4) hx h4
  have t4 := mul_le_mul_of_nonneg_right b4
    (show 0 ≤ 2*(16*q)^(2 : ℕ)*δ+(22*q)^(2 : ℕ)*δ/50+5*(32*q)^(2 : ℕ)*δ^(2 : ℕ) by positivity)
  have b5 := thetaCuspFirstAtomReflectionJet_le_of_scaled (k := 5) hx h5
  have t5 := mul_le_mul_of_nonneg_right b5
    (show 0 ≤ 2*(16*q)^(0 : ℕ)*δ+(22*q)^(0 : ℕ)*δ/50+5*(32*q)^(0 : ℕ)*δ^(2 : ℕ) by positivity)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 1) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 3) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 5) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 7) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_odd_zero (n := 9) (by norm_num) x,
    thetaCuspFirstAtomReflectionJet_zero, abs_of_nonneg (sq_nonneg (thetaCuspSourceTerm x 1)),
    abs_zero, mul_zero, zero_mul, add_zero, zero_add] at he
  norm_num only [Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at he
  have hb : |thetaCuspNativeReflectionJet 10 x-thetaCuspTwoAtomReflectionJet 10 x| ≤
      f^(2 : ℕ)*q^(5 : ℕ)*((1 : ℝ)*q^(5 : ℕ)*(2*(1099511627776 : ℝ)*δ+(26559922791424 : ℝ)*δ/50+5*(1125899906842624 : ℝ)*δ^(2 : ℕ)) + (495 : ℝ)*q^(4 : ℕ)*(2*(4294967296 : ℝ)*δ+(54875873536 : ℝ)*δ/50+5*(1099511627776 : ℝ)*δ^(2 : ℕ)) + (65100 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (2940000 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (36000000 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (55000000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ))) := by
    dsimp [q, f, δ] at *
    nlinarith only [he, t1, t2, t3, t4, t5]
  rw [thetaCuspNativeScaledEvenJet_two_error_eq 5 hx]
  norm_num only [Nat.reduceMul]
  apply (div_le_iff₀ (by positivity : 0 < f^(2 : ℕ)*q^(5 : ℕ))).mpr
  have hw : (1 : ℝ)*q^(5 : ℕ)*(2*(1099511627776 : ℝ)*δ+(26559922791424 : ℝ)*δ/50+5*(1125899906842624 : ℝ)*δ^(2 : ℕ)) + (495 : ℝ)*q^(4 : ℕ)*(2*(4294967296 : ℝ)*δ+(54875873536 : ℝ)*δ/50+5*(1099511627776 : ℝ)*δ^(2 : ℕ)) + (65100 : ℝ)*q^(3 : ℕ)*(2*(16777216 : ℝ)*δ+(113379904 : ℝ)*δ/50+5*(1073741824 : ℝ)*δ^(2 : ℕ)) + (2940000 : ℝ)*q^(2 : ℕ)*(2*(65536 : ℝ)*δ+(234256 : ℝ)*δ/50+5*(1048576 : ℝ)*δ^(2 : ℕ)) + (36000000 : ℝ)*q^(1 : ℕ)*(2*(256 : ℝ)*δ+(484 : ℝ)*δ/50+5*(1024 : ℝ)*δ^(2 : ℕ)) + (55000000 : ℝ)*q^(0 : ℕ)*(2*(1 : ℝ)*δ+(1 : ℝ)*δ/50+5*(1 : ℝ)*δ^(2 : ℕ)) ≤ (175000 : ℝ) := by
    have p0 := thetaCuspDeepTailErrorScale_weighted_middle (k := 0) (by norm_num) hq0
    have s0 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 0) (by norm_num) hq0
    have p1 := thetaCuspDeepTailErrorScale_weighted_middle (k := 1) (by norm_num) hq0
    have s1 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 1) (by norm_num) hq0
    have p2 := thetaCuspDeepTailErrorScale_weighted_middle (k := 2) (by norm_num) hq0
    have s2 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 2) (by norm_num) hq0
    have p3 := thetaCuspDeepTailErrorScale_weighted_middle (k := 3) (by norm_num) hq0
    have s3 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 3) (by norm_num) hq0
    have p4 := thetaCuspDeepTailErrorScale_weighted_middle (k := 4) (by norm_num) hq0
    have s4 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 4) (by norm_num) hq0
    have p5 := thetaCuspDeepTailErrorScale_weighted_middle (k := 5) (by norm_num) hq0
    have s5 := thetaCuspDeepTailErrorScale_sq_weighted_middle (k := 5) (by norm_num) hq0
    dsimp [q, δ]
    nlinarith only [p0, s0, p1, s1, p2, s2, p3, s3, p4, s4, p5, s5]
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ f^(2 : ℕ)*q^(5 : ℕ))
  change |thetaCuspNativeReflectionJet 10 x-thetaCuspTwoAtomReflectionJet 10 x| ≤
    (175000 : ℝ)*(f^(2 : ℕ)*q^(5 : ℕ))
  nlinarith only [hb, hm]

end
end RHTower
