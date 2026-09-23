import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomScalePolynomials
import GaloisForLFunctions.HTGeometry.TwoAtomOddAlgebra

/-! # Literal-source incidence of the exact two-atom odd rational profiles -/
open Polynomial
namespace RHTower
noncomputable section
set_option maxHeartbeats 2500000

private theorem firstPoly0 : thetaCuspFirstAtomJetPolynomial 0 =
  C (-6) * X^(1 : ℕ) +
    C 4 * X^(2 : ℕ) := by
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetPolynomial]
  ring

private theorem firstPoly1 : thetaCuspFirstAtomJetPolynomial 1 =
  C (-15) * X^(1 : ℕ) +
    C 30 * X^(2 : ℕ) +
    C (-8) * X^(3 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 1 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 0) from rfl, firstPoly0]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly2 : thetaCuspFirstAtomJetPolynomial 2 =
  C (-75/2) * X^(1 : ℕ) +
    C 165 * X^(2 : ℕ) +
    C (-112) * X^(3 : ℕ) +
    C 16 * X^(4 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 2 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 1) from rfl, firstPoly1]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly3 : thetaCuspFirstAtomJetPolynomial 3 =
  C (-375/4) * X^(1 : ℕ) +
    C (1635/2) * X^(2 : ℕ) +
    C (-1058) * X^(3 : ℕ) +
    C 360 * X^(4 : ℕ) +
    C (-32) * X^(5 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 3 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 2) from rfl, firstPoly2]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly4 : thetaCuspFirstAtomJetPolynomial 4 =
  C (-1875/8) * X^(1 : ℕ) +
    C (15465/4) * X^(2 : ℕ) +
    C (-8512) * X^(3 : ℕ) +
    C 5176 * X^(4 : ℕ) +
    C (-1056) * X^(5 : ℕ) +
    C 64 * X^(6 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 4 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 3) from rfl, firstPoly3]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly5 : thetaCuspFirstAtomJetPolynomial 5 =
  C (-9375/16) * X^(1 : ℕ) +
    C (142935/8) * X^(2 : ℕ) +
    C (-126121/2) * X^(3 : ℕ) +
    C 61020 * X^(4 : ℕ) +
    C (-21440) * X^(5 : ℕ) +
    C 2912 * X^(6 : ℕ) +
    C (-128) * X^(7 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 5 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 4) from rfl, firstPoly4]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly6 : thetaCuspFirstAtomJetPolynomial 6 =
  C (-46875/32) * X^(1 : ℕ) +
    C (1305165/16) * X^(2 : ℕ) +
    C (-445627) * X^(3 : ℕ) +
    C 644791 * X^(4 : ℕ) +
    C (-347160) * X^(5 : ℕ) +
    C 79280 * X^(6 : ℕ) +
    C (-7680) * X^(7 : ℕ) +
    C 256 * X^(8 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 6 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 5) from rfl, firstPoly5]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly7 : thetaCuspFirstAtomJetPolynomial 7 =
  C (-234375/64) * X^(1 : ℕ) +
    C (11840235/32) * X^(2 : ℕ) +
    C (-24477769/8) * X^(3 : ℕ) +
    C (12743955/2) * X^(4 : ℕ) +
    C (-4934762) * X^(5 : ℕ) +
    C 1685320 * X^(6 : ℕ) +
    C (-269920) * X^(7 : ℕ) +
    C 19584 * X^(8 : ℕ) +
    C (-512) * X^(9 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 7 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 6) from rfl, firstPoly6]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly8 : thetaCuspFirstAtomJetPolynomial 8 =
  C (-1171875/128) * X^(1 : ℕ) +
    C (107030865/64) * X^(2 : ℕ) +
    C (-20628202) * X^(3 : ℕ) +
    C 60281251 * X^(4 : ℕ) +
    C (-64558956) * X^(5 : ℕ) +
    C 30936024 * X^(6 : ℕ) +
    C (-7284480) * X^(7 : ℕ) +
    C 862976 * X^(8 : ℕ) +
    C (-48640) * X^(9 : ℕ) +
    C 1024 * X^(10 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 8 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 7) from rfl, firstPoly7]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly9 : thetaCuspFirstAtomJetPolynomial 9 =
  C (-5859375/256) * X^(1 : ℕ) +
    C (965621535/128) * X^(2 : ℕ) +
    C (-4397696881/32) * X^(3 : ℕ) +
    C (1107294075/2) * X^(4 : ℕ) +
    C (-798431540) * X^(5 : ℕ) +
    C 515818212 * X^(6 : ℕ) +
    C (-167497008) * X^(7 : ℕ) +
    C 28808064 * X^(8 : ℕ) +
    C (-2625792) * X^(9 : ℕ) +
    C 118272 * X^(10 : ℕ) +
    C (-2048) * X^(11 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 9 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 8) from rfl, firstPoly8]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem firstPoly10 : thetaCuspFirstAtomJetPolynomial 10 =
  C (-29296875/512) * X^(1 : ℕ) +
    C (8702312565/256) * X^(2 : ℕ) +
    C (-14533920247/16) * X^(3 : ℕ) +
    C (79693693981/16) * X^(4 : ℕ) +
    C (-9490825245) * X^(5 : ℕ) +
    C 8044590730 * X^(6 : ℕ) +
    C (-3460343040) * X^(7 : ℕ) +
    C 810327072 * X^(8 : ℕ) +
    C (-106193280) * X^(9 : ℕ) +
    C 7676160 * X^(10 : ℕ) +
    C (-282624) * X^(11 : ℕ) +
    C 4096 * X^(12 : ℕ) := by
  rw [show thetaCuspFirstAtomJetPolynomial 10 =
    thetaCuspFirstAtomJetStep (thetaCuspFirstAtomJetPolynomial 9) from rfl, firstPoly9]
  apply Polynomial.funext
  intro q
  norm_num [thetaCuspFirstAtomJetStep, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X]
  ring

/-- Exact unnormalized reflected polynomial at order 2. -/
theorem thetaCuspTwoAtomScaleReflectionJet_2_eq (q z : ℝ) :
    thetaCuspTwoAtomScaleReflectionJet 2 q z =
      -4*q^(3 : ℕ)*HTGeometry.twoAtomOddNumerator1 q z := by
  unfold thetaCuspTwoAtomScaleReflectionJet thetaCuspTwoAtomScaleSourceJet
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, Nat.cast_ofNat]
  rw [firstPoly0, firstPoly1, firstPoly2]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddNumerator1
  ring

/-- The literal retained normalized entry 1 equals its exact rational polynomial profile. -/
theorem thetaCuspTwoAtomScaledEvenJet_1_eq_profile {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomScaledEvenJet 1 x =
      HTGeometry.twoAtomOddProfile1 (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [thetaCuspTwoAtomScaledEvenJet_eq_scale]
  norm_num only [Nat.reduceMul]
  rw [thetaCuspTwoAtomScaleReflectionJet_2_eq]
  norm_num only [thetaCuspFirstAtomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddProfile1
  have hdp : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x-3 := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x =
    2*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3) by ring]
  field_simp [hqp.ne', hdp.ne']
  <;> ring

/-- Exact unnormalized reflected polynomial at order 4. -/
theorem thetaCuspTwoAtomScaleReflectionJet_4_eq (q z : ℝ) :
    thetaCuspTwoAtomScaleReflectionJet 4 q z =
      4*q^(3 : ℕ)*HTGeometry.twoAtomOddNumerator2 q z := by
  unfold thetaCuspTwoAtomScaleReflectionJet thetaCuspTwoAtomScaleSourceJet
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, Nat.cast_ofNat]
  rw [firstPoly0, firstPoly1, firstPoly2, firstPoly3, firstPoly4]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddNumerator2
  ring

/-- The literal retained normalized entry 2 equals its exact rational polynomial profile. -/
theorem thetaCuspTwoAtomScaledEvenJet_2_eq_profile {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomScaledEvenJet 2 x =
      HTGeometry.twoAtomOddProfile2 (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [thetaCuspTwoAtomScaledEvenJet_eq_scale]
  norm_num only [Nat.reduceMul]
  rw [thetaCuspTwoAtomScaleReflectionJet_4_eq]
  norm_num only [thetaCuspFirstAtomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddProfile2
  have hdp : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x-3 := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x =
    2*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3) by ring]
  field_simp [hqp.ne', hdp.ne']
  <;> ring

/-- Exact unnormalized reflected polynomial at order 6. -/
theorem thetaCuspTwoAtomScaleReflectionJet_6_eq (q z : ℝ) :
    thetaCuspTwoAtomScaleReflectionJet 6 q z =
      -4*q^(3 : ℕ)*HTGeometry.twoAtomOddNumerator3 q z := by
  unfold thetaCuspTwoAtomScaleReflectionJet thetaCuspTwoAtomScaleSourceJet
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, Nat.cast_ofNat]
  rw [firstPoly0, firstPoly1, firstPoly2, firstPoly3, firstPoly4, firstPoly5, firstPoly6]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddNumerator3
  ring

/-- The literal retained normalized entry 3 equals its exact rational polynomial profile. -/
theorem thetaCuspTwoAtomScaledEvenJet_3_eq_profile {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomScaledEvenJet 3 x =
      HTGeometry.twoAtomOddProfile3 (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [thetaCuspTwoAtomScaledEvenJet_eq_scale]
  norm_num only [Nat.reduceMul]
  rw [thetaCuspTwoAtomScaleReflectionJet_6_eq]
  norm_num only [thetaCuspFirstAtomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddProfile3
  have hdp : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x-3 := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x =
    2*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3) by ring]
  field_simp [hqp.ne', hdp.ne']
  <;> ring

/-- Exact unnormalized reflected polynomial at order 8. -/
theorem thetaCuspTwoAtomScaleReflectionJet_8_eq (q z : ℝ) :
    thetaCuspTwoAtomScaleReflectionJet 8 q z =
      4*q^(3 : ℕ)*HTGeometry.twoAtomOddNumerator4 q z := by
  unfold thetaCuspTwoAtomScaleReflectionJet thetaCuspTwoAtomScaleSourceJet
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, Nat.cast_ofNat]
  rw [firstPoly0, firstPoly1, firstPoly2, firstPoly3, firstPoly4, firstPoly5, firstPoly6, firstPoly7, firstPoly8]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddNumerator4
  ring

/-- The literal retained normalized entry 4 equals its exact rational polynomial profile. -/
theorem thetaCuspTwoAtomScaledEvenJet_4_eq_profile {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomScaledEvenJet 4 x =
      HTGeometry.twoAtomOddProfile4 (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [thetaCuspTwoAtomScaledEvenJet_eq_scale]
  norm_num only [Nat.reduceMul]
  rw [thetaCuspTwoAtomScaleReflectionJet_8_eq]
  norm_num only [thetaCuspFirstAtomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddProfile4
  have hdp : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x-3 := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x =
    2*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3) by ring]
  field_simp [hqp.ne', hdp.ne']
  <;> ring

/-- Exact unnormalized reflected polynomial at order 10. -/
theorem thetaCuspTwoAtomScaleReflectionJet_10_eq (q z : ℝ) :
    thetaCuspTwoAtomScaleReflectionJet 10 q z =
      -4*q^(3 : ℕ)*HTGeometry.twoAtomOddNumerator5 q z := by
  unfold thetaCuspTwoAtomScaleReflectionJet thetaCuspTwoAtomScaleSourceJet
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.cast_one, Nat.cast_ofNat]
  rw [firstPoly0, firstPoly1, firstPoly2, firstPoly3, firstPoly4, firstPoly5, firstPoly6, firstPoly7, firstPoly8, firstPoly9, firstPoly10]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddNumerator5
  ring

/-- The literal retained normalized entry 5 equals its exact rational polynomial profile. -/
theorem thetaCuspTwoAtomScaledEvenJet_5_eq_profile {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomScaledEvenJet 5 x =
      HTGeometry.twoAtomOddProfile5 (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [thetaCuspTwoAtomScaledEvenJet_eq_scale]
  norm_num only [Nat.reduceMul]
  rw [thetaCuspTwoAtomScaleReflectionJet_10_eq]
  norm_num only [thetaCuspFirstAtomJetPolynomial, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  unfold HTGeometry.twoAtomOddProfile5
  have hdp : 0 < 2*thetaCuspSingleAtomReflectionScale 1 x-3 := by
    have := three_lt_thetaCuspSingleAtomReflectionScale (n := 1) (by norm_num) hx.le
    linarith
  rw [show 4*thetaCuspSingleAtomReflectionScale 1 x^(2 : ℕ)-6*thetaCuspSingleAtomReflectionScale 1 x =
    2*thetaCuspSingleAtomReflectionScale 1 x*(2*thetaCuspSingleAtomReflectionScale 1 x-3) by ring]
  field_simp [hqp.ne', hdp.ne']
  <;> ring

end
end RHTower
