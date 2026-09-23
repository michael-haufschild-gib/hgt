import GaloisForLFunctions.RHTower.ThetaCuspMiddleLikelihoodBounds

/-! # All second-atom spectral moments and a uniform order-ten middle bound -/
open MeasureTheory Filter Topology Polynomial
namespace RHTower
noncomputable section
set_option maxHeartbeats 2000000

/-- Exact polynomial numerator of every second-atom tilted moment. -/
def thetaCuspSecondMomentNumerator : ℕ → ℝ[X]
  | 0 => C 18+C 16*X
  | n+1 => (C 3*X+C (n+1 : ℝ))*thetaCuspSecondMomentNumerator n-
    X*(thetaCuspSecondMomentNumerator n).derivative

/-- All-order polynomial-exponential moment profile for the literal second atom. -/
def thetaCuspSecondMomentProfile (n : ℕ) (B : ℝ) : ℝ :=
  Real.exp (-(9/2 : ℝ))*(Real.exp (-3*B)*(thetaCuspSecondMomentNumerator n).eval B/B^(n+1))

private theorem second_profile_deriv (n : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (thetaCuspSecondMomentProfile n) (-thetaCuspSecondMomentProfile (n+1) B) B := by
  have h := expProfile_hasDerivAt (fun q => (thetaCuspSecondMomentNumerator n).hasDerivAt q) n hB
  have he : thetaCuspSecondMomentProfile n =
      fun q => Real.exp (-(9/2 : ℝ))*(Real.exp (-3*q)*((thetaCuspSecondMomentNumerator n).eval q/q^(n+1))) := by
    funext q
    unfold thetaCuspSecondMomentProfile
    ring
  rw [he]
  apply h.congr_deriv
  simp only [thetaCuspSecondMomentProfile, thetaCuspSecondMomentNumerator,
    eval_sub, eval_add, eval_mul, eval_C, eval_X]
  field_simp
  ring

/-- Every second-atom moment is its exact rational-exponential profile, at every positive tilt. -/
theorem thetaCuspSecondAtomMoment_eq_allOrderProfile (n : ℕ) {B : ℝ} (hB : 0 < B) :
    thetaCuspSecondAtomMoment B n = thetaCuspSecondMomentProfile n B := by
  induction n generalizing B with
  | zero =>
    rw [thetaCuspSecondAtomMoment_zero hB]
    unfold secondAtomMomentProfile secondAtomProfile secondAtomNumerator0
      thetaCuspSecondMomentProfile thetaCuspSecondMomentNumerator
    simp only [eval_add, eval_mul, eval_C, eval_X]
    ring
  | succ n ih =>
    have h1 := hasDerivAt_thetaCuspSecondAtomMoment n hB
    have h2 : HasDerivAt (fun q => thetaCuspSecondAtomMoment q n)
        (-thetaCuspSecondMomentProfile (n+1) B) B :=
      (second_profile_deriv n hB).congr_of_eventuallyEq (by
        filter_upwards [Ioi_mem_nhds hB] with q hq
        exact ih hq)
    exact neg_injective (h1.unique h2)

private theorem second_num_0 : thetaCuspSecondMomentNumerator 0 =
  C (18)*X^(0 : ℕ) +
    C (16)*X^(1 : ℕ) := by
  simp only [thetaCuspSecondMomentNumerator]
  ring

private theorem second_num_1 : thetaCuspSecondMomentNumerator 1 =
  C (18)*X^(0 : ℕ) +
    C (54)*X^(1 : ℕ) +
    C (48)*X^(2 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 1 =
    (C 3*X+C (1 : ℝ))*thetaCuspSecondMomentNumerator 0-
      X*(thetaCuspSecondMomentNumerator 0).derivative from by norm_num [thetaCuspSecondMomentNumerator], second_num_0]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_2 : thetaCuspSecondMomentNumerator 2 =
  C (36)*X^(0 : ℕ) +
    C (108)*X^(1 : ℕ) +
    C (162)*X^(2 : ℕ) +
    C (144)*X^(3 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 2 =
    (C 3*X+C (2 : ℝ))*thetaCuspSecondMomentNumerator 1-
      X*(thetaCuspSecondMomentNumerator 1).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_1]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_3 : thetaCuspSecondMomentNumerator 3 =
  C (108)*X^(0 : ℕ) +
    C (324)*X^(1 : ℕ) +
    C (486)*X^(2 : ℕ) +
    C (486)*X^(3 : ℕ) +
    C (432)*X^(4 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 3 =
    (C 3*X+C (3 : ℝ))*thetaCuspSecondMomentNumerator 2-
      X*(thetaCuspSecondMomentNumerator 2).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_2]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_4 : thetaCuspSecondMomentNumerator 4 =
  C (432)*X^(0 : ℕ) +
    C (1296)*X^(1 : ℕ) +
    C (1944)*X^(2 : ℕ) +
    C (1944)*X^(3 : ℕ) +
    C (1458)*X^(4 : ℕ) +
    C (1296)*X^(5 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 4 =
    (C 3*X+C (4 : ℝ))*thetaCuspSecondMomentNumerator 3-
      X*(thetaCuspSecondMomentNumerator 3).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_3]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_5 : thetaCuspSecondMomentNumerator 5 =
  C (2160)*X^(0 : ℕ) +
    C (6480)*X^(1 : ℕ) +
    C (9720)*X^(2 : ℕ) +
    C (9720)*X^(3 : ℕ) +
    C (7290)*X^(4 : ℕ) +
    C (4374)*X^(5 : ℕ) +
    C (3888)*X^(6 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 5 =
    (C 3*X+C (5 : ℝ))*thetaCuspSecondMomentNumerator 4-
      X*(thetaCuspSecondMomentNumerator 4).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_4]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_6 : thetaCuspSecondMomentNumerator 6 =
  C (12960)*X^(0 : ℕ) +
    C (38880)*X^(1 : ℕ) +
    C (58320)*X^(2 : ℕ) +
    C (58320)*X^(3 : ℕ) +
    C (43740)*X^(4 : ℕ) +
    C (26244)*X^(5 : ℕ) +
    C (13122)*X^(6 : ℕ) +
    C (11664)*X^(7 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 6 =
    (C 3*X+C (6 : ℝ))*thetaCuspSecondMomentNumerator 5-
      X*(thetaCuspSecondMomentNumerator 5).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_5]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_7 : thetaCuspSecondMomentNumerator 7 =
  C (90720)*X^(0 : ℕ) +
    C (272160)*X^(1 : ℕ) +
    C (408240)*X^(2 : ℕ) +
    C (408240)*X^(3 : ℕ) +
    C (306180)*X^(4 : ℕ) +
    C (183708)*X^(5 : ℕ) +
    C (91854)*X^(6 : ℕ) +
    C (39366)*X^(7 : ℕ) +
    C (34992)*X^(8 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 7 =
    (C 3*X+C (7 : ℝ))*thetaCuspSecondMomentNumerator 6-
      X*(thetaCuspSecondMomentNumerator 6).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_6]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_8 : thetaCuspSecondMomentNumerator 8 =
  C (725760)*X^(0 : ℕ) +
    C (2177280)*X^(1 : ℕ) +
    C (3265920)*X^(2 : ℕ) +
    C (3265920)*X^(3 : ℕ) +
    C (2449440)*X^(4 : ℕ) +
    C (1469664)*X^(5 : ℕ) +
    C (734832)*X^(6 : ℕ) +
    C (314928)*X^(7 : ℕ) +
    C (118098)*X^(8 : ℕ) +
    C (104976)*X^(9 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 8 =
    (C 3*X+C (8 : ℝ))*thetaCuspSecondMomentNumerator 7-
      X*(thetaCuspSecondMomentNumerator 7).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_7]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_9 : thetaCuspSecondMomentNumerator 9 =
  C (6531840)*X^(0 : ℕ) +
    C (19595520)*X^(1 : ℕ) +
    C (29393280)*X^(2 : ℕ) +
    C (29393280)*X^(3 : ℕ) +
    C (22044960)*X^(4 : ℕ) +
    C (13226976)*X^(5 : ℕ) +
    C (6613488)*X^(6 : ℕ) +
    C (2834352)*X^(7 : ℕ) +
    C (1062882)*X^(8 : ℕ) +
    C (354294)*X^(9 : ℕ) +
    C (314928)*X^(10 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 9 =
    (C 3*X+C (9 : ℝ))*thetaCuspSecondMomentNumerator 8-
      X*(thetaCuspSecondMomentNumerator 8).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_8]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem second_num_10 : thetaCuspSecondMomentNumerator 10 =
  C (65318400)*X^(0 : ℕ) +
    C (195955200)*X^(1 : ℕ) +
    C (293932800)*X^(2 : ℕ) +
    C (293932800)*X^(3 : ℕ) +
    C (220449600)*X^(4 : ℕ) +
    C (132269760)*X^(5 : ℕ) +
    C (66134880)*X^(6 : ℕ) +
    C (28343520)*X^(7 : ℕ) +
    C (10628820)*X^(8 : ℕ) +
    C (3542940)*X^(9 : ℕ) +
    C (1062882)*X^(10 : ℕ) +
    C (944784)*X^(11 : ℕ) := by
  rw [show thetaCuspSecondMomentNumerator 10 =
    (C 3*X+C (10 : ℝ))*thetaCuspSecondMomentNumerator 9-
      X*(thetaCuspSecondMomentNumerator 9).derivative from by rw [thetaCuspSecondMomentNumerator]; norm_num, second_num_9]
  apply Polynomial.funext
  intro B
  norm_num [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_C, Polynomial.derivative_X]
  ring

private theorem exp_ten_half_lower : (30000 : ℝ) ≤ Real.exp (21/2) := by
  have h1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num) h1 10
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have ht : (3/2 : ℝ) ≤ Real.exp (1/2) := by linarith [Real.add_one_le_exp (1/2)]
  have hm := mul_le_mul hp ht (by norm_num : (0 : ℝ) ≤ 3/2) (Real.exp_pos 10).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith only [hm]

/-- The complete second-atom tenth moment has a symbolic rational endpoint ceiling. -/
theorem thetaCuspSecondAtomMoment_ten_at_two_le :
    thetaCuspSecondAtomMoment 2 10 ≤ (3 : ℝ)^(10 : ℕ)/100 := by
  rw [thetaCuspSecondAtomMoment_eq_allOrderProfile 10 (by norm_num)]
  unfold thetaCuspSecondMomentProfile
  rw [second_num_10]
  norm_num only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [show Real.exp (-(9/2 : ℝ))*(Real.exp (-6)*27163123200/2048) =
    Real.exp (-(21/2 : ℝ))*(27163123200/2048) by
      rw [show -(21/2 : ℝ) = -(9/2 : ℝ)+(-6) by norm_num, Real.exp_add]
      ring]
  rw [Real.exp_neg]
  have he := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 30000) exp_ten_half_lower
  norm_num only [one_div] at he
  nlinarith only [he]

end
end RHTower
