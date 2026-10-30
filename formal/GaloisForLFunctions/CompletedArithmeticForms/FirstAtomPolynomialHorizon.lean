import GaloisForLFunctions.CompletedArithmeticForms.GaussianScalePolynomial

/-!
# Quadratic order horizons for physical first-atom moments

The exact positive coefficient envelope has a rational majorant with quadratic
order cost. Its lower-degree terms pay the nonlinear clock error of the actual
first theta atom, retaining both the source amplitude and its affine factor.
-/

noncomputable section

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.ThetaCuspGaussianLimit

theorem gaussianMoment_positive (k : ℕ) : 0 < gaussianMoment k := by
  induction k with
  | zero => simp [gaussianMoment]
  | succ k ih => rw [gaussianMoment_successor]; positivity

/-- A rational majorant follows from the exact positive triangular generator. -/
theorem positiveGaussianScalePolynomial_weighted_bound (k : ℕ) {q : ℝ}
    (hq : 0 < q) (horder : (k : ℝ) ^ 2 ≤ q) :
    (8 * q - (k : ℝ) * ((k : ℝ) - 1)) *
      (positiveGaussianScalePolynomial k).eval q ≤
        8 * q * gaussianMoment k * q ^ k := by
  induction k generalizing q with
  | zero => simp [positiveGaussianScalePolynomial, gaussianMoment]
  | succ k ih =>
    push_cast at horder ⊢
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hsmall : (k : ℝ) ^ 2 ≤ q := by nlinarith only [horder, hk]
    have hprev := ih hq hsmall
    have hstep := positiveGaussianScalePolynomial_eval_succ_le k hq.le
    have hP := positiveGaussianScalePolynomial_eval_nonneg k hq.le
    have hd : 0 ≤ 8 * q - ((k : ℝ) + 1) * (k : ℝ) := by
      nlinarith only [horder, hk, sq_nonneg (k : ℝ)]
    have hcost :
        (8 * q * (2 * (k : ℝ) + 1) + 4 * (k : ℝ) ^ 2) *
            (8 * q - ((k : ℝ) + 1) * (k : ℝ)) ≤
          8 * q * (2 * (k : ℝ) + 1) *
            (8 * q - (k : ℝ) * ((k : ℝ) - 1)) := by
      have h : 0 ≤ 16 * q * (k : ℝ) + 4 * (k : ℝ) ^ 3 * ((k : ℝ) + 1) := by
        positivity
      nlinarith only [h]
    calc
      _ = (8 * q - ((k : ℝ) + 1) * (k : ℝ)) *
          (positiveGaussianScalePolynomial (k + 1)).eval q := by ring
      _ ≤ (8 * q - ((k : ℝ) + 1) * (k : ℝ)) *
          ((8 * q * (2 * (k : ℝ) + 1) + 4 * (k : ℝ) ^ 2) *
            (positiveGaussianScalePolynomial k).eval q) :=
        mul_le_mul_of_nonneg_left hstep hd
      _ ≤ (8 * q * (2 * (k : ℝ) + 1)) *
          ((8 * q - (k : ℝ) * ((k : ℝ) - 1)) *
            (positiveGaussianScalePolynomial k).eval q) := by
        nlinarith only [mul_le_mul_of_nonneg_right hcost hP]
      _ ≤ (8 * q * (2 * (k : ℝ) + 1)) *
          (8 * q * gaussianMoment k * q ^ k) :=
        mul_le_mul_of_nonneg_left hprev (by positivity)
      _ = 8 * q * gaussianMoment (k + 1) * q ^ (k + 1) := by
        rw [gaussianMoment_successor, pow_succ]
        ring

/-- On the quadratic source scale the entire envelope is at most eight sevenths of its top term. -/
theorem positiveGaussianScalePolynomial_seven_mul_le (k : ℕ) {q : ℝ}
    (hq : 0 < q) (horder : (k : ℝ) ^ 2 ≤ q) :
    7 * (positiveGaussianScalePolynomial k).eval q ≤
      8 * gaussianMoment k * q ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hP := positiveGaussianScalePolynomial_eval_nonneg k hq.le
  have hweighted := positiveGaussianScalePolynomial_weighted_bound k hq horder
  have hd : 7 * q ≤ 8 * q - (k : ℝ) * ((k : ℝ) - 1) := by
    nlinarith only [horder, hk]
  have hpaid := mul_le_mul_of_nonneg_right hd hP
  have he : q * (7 * (positiveGaussianScalePolynomial k).eval q) ≤
      q * (8 * gaussianMoment k * q ^ k) := by
    nlinarith only [hpaid, hweighted]
  exact (mul_le_mul_iff_right₀ hq).mp (by simpa only [mul_comm q] using he)

/-- The lower-degree error has quadratic order cost relative to the Gaussian leading term. -/
theorem positiveGaussianScalePolynomial_remainder_le (k : ℕ) {q : ℝ}
    (hq : 0 < q) (horder : (k : ℝ) ^ 2 ≤ q) :
    7 * q * ((positiveGaussianScalePolynomial k).eval q - gaussianMoment k * q ^ k) ≤
      (k : ℝ) ^ 2 * gaussianMoment k * q ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hP := positiveGaussianScalePolynomial_eval_nonneg k hq.le
  have hw := positiveGaussianScalePolynomial_weighted_bound k hq horder
  have hseven := positiveGaussianScalePolynomial_seven_mul_le k hq horder
  have hdegree := mul_nonneg hk hP
  have htop := mul_le_mul_of_nonneg_left hseven (sq_nonneg (k : ℝ))
  nlinarith only [hw, hdegree, htop]

/-- Every admitted physical first-atom moment retains six sevenths of its clocked leading term. -/
theorem firstAtom_signed_moment_six_sevenths_le (k : ℕ) {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    (6 / 7 : ℝ) * firstAtomClockAmplitude x *
        (firstAtomClockShape x + 6 * (k : ℝ)) * gaussianMoment k *
          thetaCuspSingleAtomReflectionScale 1 x ^ k ≤
      (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let B := firstAtomClockShape x
  let A := firstAtomClockAmplitude x
  have hq : 0 < q := by dsimp [q]; linarith only [hscale]
  have hB : 0 ≤ B := sq_nonneg _
  have hA : 0 ≤ A := (firstAtomClockAmplitude_pos x).le
  have hfactor : 0 ≤ A * (B + 6 * (k : ℝ)) := by positivity
  have hseven := positiveGaussianScalePolynomial_seven_mul_le k hq horder
  have hpaid := mul_le_mul_of_nonneg_left hseven hfactor
  have herr := (abs_le.mp (firstAtomSignedMoment_polynomial_error_le k x)).1
  change -(A * (B + 6 * (k : ℝ)) *
      ((positiveGaussianScalePolynomial k).eval q - gaussianMoment k * q ^ k)) ≤
    (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x -
      A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k at herr
  change (6 / 7 : ℝ) * A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k ≤ _
  nlinarith only [hpaid, herr]

theorem firstAtom_signed_moment_pos_of_quadratic_scale (k : ℕ) {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x := by
  have hq : 0 < thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hscale]
  have hB : 0 < firstAtomClockShape x := by
    unfold firstAtomClockShape
    exact sq_pos_of_pos (by linarith only [hscale])
  have hA := firstAtomClockAmplitude_pos x
  have hgamma := gaussianMoment_positive k
  exact lt_of_lt_of_le (by positivity) (firstAtom_signed_moment_six_sevenths_le k hscale horder)

/-- The least negative physical moment lies beyond the quadratic source horizon. -/
theorem firstAtomNegativeOrder_gt_of_quadratic_scale (K : ℕ) {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : (K : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    K < firstAtomNegativeOrder x := by
  by_contra h
  have hle : firstAtomNegativeOrder x ≤ K := le_of_not_gt h
  have hcast : (firstAtomNegativeOrder x : ℝ) ≤ K := by exact_mod_cast hle
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (firstAtomNegativeOrder x)) hcast 2
  have hp := firstAtom_signed_moment_pos_of_quadratic_scale
    (firstAtomNegativeOrder x) hscale (hsq.trans horder)
  exact not_lt_of_ge hp.le (firstAtomNegativeOrder_spec x)

/-- The physical source is close to its exact affine-Gamma clock in its own mass coordinates. -/
theorem firstAtomScaledEvenJet_clock_error_le (k : ℕ) {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspFirstAtomScaledEvenJet k x -
        gaussianMoment k * (1 + 6 * (k : ℝ) / firstAtomClockShape x)| ≤
      (1 + 6 * (k : ℝ) / firstAtomClockShape x) *
        ((k : ℝ) ^ 2 / (7 * thetaCuspSingleAtomReflectionScale 1 x)) * gaussianMoment k := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let B := firstAtomClockShape x
  let A := firstAtomClockAmplitude x
  have hq : 0 < q := by dsimp [q]; linarith only [hscale]
  have hB : 0 < B := by
    unfold B firstAtomClockShape
    exact sq_pos_of_pos (by linarith only [hscale])
  have hA : 0 < A := firstAtomClockAmplitude_pos x
  have hmass : thetaCuspSourceTerm x 1 ^ 2 = A * B := firstAtom_mass_eq x
  have hden : 0 < A * B * q ^ k := by positivity
  have hfactor : 0 ≤ A * (B + 6 * (k : ℝ)) := by positivity
  have hrem : (positiveGaussianScalePolynomial k).eval q - gaussianMoment k * q ^ k ≤
      ((k : ℝ) ^ 2 * gaussianMoment k * q ^ k) / (7 * q) := by
    apply (le_div_iff₀ (by positivity : 0 < 7 * q)).mpr
    nlinarith only [positiveGaussianScalePolynomial_remainder_le k hq horder]
  have he : |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k *
        (1 + 6 * (k : ℝ) / B)| =
      |(-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x -
        A * (B + 6 * (k : ℝ)) * gaussianMoment k * q ^ k| / (A * B * q ^ k) := by
    rw [← abs_of_pos hden, ← _root_.abs_div]
    congr 1
    change (-1 : ℝ) ^ k * thetaCuspFirstAtomReflectionJet (2 * k) x /
      (thetaCuspSourceTerm x 1 ^ 2 * q ^ k) - _ = _
    rw [hmass]
    field_simp
  change |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k *
      (1 + 6 * (k : ℝ) / B)| ≤ _
  rw [he]
  calc
    _ ≤ (A * (B + 6 * (k : ℝ)) *
        ((positiveGaussianScalePolynomial k).eval q - gaussianMoment k * q ^ k)) /
          (A * B * q ^ k) :=
      div_le_div_of_nonneg_right (firstAtomSignedMoment_polynomial_error_le k x) hden.le
    _ ≤ (A * (B + 6 * (k : ℝ)) *
        (((k : ℝ) ^ 2 * gaussianMoment k * q ^ k) / (7 * q))) /
          (A * B * q ^ k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrem hfactor) hden.le
    _ = _ := by
      change _ = (1 + 6 * (k : ℝ) / B) * ((k : ℝ) ^ 2 / (7 * q)) * gaussianMoment k
      field_simp

/-- Quadratic order replaces factorial order in the normalized physical Gaussian error. -/
theorem firstAtomScaledEvenJet_quadratic_error_le (k : ℕ) {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (horder : (k : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k| ≤
      3 * (k : ℝ) ^ 2 * gaussianMoment k / thetaCuspSingleAtomReflectionScale 1 x := by
  let q := thetaCuspSingleAtomReflectionScale 1 x
  let B := firstAtomClockShape x
  have hq3 : 3 ≤ q := hscale
  have hq : 0 < q := by linarith only [hq3]
  have hB : 0 < B := by
    unfold B firstAtomClockShape
    exact sq_pos_of_pos (by linarith only [hscale])
  have hBsq : q ^ 2 ≤ B := by
    change q ^ 2 ≤ (2 * q - 3) ^ 2
    nlinarith only [mul_nonneg (sub_nonneg.mpr hq3)
      (show 0 ≤ 3 * q - 3 by linarith only [hq3])]
  have hB3 : 3 * q ≤ B := by
    nlinarith only [hBsq, mul_nonneg hq.le (sub_nonneg.mpr hq3)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk2 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    by_cases hk0 : k = 0
    · subst k
      norm_num
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      nlinarith only [h1, sq_nonneg ((k : ℝ) - 1)]
  have hratio : 6 * (k : ℝ) / B ≤ 2 * ((k : ℝ) ^ 2 / q) := by
    rw [← mul_div_assoc (2 : ℝ) ((k : ℝ) ^ 2) q]
    apply (div_le_div_iff₀ hB hq).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 6 * q by positivity),
      mul_le_mul_of_nonneg_left hB3 (show 0 ≤ 2 * (k : ℝ) ^ 2 by positivity)]
  have hr : (k : ℝ) ^ 2 / q ≤ 1 := (div_le_iff₀ hq).mpr (by simpa using horder)
  have hratio2 : 6 * (k : ℝ) / B ≤ 2 := by linarith only [hratio, hr]
  have hratio0 : 0 ≤ 6 * (k : ℝ) / B := by positivity
  have hg := (gaussianMoment_positive k).le
  have hc := firstAtomScaledEvenJet_clock_error_le k hscale horder
  change |thetaCuspFirstAtomScaledEvenJet k x - gaussianMoment k *
      (1 + 6 * (k : ℝ) / B)| ≤
    (1 + 6 * (k : ℝ) / B) * ((k : ℝ) ^ 2 / (7 * q)) * gaussianMoment k at hc
  have hfirst : (1 + 6 * (k : ℝ) / B) * ((k : ℝ) ^ 2 / (7 * q)) * gaussianMoment k ≤
      3 * ((k : ℝ) ^ 2 / (7 * q)) * gaussianMoment k :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith only [hratio2]) (by positivity)) hg
  have hsecond := mul_le_mul_of_nonneg_left hratio hg
  have he : |gaussianMoment k * (1 + 6 * (k : ℝ) / B) - gaussianMoment k| =
      gaussianMoment k * (6 * (k : ℝ) / B) := by
    rw [show gaussianMoment k * (1 + 6 * (k : ℝ) / B) - gaussianMoment k =
      gaussianMoment k * (6 * (k : ℝ) / B) by ring, abs_of_nonneg (mul_nonneg hg hratio0)]
  calc
    _ ≤ |thetaCuspFirstAtomScaledEvenJet k x -
        gaussianMoment k * (1 + 6 * (k : ℝ) / B)| +
        |gaussianMoment k * (1 + 6 * (k : ℝ) / B) - gaussianMoment k| := abs_sub_le _ _ _
    _ ≤ 3 * ((k : ℝ) ^ 2 / (7 * q)) * gaussianMoment k +
        2 * ((k : ℝ) ^ 2 / q) * gaussianMoment k := by
      rw [he]
      nlinarith only [hc.trans hfirst, hsecond]
    _ ≤ _ := by
      change _ ≤ 3 * (k : ℝ) ^ 2 * gaussianMoment k / q
      have hn : 0 ≤ (k : ℝ) ^ 2 * gaussianMoment k / q := by positivity
      calc
        _ = (17 / 7 : ℝ) * ((k : ℝ) ^ 2 * gaussianMoment k / q) := by
          field_simp
          norm_num
        _ ≤ 3 * ((k : ℝ) ^ 2 * gaussianMoment k / q) :=
          mul_le_mul_of_nonneg_right (by norm_num) hn
        _ = _ := by ring

/-- The negative order exceeds the square root of the physical source scale. -/
theorem sqrt_scale_lt_firstAtomNegativeOrder {x : ℝ}
    (hscale : 3 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    Real.sqrt (thetaCuspSingleAtomReflectionScale 1 x) < (firstAtomNegativeOrder x : ℝ) := by
  have hq : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith only [hscale]
  have hsq : thetaCuspSingleAtomReflectionScale 1 x < (firstAtomNegativeOrder x : ℝ) ^ 2 := by
    by_contra h
    have hp := firstAtom_signed_moment_pos_of_quadratic_scale
      (firstAtomNegativeOrder x) hscale (le_of_not_gt h)
    exact not_lt_of_ge hp.le (firstAtomNegativeOrder_spec x)
  have hn : (0 : ℝ) ≤ firstAtomNegativeOrder x := Nat.cast_nonneg _
  nlinarith only [hsq, hn, Real.sqrt_nonneg (thetaCuspSingleAtomReflectionScale 1 x),
    Real.sq_sqrt hq]

/-- Explicit center for the quadratic physical moment horizon. -/
def firstAtomPolynomialHorizon (K : ℕ) : ℝ :=
  max 0 (Real.log ((3 + (K : ℝ) ^ 2) / Real.pi) / 2)

theorem firstAtomNegativeOrder_gt_of_polynomial_horizon (K : ℕ) {x : ℝ}
    (hx : firstAtomPolynomialHorizon K ≤ x) : K < firstAtomNegativeOrder x := by
  have hA : 0 < 3 + (K : ℝ) ^ 2 := by positivity
  have hxlog : Real.log ((3 + (K : ℝ) ^ 2) / Real.pi) ≤ 2 * x := by
    have h := (le_max_right 0 (Real.log ((3 + (K : ℝ) ^ 2) / Real.pi) / 2)).trans hx
    linarith only [h]
  have he := Real.exp_le_exp.mpr hxlog
  rw [Real.exp_log (div_pos hA Real.pi_pos)] at he
  have hm := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  have hq : 3 + (K : ℝ) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x := by
    simpa only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one,
      mul_div_cancel₀ _ Real.pi_ne_zero] using hm
  exact firstAtomNegativeOrder_gt_of_quadratic_scale K
    (by nlinarith only [hq, sq_nonneg (K : ℝ)]) (by linarith only [hq])

#print axioms positiveGaussianScalePolynomial_weighted_bound
#print axioms positiveGaussianScalePolynomial_remainder_le
#print axioms firstAtom_signed_moment_six_sevenths_le
#print axioms firstAtomNegativeOrder_gt_of_quadratic_scale
#print axioms firstAtomScaledEvenJet_clock_error_le
#print axioms firstAtomScaledEvenJet_quadratic_error_le
#print axioms sqrt_scale_lt_firstAtomNegativeOrder
#print axioms firstAtomNegativeOrder_gt_of_polynomial_horizon

end GaloisForLFunctions.CompletedArithmeticForms
