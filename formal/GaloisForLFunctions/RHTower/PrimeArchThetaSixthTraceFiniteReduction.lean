import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCurvatureFlow
import GaloisForLFunctions.RHTower.PrimeArchThetaThirdCumulantLikelihoodTailEnvelope

/-!
# Finite rational reduction of the completed sixth reciprocal trace

The exact-height damping of the higher theta atoms and their likelihood-ratio order remove the
infinite tail from the order-24 sixth-trace budget.  The completed bound

`normalizedPrimeArchMoment 2 < 3 / 10^7`

is reduced to five explicit rational enclosures for the first theta atom's first four raw even
moments.  No Xi-zero location or RH premise is used.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- The exact double-exponential higher-atom damping is at most `exp (-18x)`. -/
theorem thetaCuspHigherAtomExactHeightDamping_le_exp_neg_eighteen
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspHigherAtomExactHeightDamping x ≤ Real.exp (-18 * x) := by
  unfold thetaCuspHigherAtomExactHeightDamping
  apply Real.exp_le_exp.mpr
  have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
    simpa only [add_comm] using Real.add_one_le_exp (2 * x)
  nlinarith [Real.pi_gt_three]

/-- Rational pointwise higher-tail damping used only for the sixth-trace finite reduction. -/
theorem thetaCuspFullSource_sub_first_le_exp_neg_eighteen
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 ≤
      (8 / 2997 : ℝ) * Real.exp (-18 * x) * thetaCuspSourceTerm x 1 := by
  have h := thetaCuspFullSource_sub_first_le_exactHeight_rational hx
  have hdamp := thetaCuspHigherAtomExactHeightDamping_le_exp_neg_eighteen hx
  have hfirst : 0 ≤ thetaCuspSourceTerm x 1 := by
    rcases hx.eq_or_lt with rfl | hxpos
    · exact thetaCuspSourceTerm_one_zero_pos.le
    · exact thetaCuspSourceTerm_nonneg_of_pos hxpos 1
  calc
    _ ≤ (8 / 2997 : ℝ) * thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1 := h
    _ ≤ (8 / 2997 : ℝ) * Real.exp (-18 * x) * thetaCuspSourceTerm x 1 := by
      gcongr

/-- Elementary optimizer for `x^2 exp(-18x)`. -/
theorem sq_mul_exp_neg_eighteen_le
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-18 * x) ≤ Real.exp (-2) / 81 := by
  have ht := Real.add_one_le_exp (9 * x - 1)
  have hxexp : 9 * x * Real.exp (-9 * x) ≤ Real.exp (-1) := by
    have ht' : 9 * x ≤ Real.exp (9 * x - 1) := by nlinarith
    calc
      9 * x * Real.exp (-9 * x) ≤
          Real.exp (9 * x - 1) * Real.exp (-9 * x) :=
        mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le
      _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsq := pow_le_pow_left₀
    (mul_nonneg (by positivity) (Real.exp_pos _).le) hxexp 2
  have hleft : (9 * x * Real.exp (-9 * x)) ^ 2 =
      81 * (x ^ 2 * Real.exp (-18 * x)) := by
    rw [show Real.exp (-18 * x) = Real.exp (-9 * x) ^ 2 by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    ring
  have hright : Real.exp (-1) ^ 2 = Real.exp (-2) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hleft, hright] at hsq
  linarith

/-- Elementary optimizer for `x^6 exp(-18x)`. -/
theorem sixth_mul_exp_neg_eighteen_le
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ 6 * Real.exp (-18 * x) ≤ Real.exp (-6) / 729 := by
  have ht := Real.add_one_le_exp (3 * x - 1)
  have hxexp : 3 * x * Real.exp (-3 * x) ≤ Real.exp (-1) := by
    have ht' : 3 * x ≤ Real.exp (3 * x - 1) := by nlinarith
    calc
      3 * x * Real.exp (-3 * x) ≤
          Real.exp (3 * x - 1) * Real.exp (-3 * x) :=
        mul_le_mul_of_nonneg_right ht' (Real.exp_pos _).le
      _ = Real.exp (-1) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hsix := pow_le_pow_left₀
    (mul_nonneg (by positivity) (Real.exp_pos _).le) hxexp 6
  have hleft : (3 * x * Real.exp (-3 * x)) ^ 6 =
      729 * (x ^ 6 * Real.exp (-18 * x)) := by
    rw [show Real.exp (-18 * x) = Real.exp (-3 * x) ^ 6 by
      rw [← Real.exp_nat_mul]
      congr 1
      ring]
    ring
  have hright : Real.exp (-1) ^ 6 = Real.exp (-6) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hleft, hright] at hsix
  linarith

theorem exp_neg_two_lt_seventeen_over_oneHundredTwentyFive :
    Real.exp (-2) < (17 / 125 : ℝ) := by
  have he1 := Real.exp_one_gt_d9
  have he2 : (125 / 17 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    nlinarith [sq_nonneg (Real.exp 1 - (2.7182818283 : ℝ))]
  rw [Real.exp_neg]
  have h := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 125 / 17) he2
  norm_num at h ⊢
  exact h

theorem exp_neg_six_lt_one_over_fourHundred :
    Real.exp (-6) < (1 / 400 : ℝ) := by
  have he1 := Real.exp_one_gt_d9
  have he6 : (400 : ℝ) < Real.exp 6 := by
    rw [show (6 : ℝ) = (6 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    have hp := pow_lt_pow_left₀ he1 (by norm_num) (n := 6) (by norm_num)
    norm_num at hp ⊢
    nlinarith
  rw [Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 400) he6)

/-- A bounded damped insertion against the first atom controls the corresponding higher-tail
moment. -/
theorem thetaCuspHigherAtomRawEvenMoment_le_first_mass_of_damped_bound
    (j : ℕ) {C : ℝ}
    (hbound : ∀ x : ℝ, 0 ≤ x → x ^ (2 * j) * Real.exp (-18 * x) ≤ C) :
    thetaCuspHigherAtomRawEvenMoment j ≤
      (8 / 2997 : ℝ) * C * thetaCuspAtomRawEvenMoment 0 1 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) *
    (thetaCuspFullSource x - thetaCuspSourceTerm x 1)
  let g : ℝ → ℝ := fun x =>
    ((8 / 2997 : ℝ) * C) * thetaCuspSourceTerm x 1
  have hf : Integrable f mu := by
    change IntegrableOn (fun x => x ^ (2 * j) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) (Ioi 0)
    exact integrableOn_pow_mul_thetaCuspHigherSource j
  have hg : Integrable g mu := by
    dsimp only [g, mu]
    simpa only [Nat.mul_zero, pow_zero, one_mul] using
      (integrableOn_pow_mul_thetaCuspSourceTerm 0 1).const_mul
        ((8 / 2997 : ℝ) * C)
  have hmono : (∫ x, f x ∂mu) ≤ ∫ x, g x ∂mu := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have htail := thetaCuspFullSource_sub_first_le_exp_neg_eighteen hx.le
    have hpow : 0 ≤ x ^ (2 * j) := pow_nonneg hx.le _
    calc
      f x ≤ x ^ (2 * j) *
          ((8 / 2997 : ℝ) * Real.exp (-18 * x) *
            thetaCuspSourceTerm x 1) :=
        mul_le_mul_of_nonneg_left htail hpow
      _ = ((8 / 2997 : ℝ) *
          (x ^ (2 * j) * Real.exp (-18 * x))) *
            thetaCuspSourceTerm x 1 := by ring
      _ ≤ ((8 / 2997 : ℝ) * C) * thetaCuspSourceTerm x 1 := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (hbound x hx.le) (by norm_num)
        · exact thetaCuspSourceTerm_nonneg_of_pos hx 1
      _ = g x := rfl
  rw [thetaCuspHigherAtomRawEvenMoment_eq_integral_tail,
    thetaCuspAtomRawEvenMoment]
  simp only [Nat.mul_zero, pow_zero, one_mul]
  dsimp only [f, g, mu] at hmono ⊢
  rw [integral_const_mul] at hmono
  nlinarith

/-- The higher theta atoms contribute less than `9/4,000,000` to the second raw moment. -/
theorem thetaCuspHigherAtomRawEvenMoment_one_lt_nine_over_fourMillion :
    thetaCuspHigherAtomRawEvenMoment 1 < (9 / 4000000 : ℝ) := by
  have hraw := thetaCuspHigherAtomRawEvenMoment_le_first_mass_of_damped_bound
    1 (C := Real.exp (-2) / 81) (fun x hx => by
      simpa only [Nat.mul_one] using sq_mul_exp_neg_eighteen_le hx)
  have hfirst : thetaCuspAtomRawEvenMoment 0 1 ≤ 1 / 2 := by
    have hle := thetaCuspAtomRawEvenMoment_one_le_raw 0
    have hpair := thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget
    have hraw1 := thetaCuspRawEvenMoment_nonneg 1
    nlinarith
  have hexp := exp_neg_two_lt_seventeen_over_oneHundredTwentyFive
  have hnon : 0 ≤ thetaCuspAtomRawEvenMoment 0 1 :=
    thetaCuspAtomRawEvenMoment_nonneg 0 1
  calc
    thetaCuspHigherAtomRawEvenMoment 1 ≤
        (8 / 2997 : ℝ) * (Real.exp (-2) / 81) *
          thetaCuspAtomRawEvenMoment 0 1 := hraw
    _ < (9 / 4000000 : ℝ) := by nlinarith

/-- The higher theta atoms contribute less than `1/200,000,000` to the sixth raw moment. -/
theorem thetaCuspHigherAtomRawEvenMoment_three_lt_one_over_twoHundredMillion :
    thetaCuspHigherAtomRawEvenMoment 3 < (1 / 200000000 : ℝ) := by
  have hraw := thetaCuspHigherAtomRawEvenMoment_le_first_mass_of_damped_bound
    3 (C := Real.exp (-6) / 729) (fun x hx => by
      norm_num only [Nat.reduceMul]
      exact sixth_mul_exp_neg_eighteen_le hx)
  have hfirst : thetaCuspAtomRawEvenMoment 0 1 ≤ 1 / 2 := by
    have hle := thetaCuspAtomRawEvenMoment_one_le_raw 0
    have hpair := thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget
    have hraw1 := thetaCuspRawEvenMoment_nonneg 1
    nlinarith
  have hexp := exp_neg_six_lt_one_over_fourHundred
  have hnon : 0 ≤ thetaCuspAtomRawEvenMoment 0 1 :=
    thetaCuspAtomRawEvenMoment_nonneg 0 1
  calc
    thetaCuspHigherAtomRawEvenMoment 3 ≤
        (8 / 2997 : ℝ) * (Real.exp (-6) / 729) *
          thetaCuspAtomRawEvenMoment 0 1 := hraw
    _ < (1 / 200000000 : ℝ) := by nlinarith

private def sixthTraceCapPolynomial (s t : ℝ) : ℝ :=
  (0.00059935 + 1 / 200000000 : ℝ) * s ^ 2 -
    15 * (0.0029627 : ℝ) * s * t + 30 * t ^ 3 -
      (9 / 250000 : ℝ) * s ^ 3

private theorem sixthTraceCapPolynomial_mono_t
    {s t u : ℝ}
    (hs1 : s ≤ 1 / 2)
    (ht0 : (0.02297 : ℝ) ≤ t) (htu : t ≤ u) :
    sixthTraceCapPolynomial s t ≤ sixthTraceCapPolynomial s u := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht0
  have hu0 : 0 < u := lt_of_lt_of_le htpos htu
  have hbracket : 0 <
      -15 * (0.0029627 : ℝ) * s +
        30 * (u ^ 2 + u * t + t ^ 2) := by
    have hsq_t : (0.02297 : ℝ) ^ 2 ≤ t ^ 2 := by gcongr
    have htu0 : (0.02297 : ℝ) ≤ u := ht0.trans htu
    have hsq_u : (0.02297 : ℝ) ^ 2 ≤ u ^ 2 := by gcongr
    have hmul : (0.02297 : ℝ) ^ 2 ≤ u * t := by nlinarith
    nlinarith
  have hident : sixthTraceCapPolynomial s u - sixthTraceCapPolynomial s t =
      (u - t) * (-15 * (0.0029627 : ℝ) * s +
        30 * (u ^ 2 + u * t + t ^ 2)) := by
    unfold sixthTraceCapPolynomial
    ring
  nlinarith [mul_nonneg (sub_nonneg.mpr htu) hbracket.le]

private theorem sixthTraceCapPolynomial_antitone_s
    {s v t : ℝ}
    (hsv : s ≤ v) (hv1 : v ≤ 1 / 2)
    (ht0 : (0.02297 : ℝ) ≤ t) :
    sixthTraceCapPolynomial v t ≤ sixthTraceCapPolynomial s t := by
  have hs1 : s ≤ 1 / 2 := hsv.trans hv1
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht0
  have hbracket :
      (0.00059935 + 1 / 200000000 : ℝ) * (v + s) -
          15 * (0.0029627 : ℝ) * t -
        (9 / 250000 : ℝ) * (v ^ 2 + v * s + s ^ 2) < 0 := by
    have hsum : v + s ≤ 1 := by linarith
    nlinarith [sq_nonneg v, sq_nonneg s]
  have hident : sixthTraceCapPolynomial v t - sixthTraceCapPolynomial s t =
      (v - s) *
        ((0.00059935 + 1 / 200000000 : ℝ) * (v + s) -
          15 * (0.0029627 : ℝ) * t -
          (9 / 250000 : ℝ) * (v ^ 2 + v * s + s ^ 2)) := by
    unfold sixthTraceCapPolynomial
    ring
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hsv) hbracket.le]

private theorem sixthTraceCapPolynomial_small_tail_mono
    {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 9 / 188000) :
    sixthTraceCapPolynomial
        ((0.4969488 : ℝ) + h)
        ((0.0229718 : ℝ) + (47 / 1000 : ℝ) * h) ≤
      sixthTraceCapPolynomial
        ((0.4969488 : ℝ) + 9 / 188000)
        ((0.0229718 : ℝ) + 9 / 4000000) := by
  let d : ℝ := 9 / 188000
  let R : ℝ := 47 / 1000
  let A : ℝ := 0.4969488
  let B : ℝ := 0.0229718
  have hRd : R * d = 9 / 4000000 := by
    norm_num [R, d]
  have hderivLower : 0 <
      90 * R * B ^ 2 -
        15 * (0.0029627 : ℝ) *
          (R * (A + d) + (B + R * d)) -
        3 * (9 / 250000 : ℝ) * (A + d) ^ 2 := by
    norm_num [R, A, B, d]
  have hfactor : 0 ≤ d - h := sub_nonneg.mpr hh1
  have hident :
      sixthTraceCapPolynomial (A + d) (B + R * d) -
          sixthTraceCapPolynomial (A + h) (B + R * h) =
        (d - h) *
          ((0.00059935 + 1 / 200000000 : ℝ) *
              (2 * A + d + h) -
            15 * (0.0029627 : ℝ) *
              (R * (A + d) + (B + R * h)) +
            30 * R *
              ((B + R * d) ^ 2 +
                (B + R * d) * (B + R * h) +
                (B + R * h) ^ 2) -
            (9 / 250000 : ℝ) *
              ((A + d) ^ 2 + (A + d) * (A + h) + (A + h) ^ 2)) := by
    unfold sixthTraceCapPolynomial
    ring
  have hbracket : 0 ≤
      (0.00059935 + 1 / 200000000 : ℝ) * (2 * A + d + h) -
        15 * (0.0029627 : ℝ) * (R * (A + d) + (B + R * h)) +
        30 * R *
          ((B + R * d) ^ 2 + (B + R * d) * (B + R * h) +
            (B + R * h) ^ 2) -
        (9 / 250000 : ℝ) *
          ((A + d) ^ 2 + (A + d) * (A + h) + (A + h) ^ 2) := by
    dsimp only [A, B, R, d] at hderivLower ⊢
    have hB0 : 0 ≤ (0.0229718 : ℝ) := by norm_num
    have hRh0 : 0 ≤ (47 / 1000 : ℝ) * h := mul_nonneg (by norm_num) hh0
    have hsquares :
        3 * (0.0229718 : ℝ) ^ 2 ≤
          ((0.0229718 : ℝ) + (47 / 1000 : ℝ) * (9 / 188000)) ^ 2 +
          ((0.0229718 : ℝ) + (47 / 1000 : ℝ) * (9 / 188000)) *
            ((0.0229718 : ℝ) + (47 / 1000 : ℝ) * h) +
          ((0.0229718 : ℝ) + (47 / 1000 : ℝ) * h) ^ 2 := by
      nlinarith [sq_nonneg ((47 / 1000 : ℝ) * h),
        sq_nonneg ((47 / 1000 : ℝ) * (9 / 188000))]
    nlinarith [sq_nonneg ((0.4969488 : ℝ) + h),
      sq_nonneg ((0.4969488 : ℝ) + 9 / 188000)]
  have hdiff := mul_nonneg hfactor hbracket
  nlinarith [hident]

/-- Five finite first-atom rational enclosures imply the completed sixth-trace cap needed by the
order-24 endpoint reduction. -/
theorem normalizedPrimeArchMoment_two_lt_three_over_tenMillion_of_firstAtom_bounds
    (ha0 : (0.4969488 : ℝ) < thetaCuspAtomRawEvenMoment 0 1)
    (ha1lower : (0.02297 : ℝ) < thetaCuspAtomRawEvenMoment 1 1)
    (ha1upper : thetaCuspAtomRawEvenMoment 1 1 < (0.0229718 : ℝ))
    (ha2 : (0.0029627 : ℝ) < thetaCuspAtomRawEvenMoment 2 1)
    (ha3 : thetaCuspAtomRawEvenMoment 3 1 < (0.00059935 : ℝ)) :
    normalizedPrimeArchMoment 2 < (3 / 10000000 : ℝ) := by
  let a0 := thetaCuspAtomRawEvenMoment 0 1
  let a1 := thetaCuspAtomRawEvenMoment 1 1
  let a2 := thetaCuspAtomRawEvenMoment 2 1
  let a3 := thetaCuspAtomRawEvenMoment 3 1
  let h0 := thetaCuspHigherAtomRawEvenMoment 0
  let h1 := thetaCuspHigherAtomRawEvenMoment 1
  let h2 := thetaCuspHigherAtomRawEvenMoment 2
  let h3 := thetaCuspHigherAtomRawEvenMoment 3
  let m0 := thetaCuspRawEvenMoment 0
  let m1 := thetaCuspRawEvenMoment 1
  let m2 := thetaCuspRawEvenMoment 2
  let m3 := thetaCuspRawEvenMoment 3
  have hm (j : ℕ) : thetaCuspRawEvenMoment j =
      thetaCuspAtomRawEvenMoment j 1 + thetaCuspHigherAtomRawEvenMoment j :=
    thetaCuspRawEvenMoment_eq_one_add_higher j
  have hm0 : m0 = a0 + h0 := by simpa only [m0, a0, h0] using hm 0
  have hm1 : m1 = a1 + h1 := by simpa only [m1, a1, h1] using hm 1
  have hm2 : m2 = a2 + h2 := by simpa only [m2, a2, h2] using hm 2
  have hm3 : m3 = a3 + h3 := by simpa only [m3, a3, h3] using hm 3
  have ha0pos : 0 < a0 := by
    dsimp only [a0]
    exact (by norm_num : (0 : ℝ) < 0.4969488).trans ha0
  have ha1pos : 0 < a1 := by
    dsimp only [a1]
    exact (by norm_num : (0 : ℝ) < 0.02297).trans ha1lower
  have hh0 : 0 ≤ h0 := by simpa only [h0] using thetaCuspHigherAtomRawEvenMoment_nonneg 0
  have hh1 : 0 ≤ h1 := by simpa only [h1] using thetaCuspHigherAtomRawEvenMoment_nonneg 1
  have hh2 : 0 ≤ h2 := by simpa only [h2] using thetaCuspHigherAtomRawEvenMoment_nonneg 2
  have hh3 : 0 ≤ h3 := by simpa only [h3] using thetaCuspHigherAtomRawEvenMoment_nonneg 3
  have hm0pos : 0 < m0 := by simpa only [m0] using thetaCuspRawEvenMoment_zero_pos
  have hm0half : m0 ≤ 1 / 2 := by
    have hpair := thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget
    have hnon := thetaCuspRawEvenMoment_nonneg 1
    simpa only [m0] using (show thetaCuspRawEvenMoment 0 ≤ 1 / 2 by nlinarith)
  have hm1lower : (0.02297 : ℝ) < m1 := by rw [hm1]; nlinarith
  have hh1upper : h1 < (9 / 4000000 : ℝ) := by
    simpa only [h1] using thetaCuspHigherAtomRawEvenMoment_one_lt_nine_over_fourMillion
  have hh3upper : h3 < (1 / 200000000 : ℝ) := by
    simpa only [h3] using
      thetaCuspHigherAtomRawEvenMoment_three_lt_one_over_twoHundredMillion
  have hratio : h1 ≤ (47 / 1000 : ℝ) * h0 := by
    have hcross := thetaCuspHigherFirst_rawEvenMoment_cross_le 0 1
    norm_num at hcross
    have haRatio : a1 < (47 / 1000 : ℝ) * a0 := by
      dsimp only [a0, a1] at ha0 ha1upper ⊢
      nlinarith
    have hmul : a1 * h0 ≤ ((47 / 1000 : ℝ) * a0) * h0 :=
      mul_le_mul_of_nonneg_right haRatio.le hh0
    apply (mul_le_mul_iff_of_pos_right ha0pos).mp
    dsimp only [a0, a1, h0, h1] at hcross hmul ⊢
    nlinarith
  have hpolyUpper :
      m0 ^ 2 * m3 - 15 * m0 * m1 * m2 + 30 * m1 ^ 3 -
          (9 / 250000 : ℝ) * m0 ^ 3 ≤
        sixthTraceCapPolynomial m0 m1 := by
    have hm2lower : (0.0029627 : ℝ) < m2 := by rw [hm2]; nlinarith
    have hm3upper : m3 < (0.00059935 + 1 / 200000000 : ℝ) := by
      rw [hm3]
      dsimp only [a3, h3] at ha3 hh3upper ⊢
      nlinarith
    have hm1pos : 0 < m1 :=
      (by norm_num : (0 : ℝ) < 0.02297).trans hm1lower
    dsimp only [sixthTraceCapPolynomial]
    have hsq : 0 ≤ m0 ^ 2 := sq_nonneg m0
    have hprod : 0 ≤ m0 * m1 := mul_nonneg hm0pos.le hm1pos.le
    nlinarith [mul_le_mul_of_nonneg_left hm3upper.le hsq,
      mul_le_mul_of_nonneg_left hm2lower.le hprod]
  have hpolyNeg : sixthTraceCapPolynomial m0 m1 < 0 := by
    let d : ℝ := 9 / 188000
    let sStar : ℝ := 0.4969488 + d
    let tStar : ℝ := 0.0229718 + 9 / 4000000
    have hsStarHalf : sStar ≤ 1 / 2 := by norm_num [sStar, d]
    have htStarLower : (0.02297 : ℝ) ≤ tStar := by norm_num [tStar]
    have hstar : sixthTraceCapPolynomial sStar tStar < 0 := by
      norm_num [sixthTraceCapPolynomial, sStar, tStar, d]
    rcases le_total h0 d with hsmall | hlarge
    · have hm1upper : m1 ≤ (0.0229718 : ℝ) + (47 / 1000 : ℝ) * h0 := by
        rw [hm1]
        dsimp only [a1, h1] at ha1upper hratio ⊢
        nlinarith
      have hsLower : (0.4969488 : ℝ) + h0 ≤ m0 := by
        rw [hm0]
        dsimp only [a0, h0] at ha0 ⊢
        nlinarith
      have htMono := sixthTraceCapPolynomial_mono_t
        (s := m0) (t := m1)
        (u := (0.0229718 : ℝ) + (47 / 1000 : ℝ) * h0)
        hm0half hm1lower.le hm1upper
      have hsMono := sixthTraceCapPolynomial_antitone_s
        (s := (0.4969488 : ℝ) + h0) (v := m0)
        (t := (0.0229718 : ℝ) + (47 / 1000 : ℝ) * h0)
        hsLower hm0half (by
          have : (0.02297 : ℝ) ≤ 0.0229718 := by norm_num
          nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 47 / 1000) hh0])
      have hsmallMono := sixthTraceCapPolynomial_small_tail_mono hh0 hsmall
      dsimp only [sStar, tStar, d] at hstar ⊢
      exact (htMono.trans (hsMono.trans hsmallMono)).trans_lt hstar
    · have hm1upper : m1 ≤ tStar := by
        rw [hm1]
        dsimp only [a1, h1, tStar] at ha1upper hh1upper ⊢
        nlinarith
      have hsLower : sStar ≤ m0 := by
        rw [hm0]
        dsimp only [sStar, d, a0, h0] at ha0 hlarge ⊢
        nlinarith only [ha0, hlarge]
      have htMono := sixthTraceCapPolynomial_mono_t
        (s := m0) (t := m1) (u := tStar)
        hm0half hm1lower.le hm1upper
      have hsMono := sixthTraceCapPolynomial_antitone_s
        (s := sStar) (v := m0) (t := tStar)
        hsLower hm0half htStarLower
      exact (htMono.trans hsMono).trans_lt hstar
  have hcross :
      m0 ^ 2 * m3 - 15 * m0 * m1 * m2 + 30 * m1 ^ 3 -
          (9 / 250000 : ℝ) * m0 ^ 3 < 0 :=
    hpolyUpper.trans_lt hpolyNeg
  rw [normalizedPrimeArchMoment_two_eq_thetaCuspNormalizedEvenMoment]
  simp only [thetaCuspNormalizedEvenMoment]
  change m3 / m0 / 120 - m1 / m0 * (m2 / m0) / 8 +
      (m1 / m0) ^ 3 / 4 < (3 / 10000000 : ℝ)
  rw [← sub_lt_zero]
  have hident :
      m3 / m0 / 120 - m1 / m0 * (m2 / m0) / 8 +
          (m1 / m0) ^ 3 / 4 - (3 / 10000000 : ℝ) =
        (m0 ^ 2 * m3 - 15 * m0 * m1 * m2 + 30 * m1 ^ 3 -
          (9 / 250000 : ℝ) * m0 ^ 3) / (120 * m0 ^ 3) := by
    field_simp [hm0pos.ne']
    ring
  rw [hident]
  exact div_neg_of_neg_of_pos hcross (by positivity)

end

end RHTower
