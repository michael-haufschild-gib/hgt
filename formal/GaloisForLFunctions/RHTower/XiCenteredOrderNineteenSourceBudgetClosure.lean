import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentSixteenthFloor
import GaloisForLFunctions.RHTower.XiCenteredOrdersNineteenTwentySourceBudgetBoundary

/-!
# Unconditional closure of the centered order-nineteen source moment

A sixteenth-mesh theta certificate sharpens the complete fourth reciprocal-trace budget below
`147 / 10^6`.  Every zero in the formerly residual order-twenty annulus contributes more than
`147 / (4 * 10^6)` to that nonnegative trace, and its four distinct FE--Schwarz copies therefore
overspend the source budget.  The annulus is empty unconditionally, giving

`0 < normalizedPrimeArchMoment 19`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A slightly larger rational multiplier below `4*pi` sharpens the elementary logarithmic
certificate to `2.53102`. -/
lemma twoHundredFiftyThreeThousandOneHundredTwo_over_oneHundredThousand_lt_log_four_mul_pi :
    (253102 / 100000 : ℝ) < Real.log (4 * Real.pi) := by
  let v : ℝ := 5 ^ 26 / (2 ^ 6 * 3 ^ 32)
  let c : ℝ := 1 + 1 / 9000
  have hvpos : 0 < v := by
    dsimp [v]
    positivity
  have hcpos : 0 < c := by
    dsimp [c]
    norm_num
  have hvcpi : v * c < 4 * Real.pi := by
    dsimp [v, c]
    nlinarith [Real.pi_gt_d20]
  have hlogv : (2530909 / 1000000 : ℝ) < Real.log v := by
    dsimp [v]
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    nlinarith [Real.log_five_gt_d9, Real.log_two_lt_d9,
      Real.log_three_lt_d9]
  have hlogc : (2 / 18001 : ℝ) < Real.log c := by
    have h := Real.lt_log_one_add_of_pos (x := (1 / 9000 : ℝ)) (by norm_num)
    norm_num [c] at h ⊢
    exact h
  have hlogvc : Real.log v + Real.log c < Real.log (4 * Real.pi) := by
    have h := Real.log_lt_log (mul_pos hvpos hcpos) hvcpi
    rw [Real.log_mul (by positivity) (by positivity)] at h
    exact h
  have hrat :
      (253102 / 100000 : ℝ) < 2530909 / 1000000 + 2 / 18001 := by
    norm_num
  exact hrat.trans ((add_lt_add hlogv hlogc).trans hlogvc)

/-- Sharpened exact endpoint-curvature budget used by the annulus closure. -/
theorem xiEndpointCompletedCurvature_lt_oneThousandOneHundredFiftySeven_over_twentyFiveThousand :
    xiEndpointCompletedCurvature < 1157 / 25000 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith
    [eulerMascheroniConstant_lt_fiveThousandSevenHundredSeventyThree_over_tenThousand,
      twoHundredFiftyThreeThousandOneHundredTwo_over_oneHundredThousand_lt_log_four_mul_pi]

/-- The sixteenth-mesh dominant-atom floor gives the normalized fourth theta-moment threshold
needed by the source contraction. -/
theorem oneHundredThirtyNine_div_twentyFiveThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (139 / 25000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  have hraw2 : (139 / 50000 : ℝ) < thetaCuspRawEvenMoment 2 :=
    oneHundredThirtyNine_div_fiftyThousand_lt_thetaCuspAtomRawEvenMoment_two_one.trans_le
      (thetaCuspAtomRawEvenMoment_one_le_raw 2)
  have hraw0pos : 0 < thetaCuspRawEvenMoment 0 :=
    thetaCuspRawEvenMoment_zero_pos
  have hraw1nonneg : 0 ≤ thetaCuspRawEvenMoment 1 :=
    thetaCuspRawEvenMoment_nonneg 1
  have hraw0le : thetaCuspRawEvenMoment 0 ≤ 1 / 2 := by
    nlinarith [thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget]
  rw [thetaCuspNormalizedEvenMoment, lt_div_iff₀ hraw0pos]
  nlinarith

/-- The coupled endpoint-resolvent/source inequality now places the zeroth reciprocal trace below
`0.04633`. -/
theorem normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredThirtyThree_over_oneHundredThousand :
    normalizedPrimeArchMoment 0 < 4633 / 100000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hM1 : M < 1 := by
    simpa only [M] using normalizedPrimeArchMoment_zero_lt_one
  have hmu :=
    oneHundredThirtyNine_div_twentyFiveThousand_lt_thetaCuspNormalizedEvenMoment_two
  have hsource : normalizedPrimeArchMoment 1 <
      M ^ 2 / 2 - (139 / 25000 : ℝ) / 6 := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [M]
    nlinarith
  have hthermal : xiThermalSecondMoment <
      (84 / 83 : ℝ) * (M ^ 2 / 2 - (139 / 25000 : ℝ) / 6) :=
    xiThermalSecondMoment_le_eightyFour_over_eightyThree_source.trans_lt
      (mul_lt_mul_of_pos_left hsource (by norm_num))
  have hgap :=
    normalizedPrimeArchMoment_zero_sub_thermalEndpointResolvent_le_quarter_secondMoment
  have hres := xiThermalEndpointResolventValue_le_endpointCompletedCurvature
  have hC :=
    xiEndpointCompletedCurvature_lt_oneThousandOneHundredFiftySeven_over_twentyFiveThousand
  have hmaster :
      M < 1157 / 25000 +
        (21 / 83 : ℝ) * (M ^ 2 / 2 - (139 / 25000 : ℝ) / 6) := by
    dsimp only [M] at hgap ⊢
    nlinarith
  by_contra hnot
  have hMlower : (4633 / 100000 : ℝ) ≤ M := le_of_not_gt hnot
  have hfactor : 0 < 1 - (21 / 166 : ℝ) * (M + 4633 / 100000) := by
    nlinarith
  have hmonotone :
      (4633 / 100000 : ℝ) - (21 / 166 : ℝ) * (4633 / 100000) ^ 2 ≤
        M - (21 / 166 : ℝ) * M ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hMlower) hfactor.le
    nlinarith
  have hupper :
      M - (21 / 166 : ℝ) * M ^ 2 <
        1157 / 25000 - (21 / 498 : ℝ) * (139 / 25000) := by
    nlinarith [hmaster]
  have hrat :
      1157 / 25000 - (21 / 498 : ℝ) * (139 / 25000) <
        (4633 / 100000 : ℝ) - (21 / 166 : ℝ) * (4633 / 100000) ^ 2 := by
    norm_num
  linarith

/-- **Sharpened complete fourth reciprocal-trace budget.** -/
theorem normalizedPrimeArchMoment_one_lt_oneHundredFortySeven_over_oneMillion :
    normalizedPrimeArchMoment 1 < 147 / 1000000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hM :=
    normalizedPrimeArchMoment_zero_lt_fourThousandSixHundredThirtyThree_over_oneHundredThousand
  have hMsq : M ^ 2 < (4633 / 100000 : ℝ) ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr (by simpa only [M] using hM))
      (add_pos (by norm_num : (0 : ℝ) < 4633 / 100000) hM0)
    nlinarith
  have hmu :=
    oneHundredThirtyNine_div_twentyFiveThousand_lt_thetaCuspNormalizedEvenMoment_two
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  simpa only [M] using (by nlinarith :
    M ^ 2 / 2 - thetaCuspNormalizedEvenMoment 2 / 6 < 147 / 1000000)

/-- Every fourth-trace atom throughout the old order-twenty residual height window exceeds one
quarter of the sharpened global source threshold. -/
theorem oneHundredFortySeven_over_fourMillion_lt_xiFourthReciprocalTraceAtom_below_327_over_2
    (q : XiZeroCopy)
    (huLower : (0 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 2365 / 16 ≤ (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 327 / 2) :
    (147 / 4000000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 655 / 4
  have hu0 : 0 < u := by simpa only [u] using huLower
  have hv0 : 0 < v := by dsimp only [v]; linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvL : 2365 / 16 ≤ v := by simpa only [v] using hvLower
  have hvU : v < 327 / 2 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 2365 / 16 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 :=
    (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsqLower : (2365 / 16 : ℝ) ^ 2 < w ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
  have hsecond : 0 < 147 * (W ^ 2 + w ^ 2) - 4000000 := by
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      4000000 * W ^ 2 - 147 * W ^ 4 <
        4000000 * w ^ 2 - 147 * w ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (4000000 * w ^ 2 - 147 * w ^ 4) -
            (4000000 * W ^ 2 - 147 * W ^ 4) =
          (W ^ 2 - w ^ 2) * (147 * (W ^ 2 + w ^ 2) - 4000000) := by
      ring
    nlinarith
  have huv : u * v < 327 / 8 := by
    calc
      u * v < (1 / 4 : ℝ) * v := mul_lt_mul_of_pos_right huU hv0
      _ < (1 / 4 : ℝ) * (327 / 2) :=
        mul_lt_mul_of_pos_left hvU (by norm_num)
      _ = 327 / 8 := by ring
  have hendpoint :
      32000000 * (327 / 8 : ℝ) <
        4000000 * W ^ 2 - 147 * W ^ 4 := by
    norm_num [W]
  have huvScaled : 32000000 * (u * v) < 32000000 * (327 / 8 : ℝ) :=
    mul_lt_mul_of_pos_left huv (by norm_num)
  have hchain :
      32000000 * (u * v) < 4000000 * w ^ 2 - 147 * w ^ 4 :=
    huvScaled.trans (hendpoint.trans hshape)
  have hG :
      0 < 4000000 * (v ^ 2 - 6 * u * v + u ^ 2) - 147 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith [hchain]
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    simp only [u, v, w]
    exact xiZeroCopyReciprocalSquare_sq_re_formula q
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4000000) (pow_pos hw0 4)]
  nlinarith

/-- Four FE--Schwarz copies of an old residual-annulus zero overspend the complete trace. -/
theorem oneHundredFortySeven_over_oneMillion_lt_source_of_centeredOrderTwentyResidualAnnulus
    (q : XiZeroCopy) (hq : XiCenteredOrderTwentyResidualAnnulus q) :
    (147 / 1000000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hle := four_mul_xiFourthReciprocalTraceAtom_le_source_of_offLine q hq.1
  have hatom :=
    oneHundredFortySeven_over_fourMillion_lt_xiFourthReciprocalTraceAtom_below_327_over_2
      q (by linarith [hq.2.1]) hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2
  nlinarith

/-- **Unconditional emptiness of the order-twenty residual annulus.** -/
theorem xiCenteredOrderTwentyResidualAnnulusEmpty :
    XiCenteredOrderTwentyResidualAnnulusEmpty := by
  rintro ⟨q, hq⟩
  have hlower :=
    oneHundredFortySeven_over_oneMillion_lt_source_of_centeredOrderTwentyResidualAnnulus q hq
  have hupper := normalizedPrimeArchMoment_one_lt_oneHundredFortySeven_over_oneMillion
  linarith

/-- Every centered reciprocal-square twentieth power has positive real part unconditionally. -/
theorem xiZeroCopyReciprocalSquare_pow_twenty_re_pos (q : XiZeroCopy) :
    0 < (xiZeroCopyReciprocalSquare q ^ 20).re :=
  xiZeroCopyReciprocalSquare_pow_twenty_re_pos_of_residualAnnulusEmpty
    xiCenteredOrderTwentyResidualAnnulusEmpty q

/-- **Unconditional centered order-nineteen source positivity.** -/
theorem normalizedPrimeArchMoment_nineteen_pos :
    0 < normalizedPrimeArchMoment 19 :=
  normalizedPrimeArchMoment_nineteen_pos_of_centeredOrderTwentyResidualAnnulusEmpty
    xiCenteredOrderTwentyResidualAnnulusEmpty

end

end RHTower
