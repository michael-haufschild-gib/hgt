import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomFourthMomentFloor
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity
import GaloisForLFunctions.RHTower.XiThermalEndpointResolventGap
import GaloisForLFunctions.RHTower.PrimeArchEndpointCalibratedHausdorffRH
import GaloisForLFunctions.RHTower.XiOrderFourteenEdgeCorner
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Source exclusion of the order-fourteen compact edge corner

The order-fifteen squared-Xi sector can fail only in the compact corner

`1/5 < (Re rho - 1/2)^2 < 1/4`, `85 < (Im rho)^2 < 100`.

This module excludes that corner without a zero table.  A rational lower bound for the dominant
theta atom forces the normalized fourth theta moment above `269/50000`. The endpoint resolvent and
the unconditional quartet orientation estimate then bound the fourth reciprocal trace below
`1/5000`. Four FE--Schwarz copies of a zero in the corner would contribute more than that
amount to the same nonnegative trace, which is impossible.

This is a route discriminator, not an RH disproof: it proves that the first unprotected fixed
squared-seam order still has the RH-compatible strict sign.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A small multiplicative improvement of the existing smooth logarithmic approximant raises the
certified lower bound for `log (4*pi)` to `2.531`. -/
lemma twoThousandFiveHundredThirtyOne_over_thousand_lt_log_four_mul_pi :
    (2531 / 1000 : ℝ) < Real.log (4 * Real.pi) := by
  let v : ℝ := 5 ^ 26 / (2 ^ 6 * 3 ^ 32)
  let c : ℝ := 1 + 1 / 10000
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
  have hlogc : (2 / 20001 : ℝ) < Real.log c := by
    have h := Real.lt_log_one_add_of_pos (x := (1 / 10000 : ℝ)) (by norm_num)
    norm_num [c] at h ⊢
    exact h
  have hlogvc : Real.log v + Real.log c < Real.log (4 * Real.pi) := by
    have h := Real.log_lt_log (mul_pos hvpos hcpos) hvcpi
    rw [Real.log_mul (by positivity) (by positivity)] at h
    exact h
  have hrat :
      (2531 / 1000 : ℝ) < 2530909 / 1000000 + 2 / 20001 := by
    norm_num
  exact hrat.trans ((add_lt_add hlogv hlogc).trans hlogvc)

set_option maxRecDepth 1000000 in
/-- A certified upper bound for Euler's constant from the decreasing Euler--Mascheroni sequence
at the factorable index `6250 = 2 * 5^5`. -/
lemma eulerMascheroniConstant_lt_fiveThousandSevenHundredSeventyThree_over_tenThousand :
    Real.eulerMascheroniConstant < 5773 / 10000 := by
  refine (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 6250).trans ?_
  rw [Real.eulerMascheroniSeq']
  norm_num only [if_false, Nat.reduceEqDiff, Nat.cast_ofNat]
  rw [show (6250 : ℝ) = 2 * 5 ^ 5 by norm_num,
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have htwo := Real.log_two_gt_d9
  have hfive := Real.log_five_gt_d9
  norm_num [harmonic] at *
  linarith

/-- The sharper elementary logarithm and Euler-constant bounds improve the completed endpoint
curvature budget. -/
theorem xiEndpointCompletedCurvature_lt_fourHundredSixtyThree_over_tenThousand :
    xiEndpointCompletedCurvature < 463 / 10000 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log]
  nlinarith
    [eulerMascheroniConstant_lt_fiveThousandSevenHundredSeventyThree_over_tenThousand,
      twoThousandFiveHundredThirtyOne_over_thousand_lt_log_four_mul_pi]

/-- The dominant first theta atom and the half-density budget give a normalized fourth-moment
floor with no numerical integration. -/
theorem twoHundredSixtyNine_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (269 / 50000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  have hraw2 : (269 / 100000 : ℝ) < thetaCuspRawEvenMoment 2 :=
    twoHundredSixtyNine_div_oneHundredThousand_lt_thetaCuspAtomRawEvenMoment_two_one.trans_le
      (thetaCuspAtomRawEvenMoment_one_le_raw 2)
  have hraw0pos : 0 < thetaCuspRawEvenMoment 0 :=
    thetaCuspRawEvenMoment_zero_pos
  have hraw1nonneg : 0 ≤ thetaCuspRawEvenMoment 1 :=
    thetaCuspRawEvenMoment_nonneg 1
  have hraw0le : thetaCuspRawEvenMoment 0 ≤ 1 / 2 := by
    nlinarith [thetaCuspRawEvenMomentPair_le_fullHalfDensityBudget]
  rw [thetaCuspNormalizedEvenMoment, lt_div_iff₀ hraw0pos]
  nlinarith

/-- Compatibility form of the earlier seven-interval normalized fourth-moment floor. -/
theorem twoHundredSixtyThree_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (263 / 50000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  nlinarith [twoHundredSixtyNine_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two]

/-- Compatibility form of the earlier six-interval normalized fourth-moment floor. -/
theorem three_div_sixHundredTwentyFive_lt_thetaCuspNormalizedEvenMoment_two :
    (3 / 625 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  nlinarith [twoHundredSixtyThree_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two]

/-- Compatibility form of the earlier normalized fourth-moment floor. -/
theorem twoThousandOneHundredFiftyOne_div_fiveHundredThousand_lt_thetaCuspNormalizedEvenMoment_two :
    (2151 / 500000 : ℝ) < thetaCuspNormalizedEvenMoment 2 := by
  nlinarith [three_div_sixHundredTwentyFive_lt_thetaCuspNormalizedEvenMoment_two]

/-- Removing the quarter-resolvent smoothing costs at most one quarter of the positive thermal
second moment. -/
theorem normalizedPrimeArchMoment_zero_sub_thermalEndpointResolvent_le_quarter_secondMoment :
    normalizedPrimeArchMoment 0 - xiThermalEndpointResolventValue ≤
      xiThermalSecondMoment / 4 := by
  have hnode : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  have hres := summable_xiThermalEndpointResolventValue
  have hsq := summable_xiThermalNode_sq
  have hleft := hnode.sub hres
  have hright := hsq.div_const 4
  rw [← xiThermalPositiveMoment_zero_eq_source]
  rw [xiThermalPositiveMoment, xiThermalEndpointResolventValue,
    xiThermalSecondMoment]
  simp only [Nat.zero_add, pow_one]
  rw [← hnode.tsum_sub hres, ← tsum_div_const]
  exact hleft.tsum_le_tsum (fun q => by
    let x : ℝ := xiThermalNode q
    have hx : 0 < x := by simpa only [x] using xiThermalNode_pos q
    have hd : 0 < 1 + x / 4 := by linarith
    have hx3 : 0 ≤ x ^ 2 * x := mul_nonneg (sq_nonneg x) hx.le
    change x - x / (1 + x / 4) ≤ x ^ 2 / 4
    rw [show x - x / (1 + x / 4) =
        x ^ 2 / (4 * (1 + x / 4)) by
      field_simp [hd.ne']
      ring]
    rw [div_le_iff₀ (mul_pos (by norm_num) hd)]
    nlinarith) hright

/-- The thermal second moment is bounded by the zeroth source moment because every source-selected
thermal node lies strictly between zero and one. -/
theorem xiThermalSecondMoment_le_normalizedPrimeArchMoment_zero :
    xiThermalSecondMoment ≤ normalizedPrimeArchMoment 0 := by
  have hnode : Summable (fun q : XiZeroCopy => xiThermalNode q) := by
    simpa using summable_xiThermalNode_pow 0
  rw [← xiThermalPositiveMoment_zero_eq_source]
  rw [xiThermalSecondMoment, xiThermalPositiveMoment]
  simp only [Nat.zero_add, pow_one]
  exact summable_xiThermalNode_sq.tsum_le_tsum (fun q => by
    have hx0 := xiThermalNode_pos q
    have hxR := xiThermalNode_le_primeArchEndpointHausdorffRadius q
    have hR1 := primeArchEndpointHausdorffRadius_lt_one
    have hx1 : xiThermalNode q < 1 := hxR.trans_lt hR1
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx1.le)]) hnode

/-- A coarse bound used only to select the increasing branch of the final quadratic estimate. -/
theorem normalizedPrimeArchMoment_zero_lt_one :
    normalizedPrimeArchMoment 0 < 1 := by
  have hgap :=
    normalizedPrimeArchMoment_zero_sub_thermalEndpointResolvent_le_quarter_secondMoment
  have hsecond := xiThermalSecondMoment_le_normalizedPrimeArchMoment_zero
  have hres := xiThermalEndpointResolventValue_le_endpointCompletedCurvature
  have hC := xiEndpointCompletedCurvature_lt_one_half
  nlinarith

/-- The theta floor, endpoint resolvent, and quartet orientation budget force the exact rational
upper bound needed by the compact-corner contradiction. -/
theorem normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive :
    normalizedPrimeArchMoment 0 < 29 / 625 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM1 : M < 1 := by
    simpa only [M] using normalizedPrimeArchMoment_zero_lt_one
  have hmu2 :=
    twoHundredSixtyNine_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two
  have hsource : normalizedPrimeArchMoment 1 <
      M ^ 2 / 2 - (269 / 50000 : ℝ) / 6 := by
    rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
      ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
    dsimp only [M]
    nlinarith
  have hthermal : xiThermalSecondMoment <
      (84 / 83 : ℝ) * (M ^ 2 / 2 - (269 / 50000 : ℝ) / 6) :=
    xiThermalSecondMoment_le_eightyFour_over_eightyThree_source.trans_lt
      (mul_lt_mul_of_pos_left hsource (by norm_num))
  have hgap :=
    normalizedPrimeArchMoment_zero_sub_thermalEndpointResolvent_le_quarter_secondMoment
  have hres := xiThermalEndpointResolventValue_le_endpointCompletedCurvature
  have hC := xiEndpointCompletedCurvature_lt_fourHundredSixtyThree_over_tenThousand
  have hmaster :
      M < 463 / 10000 +
        ((84 / 83 : ℝ) * (M ^ 2 / 2 - (269 / 50000 : ℝ) / 6)) / 4 := by
    dsimp only [M] at hgap ⊢
    nlinarith
  by_contra hnot
  have hMlower : (29 / 625 : ℝ) ≤ M := le_of_not_gt hnot
  have hfactor : 0 < 1 - (21 / 166 : ℝ) * (M + 29 / 625) := by
    nlinarith
  have hmonotone :
      (29 / 625 : ℝ) - (21 / 166 : ℝ) * (29 / 625) ^ 2 ≤
        M - (21 / 166 : ℝ) * M ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hMlower) hfactor.le
    nlinarith
  have hupper :
      M - (21 / 166 : ℝ) * M ^ 2 <
      463 / 10000 - (21 / 498 : ℝ) * (269 / 50000) := by
    nlinarith [hmaster]
  have hrat :
      463 / 10000 - (21 / 498 : ℝ) * (269 / 50000) <
        (29 / 625 : ℝ) - (21 / 166 : ℝ) * (29 / 625) ^ 2 := by
    norm_num
  linarith

/-- The completed fourth reciprocal trace lies strictly below the corner quartet threshold. -/
theorem normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand :
    normalizedPrimeArchMoment 1 < 9 / 50000 := by
  let M : ℝ := normalizedPrimeArchMoment 0
  have hM0 : 0 < M := by
    simpa only [M] using normalizedPrimeArchMoment_zero_pos
  have hM := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  have hMsq : M ^ 2 < (29 / 625 : ℝ) ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr (by simpa only [M] using hM))
      (add_pos (by norm_num : (0 : ℝ) < 29 / 625) hM0)
    nlinarith
  have hmu2 :=
    twoHundredSixtyNine_div_fiftyThousand_lt_thetaCuspNormalizedEvenMoment_two
  rw [normalizedPrimeArchMoment_one_eq_thetaCuspNormalizedEvenMoment,
    ← normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  have hrat :
      (29 / 625 : ℝ) ^ 2 / 2 - (269 / 50000 : ℝ) / 6 < 9 / 50000 := by
    norm_num
  simpa only [M] using (by nlinarith :
    M ^ 2 / 2 - thetaCuspNormalizedEvenMoment 2 / 6 < 9 / 50000)

/-- Compatibility form of the earlier fourth reciprocal-trace upper bound. -/
theorem normalizedPrimeArchMoment_one_lt_one_over_fiveThousand :
    normalizedPrimeArchMoment 1 < 1 / 5000 := by
  nlinarith [normalizedPrimeArchMoment_one_lt_nine_over_fiftyThousand]

/-- Compatibility form of the earlier fourth reciprocal-trace upper bound. -/
theorem normalizedPrimeArchMoment_one_lt_seven_over_twentyFiveThousand :
    normalizedPrimeArchMoment 1 < 7 / 25000 := by
  nlinarith [normalizedPrimeArchMoment_one_lt_one_over_fiveThousand]

/-- Compatibility form of the earlier fourth reciprocal-trace upper bound. -/
theorem normalizedPrimeArchMoment_one_lt_nine_over_twentyFiveThousand :
    normalizedPrimeArchMoment 1 < 9 / 25000 := by
  nlinarith [normalizedPrimeArchMoment_one_lt_seven_over_twentyFiveThousand]

/-- Every individual fourth reciprocal trace atom is nonnegative unconditionally. -/
theorem xiFourthReciprocalTraceAtom_nonneg (q : XiZeroCopy) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 2).re := by
  have h := xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  rw [pow_two, Complex.mul_re]
  simp only [xiThermalNode] at h
  nlinarith

lemma xiFourthReciprocalTraceAtom_lineConj (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
  have hz :
      xiZeroCopyReciprocalSquare (xiZeroCopyLineConjEquiv q) =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
    rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_lineConj, map_pow, map_inv₀]
  rw [hz, ← map_pow, Complex.conj_re]

lemma xiFourthReciprocalTraceAtom_conj (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
  have hz :
      xiZeroCopyReciprocalSquare (xiZeroCopyConjEquiv q) =
        (starRingEnd ℂ) (xiZeroCopyReciprocalSquare q) := by
    rw [xiZeroCopyReciprocalSquare, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_copyConj, map_pow, map_inv₀, inv_neg]
    ring
  rw [hz, ← map_pow, Complex.conj_re]

/-- The real fourth reciprocal trace over the exact multiplicity copies is the first nontrivial
normalized prime--archimedean source moment. -/
theorem tsum_xiFourthReciprocalTraceAtom_eq_source :
    (∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 2).re) =
      normalizedPrimeArchMoment 1 := by
  have hsum := summable_xiZeroCopyReciprocalSquare_pow 1
  calc
    (∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q ^ 2).re) =
        (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q ^ 2).re := by
      rw [Complex.re_tsum hsum]
    _ = (xiCentralReciprocalMoment 1).re := by
      rw [tsum_xiZeroCopyReciprocalSquare_pow 1]
    _ = normalizedPrimeArchMoment 1 := by
      have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 1
      simpa [normalizedPrimeArchMoment, normalizedPrimeArchMomentGerm] using
        congrArg Complex.re hsource.symm

/-- One reciprocal fourth-trace atom in the compact edge corner exceeds one quarter of the global
source threshold. -/
theorem thirtyNine_over_fourHundredThousand_lt_xiFourthReciprocalTraceAtom_of_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 100) :
    (39 / 400000 : ℝ) < (xiZeroCopyReciprocalSquare q ^ 2).re := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let w : ℝ := u + v
  let W : ℝ := 401 / 4
  have hu0 : 0 < u := by
    exact (by norm_num : (0 : ℝ) < 1 / 5).trans
      (by simpa only [u] using huLower)
  have hv0 : 0 < v := by linarith
  have huU : u < 1 / 4 := by simpa only [u] using huUpper
  have hvU : v < 100 := by simpa only [v] using hvUpper
  have hw0 : 0 < w := by dsimp only [w]; positivity
  have hwLower : 85 < w := by dsimp only [w]; linarith
  have hwUpper : w < W := by dsimp only [w, W]; linarith
  have hW0 : 0 < W := by dsimp only [W]; norm_num
  have hsqUpper : w ^ 2 < W ^ 2 := by
    exact (sq_lt_sq₀ hw0.le hW0.le).2 hwUpper
  have hsecond : 0 < 39 * (W ^ 2 + w ^ 2) - 400000 := by
    have hsqLower : (85 : ℝ) ^ 2 < w ^ 2 :=
      (sq_lt_sq₀ (by norm_num) hw0.le).2 hwLower
    dsimp only [W] at hsqLower ⊢
    nlinarith
  have hshape :
      400000 * w ^ 2 - 39 * w ^ 4 >
        400000 * W ^ 2 - 39 * W ^ 4 := by
    have hprod := mul_pos (sub_pos.mpr hsqUpper) hsecond
    have hid :
        (400000 * w ^ 2 - 39 * w ^ 4) -
            (400000 * W ^ 2 - 39 * W ^ 4) =
          (W ^ 2 - w ^ 2) * (39 * (W ^ 2 + w ^ 2) - 400000) := by
      ring
    nlinarith
  have huv : u * v < 25 := by
    calc
      u * v < (1 / 4 : ℝ) * v :=
        mul_lt_mul_of_pos_right (by simpa only [u] using huUpper) hv0
      _ < (1 / 4 : ℝ) * 100 :=
        mul_lt_mul_of_pos_left (by simpa only [v] using hvUpper) (by norm_num)
      _ = 25 := by norm_num
  have hendpoint :
      0 < (400000 * W ^ 2 - 39 * W ^ 4) - 80000000 := by
    norm_num [W]
  have hG :
      0 < 400000 * (v ^ 2 - 6 * u * v + u ^ 2) - 39 * w ^ 4 := by
    have hN : v ^ 2 - 6 * u * v + u ^ 2 = w ^ 2 - 8 * u * v := by
      dsimp only [w]
      ring
    rw [hN]
    nlinarith
  have hformula :
      (xiZeroCopyReciprocalSquare q ^ 2).re =
        (v ^ 2 - 6 * u * v + u ^ 2) / w ^ 4 := by
    rw [pow_two, Complex.mul_re, xiZeroCopyReciprocalSquare_re_formula,
      xiZeroCopyReciprocalSquare_im_formula]
    simp only [u, v, w]
    have hden : u + v ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [hformula]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 400000) (pow_pos hw0 4)]
  nlinarith

/-- Four distinct FE--Schwarz copies of a corner zero would overspend the complete fourth trace. -/
theorem thirtyNine_over_oneHundredThousand_lt_source_of_edgeCorner
    (q : XiZeroCopy)
    (huLower : (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2)
    (huUpper : ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4)
    (hvLower : 85 < (q.1 : ℂ).im ^ 2)
    (hvUpper : (q.1 : ℂ).im ^ 2 < 100) :
    (39 / 100000 : ℝ) < normalizedPrimeArchMoment 1 := by
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
    intro h
    rw [h] at huLower
    norm_num at huLower
  let qJ := xiZeroCopyLineConjEquiv q
  let qC := xiZeroCopyConjEquiv q
  let qCJ := xiZeroCopyLineConjEquiv qC
  let s : Finset XiZeroCopy := {q, qJ, qC, qCJ}
  have hqJ : q ≠ qJ := by
    simpa only [qJ] using xiZeroCopy_ne_lineConj_of_re_ne_half q hoff
  have hqC : q ≠ qC := by
    simpa only [qC] using xiZeroCopy_ne_conj q
  have hqCJ : q ≠ qCJ := by
    simpa only [qC, qCJ] using xiZeroCopy_ne_lineConjConj q
  have hqJqC : qJ ≠ qC := by
    simpa only [qJ, qC] using xiZeroCopy_lineConj_ne_conj q
  have hqJqCJ : qJ ≠ qCJ := by
    simpa only [qJ, qC, qCJ] using xiZeroCopy_lineConj_ne_lineConjConj q
  have hqCqCJ : qC ≠ qCJ := by
    simpa only [qC, qCJ] using
      xiZeroCopy_conj_ne_lineConjConj_of_re_ne_half q hoff
  have hsum : Summable
      (fun r : XiZeroCopy => (xiZeroCopyReciprocalSquare r ^ 2).re) :=
    (summable_xiZeroCopyReciprocalSquare_pow 1).mapL Complex.reCLM
  have hle := hsum.sum_le_tsum s (fun r _ => xiFourthReciprocalTraceAtom_nonneg r)
  have hJ : (xiZeroCopyReciprocalSquare qJ ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simpa only [qJ] using xiFourthReciprocalTraceAtom_lineConj q
  have hCq : (xiZeroCopyReciprocalSquare qC ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simpa only [qC] using xiFourthReciprocalTraceAtom_conj q
  have hCJ : (xiZeroCopyReciprocalSquare qCJ ^ 2).re =
      (xiZeroCopyReciprocalSquare q ^ 2).re := by
    calc
      (xiZeroCopyReciprocalSquare qCJ ^ 2).re =
          (xiZeroCopyReciprocalSquare qC ^ 2).re := by
        simpa only [qC, qCJ] using xiFourthReciprocalTraceAtom_lineConj qC
      _ = (xiZeroCopyReciprocalSquare q ^ 2).re := hCq
  have hfinite :
      ∑ r ∈ s, (xiZeroCopyReciprocalSquare r ^ 2).re =
        4 * (xiZeroCopyReciprocalSquare q ^ 2).re := by
    simp only [s]
    rw [Finset.sum_insert (by simp [hqJ, hqC, hqCJ]),
      Finset.sum_insert (by simp [hqJqC, hqJqCJ]),
      Finset.sum_insert (by simp [hqCqCJ]), Finset.sum_singleton,
      hJ, hCq, hCJ]
    ring
  rw [hfinite, tsum_xiFourthReciprocalTraceAtom_eq_source] at hle
  have hatom :=
    thirtyNine_over_fourHundredThousand_lt_xiFourthReciprocalTraceAtom_of_edgeCorner
      q huLower huUpper hvLower hvUpper
  nlinarith

/-- **Unconditional compact-corner exclusion.** -/
theorem not_exists_xiZeroCopy_mem_orderFourteen_edgeCorner :
    ¬ ∃ q : XiZeroCopy,
      (1 / 5 : ℝ) < ((q.1 : ℂ).re - 1 / 2) ^ 2 ∧
      ((q.1 : ℂ).re - 1 / 2) ^ 2 < 1 / 4 ∧
      85 < (q.1 : ℂ).im ^ 2 ∧
      (q.1 : ℂ).im ^ 2 < 100 := by
  rintro ⟨q, huLower, huUpper, hvLower, hvUpper⟩
  have hlower := thirtyNine_over_oneHundredThousand_lt_source_of_edgeCorner
    q huLower huUpper hvLower hvUpper
  have hupper := normalizedPrimeArchMoment_one_lt_nine_over_twentyFiveThousand
  linarith

/-- The first formerly unprotected squared-seam order is in fact strictly positive everywhere. -/
theorem xiOrderFifteenReciprocalPower_re_pos
    (q : XiZeroCopy) {y : ℝ} (hy : 1 / 4 < y) :
    let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    0 < ((((A : ℂ) - B * I)⁻¹) ^ 15).re := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · let A : ℝ := (q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2 + y
    let B : ℝ := 2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im
    have hA : 0 < A := by
      dsimp only [A]
      rw [hoff]
      norm_num
      nlinarith [sq_nonneg (q.1 : ℂ).im]
    apply orderFifteenReciprocalPower_re_pos_of_sectorRatio hA
    rw [hoff]
    norm_num
    exact sq_pos_of_pos hA
  · by_contra hnot
    have hcorner := xiOrderFifteenReciprocalPower_nonpos_mem_edgeCorner q hoff hy
      (le_of_not_gt hnot)
    exact not_exists_xiZeroCopy_mem_orderFourteen_edgeCorner ⟨q, hcorner⟩

end

end RHTower
