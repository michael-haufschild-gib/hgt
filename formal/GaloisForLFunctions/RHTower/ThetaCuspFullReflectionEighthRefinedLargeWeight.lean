import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthLargeWeight

/-!
# Refined large-weight chamber for eighth reflected curvature

The uniform sixth-likelihood budget used by the large-weight argument already fits the exact
first-atom rank-three polynomial at weight `19/4`, not merely at weight `5`.  Three independent
positive-coefficient certificates propagate this sharper boundary through the baseline and its
curvature monotonicity.  An eighth-order Taylor lower bound for the source exponential then puts
every `x ≥ 69/200` in the refined chamber.
-/

namespace RHTower

noncomputable section

/-- The worst uniform sixth-jet loss still leaves a strict first-atom baseline from weight
`19/4`. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossBaseline_pos_of_nineteen_fourths_le
    {q : ℝ} (hq : (19 / 4 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthWorstSixthLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 19 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 16 * thetaCuspFirstAtomEighthWorstSixthLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthWorstSixthLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 19 / 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The curvature derivative bracket for the worst uniform sixth loss is positive from weight
`19/4`. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos_of_nineteen_fourths_le
    {q : ℝ} (hq : (19 / 4 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 63232
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * Aw * Cw - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 19 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 16 *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 4 -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ 2 +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 63232) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 19 / 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The derivative of the refined worst-loss curvature bracket is positive from weight
`19/4`. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos_of_nineteen_fourths_le
    {q : ℝ} (hq : (19 / 4 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 63232
    0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B0) + 48 * Cw := by
  have hqpos : 0 < q := by linarith
  let y := q - 19 / 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 10 *
      (2 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (1152 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
            672 * thetaCuspFirstAtomFourthProfile q) +
        48 * (thetaCuspFirstAtomSixthProfile q - 63232)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 19 / 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 10]

/-- Full Born-top baseline is strict whenever the first-atom weight is at least `19/4`. -/
theorem thetaCuspFullReflectionEighthBornTopBaseline_pos_of_nineteen_fourths_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (19 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthBornTopBaseline x := by
  let q := thetaCuspBornWittenWeight 1 x
  let A0 := thetaCuspBornWittenLogCurvature 1 x
  let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
  let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
  let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
  let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
  let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
  let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
  let A := A0 - e2
  let B := B0 - e4
  let C := C0 - e6
  let Aw := A0 - 13 / 10
  let Cw := C0 - 63232
  have hq : (19 / 4 : ℝ) ≤ q := by simpa only [q] using hqBound
  have hqSupport : (41 / 25 : ℝ) ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ 2 + 2160 / q ^ 3 +
        16200 / q ^ 4 + 38880 / q ^ 5 + 29160 / q ^ 6) =
        thetaCuspFirstAtomSixthProfile q
    dsimp only [thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    ring
  have hD0profile : D0 = thetaCuspFirstAtomEighthProfile q := by
    dsimp only [D0, q, thetaCuspBornWittenLogEighthDerivative,
      thetaCuspFirstAtomEighthProfile]
  have hA0 : (19 : ℝ) ≤ A0 := by
    simpa only [A0] using
      nineteen_le_thetaCuspBornWittenLogCurvature (n := 1) (by norm_num) hx
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ 2 := by
    simpa only [A0, B0] using
      thetaCuspBornWittenLogFourthDerivative_le_sixFifths_curvature_sq
        (n := 1) (by norm_num) hx
  have he2upper : e2 ≤ (13 / 10 : ℝ) := by
    simpa only [e2] using
      thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
  have he4pos : 0 < e4 := by
    simpa only [e4] using thetaCuspLikelihoodSourceLogPartitionJetFour_pos hx
  have he6pos : 0 < e6 := by
    simpa only [e6] using thetaCuspLikelihoodSourceLogPartitionJetSix_pos hx
  have he6upper : e6 < 63232 := by
    simpa only [e6] using
      thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyThreeThousandTwoHundredThirtyTwo hx
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hBB0 : B < B0 := by dsimp only [B]; linarith
  have hCwC : Cw < C := by dsimp only [Cw, C]; linarith
  have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
    dsimp only [Aw]
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ 2 * A0 ^ 2 ≤ Aw ^ 2 := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hAwRatio 2
    simpa only [mul_pow] using hpow
  have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ 2 := by
    have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ 2 := by norm_num
    have hA0sq : 0 < A0 ^ 2 := by positivity
    have hstrict : (6 / 5 : ℝ) * A0 ^ 2 <
        ((7 / 5 : ℝ) * (177 / 190) ^ 2) * A0 ^ 2 :=
      mul_lt_mul_of_pos_right hcoef hA0sq
    nlinarith
  have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only [thetaCuspFirstAtomEighthWorstSixthLossBaseline] using
      thetaCuspFirstAtomEighthWorstSixthLossBaseline_pos_of_nineteen_fourths_le hq
  have hCcoefWorst : 0 < 128 * Aw ^ 3 - 2 * C0 := by
    dsimp only [Aw]
    rw [hA0profile, hC0profile]
    exact thetaCuspFirstAtomEighthSixthLossCoefficient_pos hqSupport
  have hCcoef : 0 < 128 * Aw ^ 3 - C - Cw := by
    dsimp only [C, Cw]
    nlinarith
  have hCmono : thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 <
      thetaCuspReflectedEighthPolynomial Aw B0 C D0 := by
    have hdiff :
        thetaCuspReflectedEighthPolynomial Aw B0 C D0 -
            thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 =
          (C - Cw) * (128 * Aw ^ 3 - C - Cw) := by
      unfold thetaCuspReflectedEighthPolynomial
      ring
    rw [← sub_pos, hdiff]
    exact mul_pos (sub_pos.mpr hCwC) hCcoef
  have hG : 0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * Aw * Cw - D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only using
      thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos_of_nineteen_fourths_le hq
  have hJ : 0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B0) + 48 * Cw := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile]
    simpa only using
      thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos_of_nineteen_fourths_le hq
  have hK : 0 < 1344 * Aw ^ 4 - 608 * Aw ^ 2 * B0 + 204 * B0 ^ 2 - D0 := by
    dsimp only [Aw]
    rw [hA0profile, hB0profile, hD0profile]
    simpa only using thetaCuspFirstAtomEighthFourthDisplacementConstant_pos hqSupport
  have hAmono : thetaCuspReflectedEighthPolynomial Aw B0 C D0 ≤
      thetaCuspReflectedEighthPolynomial A B0 C D0 :=
    thetaCuspReflectedEighthPolynomial_mono_curvature_of_lower_sixth
      hAwpos hAwA hB0Aw hCwC.le hG hJ
  have hBmono : thetaCuspReflectedEighthPolynomial A B0 C D0 <
      thetaCuspReflectedEighthPolynomial A B C D0 :=
    thetaCuspReflectedEighthPolynomial_strictAnti_fourth hAwpos hAwA hBB0 hB0Aw hK
  change 0 < thetaCuspReflectedEighthPolynomial A B C D0
  exact ((hbase.trans hCmono).trans_le hAmono).trans hBmono

/-- Favorable eighth likelihood channel makes native D1 strict above first-atom weight
`19/4`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineteen_fourths_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (19 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hbase :=
    thetaCuspFullReflectionEighthBornTopBaseline_pos_of_nineteen_fourths_le_weight
      hx hqBound
  have hA : 0 < thetaCuspFullReflectedLogCurvature x := by
    have hfirst := nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
    have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
    unfold thetaCuspFullReflectedLogCurvature
    linarith
  have hcoef : 0 < 4 * thetaCuspFullReflectedLogCurvature x ^ 2 -
      thetaCuspFullReflectedLogFourthJet x := by
    have hfourth := thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq hx
    nlinarith [sq_pos_of_pos hA]
  have he8 := thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain]
  exact add_pos hbase (mul_pos hcoef he8)

/-- Exact rational Taylor certificate placing `x = 69/200` inside the refined weight
chamber. -/
theorem twentyFiveFourths_lt_pi_mul_exp_sixtyNineHundredths :
    (25 / 4 : ℝ) < Real.pi * Real.exp (69 / 100 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 69 / 100) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := Real.pi_gt_d20
  calc
    (25 / 4 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (111647992627109921 / 56000000000000000 : ℝ) := by
      norm_num
    _ ≤ Real.pi * Real.exp (69 / 100 : ℝ) := by gcongr

/-- Native D1 is strictly positive on the complete refined large-source half-line
`x ≥ 69/200`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_sixtyNineTwoHundredths_le
    {x : ℝ} (hx : (69 / 200 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (69 / 100 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (25 / 4 : ℝ) < Real.pi * Real.exp (2 * x) :=
    twentyFiveFourths_lt_pi_mul_exp_sixtyNineHundredths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (19 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact
    thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineteen_fourths_le_weight
      hx0 hqBound

end

end RHTower
