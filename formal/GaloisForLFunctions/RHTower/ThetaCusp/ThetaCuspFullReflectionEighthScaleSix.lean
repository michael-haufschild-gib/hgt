import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthScaleSixBound
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthLargeWeight

/-!
# Scale-six chamber for eighth reflected curvature

The scale-local likelihood estimate `J₆ < 3700` replaces the global loss budget `63232`.  Exact
positive-coefficient profile certificates then preserve the Born top determinant from first-atom
weight `q = 9/2`.  The favorable eighth likelihood channel yields native D1 positivity, and a
finite Taylor lower bound puts every source `x ≥ 13/40` in this chamber.
-/

namespace RHTower

noncomputable section

/-- First-atom rank-three baseline after the scale-six local sixth-jet loss. -/
def thetaCuspFirstAtomEighthScaleSixLossBaseline (q : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
    (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
    (thetaCuspFirstAtomFourthProfile q)
    (thetaCuspFirstAtomSixthProfile q - 3700)
    (thetaCuspFirstAtomEighthProfile q)

/-- The scale-six loss baseline is strict from first-atom weight `9/2`. -/
theorem thetaCuspFirstAtomEighthScaleSixLossBaseline_pos_of_nineHalves_le
    {q : ℝ} (hq : (9 / 2 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthScaleSixLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) * thetaCuspFirstAtomEighthScaleSixLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthScaleSixLossBaseline,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 9 / 2 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Curvature transport bracket for the scale-six loss is strict from weight `9/2`. -/
theorem thetaCuspFirstAtomEighthScaleSixLossCurvatureBracket_pos_of_nineHalves_le
    {q : ℝ} (hq : (9 / 2 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 3700
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
      48 * Aw * Cw - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (16 : ℕ) *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ (2 : ℕ) +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 3700) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 9 / 2 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Derivative bracket for scale-six curvature transport is strict from weight `9/2`. -/
theorem thetaCuspFirstAtomEighthScaleSixLossCurvatureBracketDerivative_pos_of_nineHalves_le
    {q : ℝ} (hq : (9 / 2 : ℝ) ≤ q) :
    let Aw := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 3700
    0 < 2 * Aw * (1152 * Aw ^ (2 : ℕ) - 672 * B0) + 48 * Cw := by
  have hqpos : 0 < q := by linarith
  let y := q - 9 / 2
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (10 : ℕ) *
      (2 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (1152 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
            672 * thetaCuspFirstAtomFourthProfile q) +
        48 * (thetaCuspFirstAtomSixthProfile q - 3700)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 9 / 2 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 10]

/-- Full Born-top determinant is strict throughout the scale-six weight chamber. -/
theorem thetaCuspFullReflectionEighthBornTopBaseline_pos_of_nineHalves_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (9 / 2 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthBornTopBaseline x := by
  let q := thetaCuspBornWittenWeight 1 x
  let As := thetaCuspSingleAtomReflectionScale 1 x
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
  let Cw := C0 - 3700
  have hq : (9 / 2 : ℝ) ≤ q := by simpa only [q] using hqBound
  have hqSupport : (41 / 25 : ℝ) ≤ q := by linarith
  have hqpos : 0 < q := by linarith
  have hAsq : As = q + 3 / 2 := by
    dsimp only [As, q, thetaCuspSingleAtomReflectionScale]
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
  have hA6 : 6 ≤ As := by rw [hAsq]; linarith
  have hA0profile : A0 = thetaCuspFirstAtomCurvatureProfile q := by
    dsimp only [A0, q]
    rw [thetaCuspBornWittenLogCurvature_eq_readoutProfile (by norm_num) hx]
    rfl
  have hB0profile : B0 = thetaCuspFirstAtomFourthProfile q := by
    dsimp only [B0, q]
    rfl
  have hC0profile : C0 = thetaCuspFirstAtomSixthProfile q := by
    change
      (2 * q + 3) * (32 + 48 / q ^ (2 : ℕ) + 2160 / q ^ (3 : ℕ) +
        16200 / q ^ (4 : ℕ) + 38880 / q ^ (5 : ℕ) + 29160 / q ^ (6 : ℕ)) =
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
  have hB0upper : B0 ≤ (6 / 5 : ℝ) * A0 ^ (2 : ℕ) := by
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
  have he6upper : e6 < 3700 := by
    simpa only [e6] using
      thetaCuspLikelihoodSourceLogPartitionJetSix_lt_threeThousandSevenHundred_of_six_le_scale
        hx hA6
  have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
  have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
  have hBB0 : B < B0 := by dsimp only [B]; linarith
  have hCwC : Cw < C := by dsimp only [Cw, C]; linarith
  have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
    dsimp only [Aw]
    nlinarith
  have hratioSq : (177 / 190 : ℝ) ^ (2 : ℕ) * A0 ^ (2 : ℕ) ≤ Aw ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (177 / 190) * A0)
      hAwRatio 2
    simpa only [mul_pow] using hpow
  have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ (2 : ℕ) := by
    have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ) := by norm_num
    have hA0sq : 0 < A0 ^ (2 : ℕ) := by positivity
    have hstrict : (6 / 5 : ℝ) * A0 ^ (2 : ℕ) <
        ((7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ)) * A0 ^ (2 : ℕ) :=
      mul_lt_mul_of_pos_right hcoef hA0sq
    nlinarith
  have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only [thetaCuspFirstAtomEighthScaleSixLossBaseline] using
      thetaCuspFirstAtomEighthScaleSixLossBaseline_pos_of_nineHalves_le hq
  have hCcoefWorst : 0 < 128 * Aw ^ (3 : ℕ) - 2 * C0 := by
    dsimp only [Aw]
    rw [hA0profile, hC0profile]
    exact thetaCuspFirstAtomEighthSixthLossCoefficient_pos hqSupport
  have hCcoef : 0 < 128 * Aw ^ (3 : ℕ) - C - Cw := by
    dsimp only [C, Cw]
    nlinarith
  have hCmono : thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 <
      thetaCuspReflectedEighthPolynomial Aw B0 C D0 := by
    have hdiff :
        thetaCuspReflectedEighthPolynomial Aw B0 C D0 -
            thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 =
          (C - Cw) * (128 * Aw ^ (3 : ℕ) - C - Cw) := by
      unfold thetaCuspReflectedEighthPolynomial
      ring
    rw [← sub_pos, hdiff]
    exact mul_pos (sub_pos.mpr hCwC) hCcoef
  have hG : 0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
      48 * Aw * Cw - D0 := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile, hD0profile]
    simpa only using
      thetaCuspFirstAtomEighthScaleSixLossCurvatureBracket_pos_of_nineHalves_le hq
  have hJ : 0 < 2 * Aw * (1152 * Aw ^ (2 : ℕ) - 672 * B0) + 48 * Cw := by
    dsimp only [Aw, Cw]
    rw [hA0profile, hB0profile, hC0profile]
    simpa only using
      thetaCuspFirstAtomEighthScaleSixLossCurvatureBracketDerivative_pos_of_nineHalves_le hq
  have hK : 0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D0 := by
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

/-- Native D1 is strict whenever first-atom weight is at least `9/2`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineHalves_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (9 / 2 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hbase :=
    thetaCuspFullReflectionEighthBornTopBaseline_pos_of_nineHalves_le_weight hx hqBound
  have hA : 0 < thetaCuspFullReflectedLogCurvature x := by
    have hfirst := nineteen_le_thetaCuspBornWittenLogCurvature
      (n := 1) (by norm_num) hx
    have he2 := thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths hx
    unfold thetaCuspFullReflectedLogCurvature
    linarith
  have hcoef : 0 < 4 * thetaCuspFullReflectedLogCurvature x ^ (2 : ℕ) -
      thetaCuspFullReflectedLogFourthJet x := by
    have hfourth := thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq hx
    nlinarith [sq_pos_of_pos hA]
  have he8 := thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
  rw [thetaCuspFullReflectionEighthHankelCurvature_eq_baseline_add_likelihoodGain]
  exact add_pos hbase (mul_pos hcoef he8)

/-- Exact Taylor certificate placing `x = 13/40` in the scale-six chamber. -/
theorem six_lt_pi_mul_exp_thirteenTwentieths :
    (6 : ℝ) < Real.pi * Real.exp (13 / 20 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 13 / 20) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := Real.pi_gt_d20
  calc
    (6 : ℝ) <
        (3.14159265358979323846 : ℝ) *
          (4119177168059 / 2150400000000 : ℝ) := by
      norm_num
    _ ≤ Real.pi * Real.exp (13 / 20 : ℝ) := by gcongr

/-- Native D1 is strict on the complete source half-line `x ≥ 13/40`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_thirteenFortieths_le
    {x : ℝ} (hx : (13 / 40 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (13 / 20 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (6 : ℝ) < Real.pi * Real.exp (2 * x) :=
    six_lt_pi_mul_exp_thirteenTwentieths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (9 / 2 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineHalves_le_weight
    hx0 hqBound

end

end RHTower
