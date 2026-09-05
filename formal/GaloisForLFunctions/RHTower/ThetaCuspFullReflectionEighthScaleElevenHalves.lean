import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScaleElevenHalvesBound
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthScaleSix
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthSpectralRefinedWeight

/-!
# Scale-eleven-halves spectral chamber for eighth reflected curvature

The scale-local bound `J₆ < 1800` and strict spectral coupling
`A_scale² J₆ / 69 < J₈` preserve the native rank-three determinant from first-atom weight `q = 4`.
The prior scale-six theorem handles `q ≥ 9/2`; exact compensated profiles close the bridge strip.
A finite Taylor certificate places every source `x ≥ 281/1000` in this chamber.
-/

namespace RHTower

noncomputable section

/-- Rank-three baseline after the local sixth loss and guaranteed spectral eighth gain. -/
def thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline (q : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
      (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
      (thetaCuspFirstAtomFourthProfile q)
      (thetaCuspFirstAtomSixthProfile q - 1800)
      (thetaCuspFirstAtomEighthProfile q) +
    1800 * thetaCuspFullReflectionEighthCompactEighthCoefficient q *
      (1 / 69) * (q + 3 / 2) ^ 2

/-- The compensated local-loss baseline is strict from weight `4`. -/
theorem thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline_pos_of_four_le
    {q : ℝ} (hq : (4 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ 16 *
      thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Curvature bracket for the scale-eleven-halves loss is strict from weight `4`. -/
theorem thetaCuspFirstAtomEighthScaleElevenHalvesLossCurvatureBracket_pos_of_four_le
    {q : ℝ} (hq : (4 : ℝ) ≤ q) :
    let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 1800
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * W ^ 4 - 672 * W ^ 2 * B0 + 76 * B0 ^ 2 +
      48 * W * Cw - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 16 *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 4 -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ 2 +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 1800) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- Derivative bracket for scale-eleven-halves curvature transport is strict from weight `4`. -/
theorem thetaCuspFirstAtomEighthScaleElevenHalvesLossCurvatureBracketDerivative_pos_of_four_le
    {q : ℝ} (hq : (4 : ℝ) ≤ q) :
    let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 1800
    0 < 2 * W * (1152 * W ^ 2 - 672 * B0) + 48 * Cw := by
  have hqpos : 0 < q := by linarith
  let y := q - 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ 10 *
      (2 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (1152 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 2 -
            672 * thetaCuspFirstAtomFourthProfile q) +
        48 * (thetaCuspFirstAtomSixthProfile q - 1800)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 4 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 10]

/-- Effective sixth-loss coefficient after subtracting the guaranteed spectral eighth gain. -/
def thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient
    (q : ℝ) : ℝ :=
  128 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ 3 -
    2 * thetaCuspFirstAtomSixthProfile q -
    thetaCuspFullReflectionEighthCompactEighthCoefficient q *
      (1 / 69) * (q + 3 / 2) ^ 2

/-- The effective loss coefficient is strict on the bridge strip `4 ≤ q < 9/2`. -/
theorem thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient_pos
    {q : ℝ} (hq : (4 : ℝ) ≤ q) (hqUpper : q < 9 / 2) :
    0 < thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient q := by
  have hqpos : 0 < q := by linarith
  let y := q - 4
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyUpper : y < 1 / 2 := by dsimp only [y]; linarith
  have htailFactor : 0 < 2249446400 - 256000 * y := by nlinarith
  have htail : 0 ≤ y ^ 9 * (2249446400 - 256000 * y) := by positivity
  have hy2 : 0 ≤ y ^ 2 := by positivity
  have hy3 : 0 ≤ y ^ 3 := by positivity
  have hy4 : 0 ≤ y ^ 4 := by positivity
  have hy5 : 0 ≤ y ^ 5 := by positivity
  have hy6 : 0 ≤ y ^ 6 := by positivity
  have hy7 : 0 ≤ y ^ 7 := by positivity
  have hy8 : 0 ≤ y ^ 8 := by positivity
  have hmul : 0 < q ^ 6 *
      thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient q := by
    dsimp [thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 4 + y by dsimp only [y]; ring]
    ring_nf
    nlinarith [htail]
  nlinarith [pow_pos hqpos 6]

/-- Native D1 is strict whenever first-atom weight is at least `4`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_four_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqLarge : (9 / 2 : ℝ) ≤ thetaCuspBornWittenWeight 1 x
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineHalves_le_weight
      hx hqLarge
  · let q := thetaCuspBornWittenWeight 1 x
    let As := thetaCuspSingleAtomReflectionScale 1 x
    let A0 := thetaCuspBornWittenLogCurvature 1 x
    let B0 := thetaCuspBornWittenLogFourthDerivative 1 x
    let C0 := thetaCuspBornWittenLogSixthDerivative 1 x
    let D0 := thetaCuspBornWittenLogEighthDerivative 1 x
    let e2 := thetaCuspLikelihoodSourceLogPartitionJetTwo x
    let e4 := thetaCuspLikelihoodSourceLogPartitionJetFour x
    let e6 := thetaCuspLikelihoodSourceLogPartitionJetSix x
    let e8 := thetaCuspLikelihoodSourceLogPartitionJetEight x
    let A := A0 - e2
    let B := B0 - e4
    let C := C0 - e6
    let D := D0 - e8
    let Aw := A0 - 13 / 10
    let Cw := C0 - 1800
    let K8 := 4 * Aw ^ 2 - B0
    let L := 128 * Aw ^ 3 - 2 * C0 - K8 * (1 / 69) * As ^ 2
    have hq : (4 : ℝ) ≤ q := by simpa only [q] using hqBound
    have hqUpper : q < 9 / 2 := by
      simpa only [q, not_le] using hqLarge
    have hqSupport : (41 / 25 : ℝ) ≤ q := by linarith
    have hqpos : 0 < q := by linarith
    have hAsq : As = q + 3 / 2 := by
      dsimp only [As, q, thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
    have hAsLower : (11 / 2 : ℝ) ≤ As := by rw [hAsq]; linarith
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
    have he6upper : e6 < 1800 := by
      simpa only [e6] using
        thetaCuspLikelihoodSourceLogPartitionJetSix_lt_eighteenHundred_of_elevenHalves_le_scale
          hx hAsLower
    have he8pos : 0 < e8 := by
      simpa only [e8] using thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
    have hcoupling : (1 / 69 : ℝ) * As ^ 2 * e6 < e8 := by
      simpa only [As, e6, e8] using
        oneSixtyNinth_mul_scale_sq_logJetSix_lt_logJetEight hx
    have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
    have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
    have hBB0 : B < B0 := by dsimp only [B]; linarith
    have hCwC : Cw < C := by dsimp only [Cw, C]; linarith
    have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
      dsimp only [Aw]
      nlinarith
    have hratioSq : (177 / 190 : ℝ) ^ 2 * A0 ^ 2 ≤ Aw ^ 2 := by
      have hpow := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ (177 / 190) * A0) hAwRatio 2
      simpa only [mul_pow] using hpow
    have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ 2 := by
      have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ 2 := by norm_num
      have hA0sq : 0 < A0 ^ 2 := by positivity
      have hstrict : (6 / 5 : ℝ) * A0 ^ 2 <
          ((7 / 5 : ℝ) * (177 / 190) ^ 2) * A0 ^ 2 :=
        mul_lt_mul_of_pos_right hcoef hA0sq
      nlinarith
    have hK8 : 0 < K8 := by
      dsimp only [K8, Aw]
      rw [hA0profile, hB0profile]
      simpa only [thetaCuspFullReflectionEighthCompactEighthCoefficient] using
        thetaCuspFullReflectionEighthCompactEighthCoefficient_pos hx
    have hL : 0 < L := by
      dsimp only [L, K8, Aw]
      rw [hA0profile, hB0profile, hC0profile, hAsq]
      simpa only [
        thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient,
        thetaCuspFullReflectionEighthCompactEighthCoefficient] using
        thetaCuspFirstAtomEighthScaleElevenHalvesSpectralEffectiveSixthCoefficient_pos
          hq hqUpper
    have hprofileBase :
        0 < thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline q :=
      thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline_pos_of_four_le hq
    have hbaseCompare :
        thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline q <
          thetaCuspReflectedEighthPolynomial Aw B0 C D := by
      have hgain : 0 < K8 * (e8 - (1 / 69 : ℝ) * As ^ 2 * e6) := by
        exact mul_pos hK8 (sub_pos.mpr hcoupling)
      have hloss : 0 < (1800 - e6) * (L + 1800 + e6) := by positivity
      have htest : thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline q =
          thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 +
            1800 * K8 * (1 / 69) * As ^ 2 := by
        dsimp only [thetaCuspFirstAtomEighthScaleElevenHalvesSpectralLossBaseline,
          Aw, Cw, K8]
        rw [hA0profile, hB0profile, hC0profile, hD0profile, hAsq]
        rfl
      rw [htest, ← sub_pos]
      have hdiff :
          thetaCuspReflectedEighthPolynomial Aw B0 C D -
              (thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 +
                1800 * K8 * (1 / 69) * As ^ 2) =
            K8 * (e8 - (1 / 69) * As ^ 2 * e6) +
              (1800 - e6) * (L + 1800 + e6) := by
        dsimp only [C, D, Cw, L, K8]
        unfold thetaCuspReflectedEighthPolynomial
        ring
      rw [hdiff]
      positivity
    have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 C D :=
      hprofileBase.trans hbaseCompare
    have hG : 0 < 576 * Aw ^ 4 - 672 * Aw ^ 2 * B0 + 76 * B0 ^ 2 +
        48 * Aw * Cw - D := by
      have hprofile :=
        thetaCuspFirstAtomEighthScaleElevenHalvesLossCurvatureBracket_pos_of_four_le hq
      dsimp only at hprofile
      dsimp only [D, Aw, Cw]
      rw [hA0profile, hB0profile, hC0profile, hD0profile]
      nlinarith
    have hJ : 0 < 2 * Aw * (1152 * Aw ^ 2 - 672 * B0) + 48 * Cw := by
      dsimp only [Aw, Cw]
      rw [hA0profile, hB0profile, hC0profile]
      simpa only using
        thetaCuspFirstAtomEighthScaleElevenHalvesLossCurvatureBracketDerivative_pos_of_four_le hq
    have hK : 0 < 1344 * Aw ^ 4 - 608 * Aw ^ 2 * B0 + 204 * B0 ^ 2 - D := by
      have hK0 : 0 < 1344 * Aw ^ 4 - 608 * Aw ^ 2 * B0 +
          204 * B0 ^ 2 - D0 := by
        dsimp only [Aw]
        rw [hA0profile, hB0profile, hD0profile]
        simpa only using thetaCuspFirstAtomEighthFourthDisplacementConstant_pos hqSupport
      dsimp only [D]
      linarith
    have hAmono : thetaCuspReflectedEighthPolynomial Aw B0 C D ≤
        thetaCuspReflectedEighthPolynomial A B0 C D :=
      thetaCuspReflectedEighthPolynomial_mono_curvature_of_lower_sixth
        hAwpos hAwA hB0Aw hCwC.le hG hJ
    have hBmono : thetaCuspReflectedEighthPolynomial A B0 C D <
        thetaCuspReflectedEighthPolynomial A B C D :=
      thetaCuspReflectedEighthPolynomial_strictAnti_fourth
        hAwpos hAwA hBB0 hB0Aw hK
    change 0 < thetaCuspReflectedEighthPolynomial A B C D
    exact (hbase.trans_le hAmono).trans hBmono

/-- Exact Taylor certificate placing `x = 281/1000` in the weight-four chamber. -/
theorem elevenHalves_lt_pi_mul_exp_twoHundredEightyOneFiveHundredths :
    (11 / 2 : ℝ) < Real.pi * Real.exp (281 / 500 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 281 / 500) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := Real.pi_gt_d20
  have hmul := mul_le_mul hp.le he (by norm_num) Real.pi_pos.le
  have htarget : (11 / 2 : ℝ) <
      (3.14159265358979323846 : ℝ) *
        (69070722754879842751861 / 39375000000000000000000 : ℝ) := by
    norm_num
  exact htarget.trans_le hmul

/-- Native D1 is strict on the complete source half-line `x ≥ 281/1000`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_twoHundredEightyOneThousandths_le
    {x : ℝ} (hx : (281 / 1000 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (281 / 500 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (11 / 2 : ℝ) < Real.pi * Real.exp (2 * x) :=
    elevenHalves_lt_pi_mul_exp_twoHundredEightyOneFiveHundredths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ 2 = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_four_le_weight
    hx0 hqBound

end


end RHTower
