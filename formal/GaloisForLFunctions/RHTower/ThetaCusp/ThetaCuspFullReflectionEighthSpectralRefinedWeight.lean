import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthRefinedLargeWeight
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthSixthSpectralReserve

/-!
# Spectrally refined large-weight chamber for eighth reflected curvature

The fixed higher-theta spectrum makes the literal eighth likelihood jet dominate `1/69` times
squared scale times the sixth jet.  The exact particle-grade budget also lowers the uniform sixth
loss from `63232` to `62928`.  Keeping both improvements inside the native reflected polynomial
lowers the exact uniform-loss chamber from first-atom weight `19/4` to `467/100`.  The curvature
transport certificates remain positive there.  An exact finite Taylor lower bound then places
every source `x ≥ 169/500` in this refined chamber.
-/

namespace RHTower

noncomputable section

/-- Native worst-sixth profile after retaining the spectral fraction of the eighth gain. -/
def thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline (q : ℝ) : ℝ :=
  thetaCuspReflectedEighthPolynomial
      (thetaCuspFirstAtomCurvatureProfile q - 13 / 10)
      (thetaCuspFirstAtomFourthProfile q)
      (thetaCuspFirstAtomSixthProfile q - 62928)
      (thetaCuspFirstAtomEighthProfile q) +
    62928 * thetaCuspFullReflectionEighthCompactEighthCoefficient q *
      (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)

/-- The spectrally compensated uniform-loss baseline is strict from weight `467/100`. -/
theorem thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline_pos_of_fourHundredSixtySevenHundredths_le
    {q : ℝ} (hq : (467 / 100 : ℝ) ≤ q) :
    0 < thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline q := by
  have hqpos : 0 < q := by linarith
  let y := q - 467 / 100
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hmul : 0 < q ^ (16 : ℕ) *
      thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline q := by
    dsimp [thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspReflectedEighthPolynomial,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 467 / 100 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The worst-sixth curvature bracket remains strict at the spectrally refined boundary. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos_of_fourHundredSixtySevenHundredths_le
    {q : ℝ} (hq : (467 / 100 : ℝ) ≤ q) :
    let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 62928
    let D0 := thetaCuspFirstAtomEighthProfile q
    0 < 576 * W ^ (4 : ℕ) - 672 * W ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
      48 * W * Cw - D0 := by
  have hqpos : 0 < q := by linarith
  let y := q - 467 / 100
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (16 : ℕ) *
      (576 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (4 : ℕ) -
        672 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) *
          thetaCuspFirstAtomFourthProfile q +
        76 * thetaCuspFirstAtomFourthProfile q ^ (2 : ℕ) +
        48 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (thetaCuspFirstAtomSixthProfile q - 62928) -
        thetaCuspFirstAtomEighthProfile q) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile, thetaCuspFirstAtomEighthProfile]
    field_simp [hqpos.ne']
    rw [show q = 467 / 100 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 16]

/-- The derivative bracket needed for curvature transport is strict from weight `467/100`. -/
theorem thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos_of_fourHundredSixtySevenHundredths_le
    {q : ℝ} (hq : (467 / 100 : ℝ) ≤ q) :
    let W := thetaCuspFirstAtomCurvatureProfile q - 13 / 10
    let B0 := thetaCuspFirstAtomFourthProfile q
    let Cw := thetaCuspFirstAtomSixthProfile q - 62928
    0 < 2 * W * (1152 * W ^ (2 : ℕ) - 672 * B0) + 48 * Cw := by
  have hqpos : 0 < q := by linarith
  let y := q - 467 / 100
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  dsimp only
  have hmul : 0 < q ^ (10 : ℕ) *
      (2 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) *
          (1152 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (2 : ℕ) -
            672 * thetaCuspFirstAtomFourthProfile q) +
        48 * (thetaCuspFirstAtomSixthProfile q - 62928)) := by
    dsimp [thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 467 / 100 + y by dsimp only [y]; ring]
    ring_nf
    positivity
  nlinarith [pow_pos hqpos 10]

/-- Effective native sixth-loss coefficient after subtracting the guaranteed spectral eighth
gain. -/
def thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient (q : ℝ) : ℝ :=
  128 * (thetaCuspFirstAtomCurvatureProfile q - 13 / 10) ^ (3 : ℕ) -
    2 * thetaCuspFirstAtomSixthProfile q -
    thetaCuspFullReflectionEighthCompactEighthCoefficient q *
      (1 / 69) * (q + 3 / 2) ^ (2 : ℕ)

/-- The effective loss coefficient is positive throughout the only new chamber. -/
theorem thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient_pos
    {q : ℝ} (hq : (467 / 100 : ℝ) ≤ q) (hqUpper : q < 19 / 4) :
    0 < thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient q := by
  have hqpos : 0 < q := by linarith
  let y := q - 467 / 100
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hyUpper : y < 2 / 25 := by dsimp only [y]; linarith
  have htailFactor : 0 < 2247731200 - 256000 * y := by nlinarith
  have htail : 0 ≤ y ^ (9 : ℕ) * (2247731200 - 256000 * y) := by positivity
  have hy2 : 0 ≤ y ^ (2 : ℕ) := by positivity
  have hy3 : 0 ≤ y ^ (3 : ℕ) := by positivity
  have hy4 : 0 ≤ y ^ (4 : ℕ) := by positivity
  have hy5 : 0 ≤ y ^ (5 : ℕ) := by positivity
  have hy6 : 0 ≤ y ^ (6 : ℕ) := by positivity
  have hy7 : 0 ≤ y ^ (7 : ℕ) := by positivity
  have hy8 : 0 ≤ y ^ (8 : ℕ) := by positivity
  have hmul : 0 < q ^ (6 : ℕ) *
      thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient q := by
    dsimp [thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient,
      thetaCuspFullReflectionEighthCompactEighthCoefficient,
      thetaCuspFirstAtomCurvatureProfile, thetaCuspFirstAtomFourthProfile,
      thetaCuspFirstAtomSixthProfile]
    field_simp [hqpos.ne']
    rw [show q = 467 / 100 + y by dsimp only [y]; ring]
    ring_nf
    nlinarith [htail]
  nlinarith [pow_pos hqpos 6]

/-- Native D1 is strict whenever first-atom weight is at least `467/100`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_fourHundredSixtySevenHundredths_le_weight
    {x : ℝ} (hx : 0 ≤ x)
    (hqBound : (467 / 100 : ℝ) ≤ thetaCuspBornWittenWeight 1 x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  by_cases hqLarge : (19 / 4 : ℝ) ≤ thetaCuspBornWittenWeight 1 x
  · exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_nineteen_fourths_le_weight
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
    let Cw := C0 - 62928
    let K8 := 4 * Aw ^ (2 : ℕ) - B0
    let L := 128 * Aw ^ (3 : ℕ) - 2 * C0 - K8 * (1 / 69) * As ^ (2 : ℕ)
    have hq : (467 / 100 : ℝ) ≤ q := by simpa only [q] using hqBound
    have hqUpper : q < 19 / 4 := by
      simpa only [q, not_le] using hqLarge
    have hqSupport : (41 / 25 : ℝ) ≤ q := by linarith
    have hqpos : 0 < q := by linarith
    have hAsq : As = q + 3 / 2 := by
      dsimp only [As, q, thetaCuspSingleAtomReflectionScale]
      rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
      norm_num
      rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
        rw [show 2 * x = x + x by ring, Real.exp_add]
        ring]
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
    have he6upper : e6 < 62928 := by
      simpa only [e6] using
        thetaCuspLikelihoodSourceLogPartitionJetSix_lt_sixtyTwoThousandNineHundredTwentyEight hx
    have he8pos : 0 < e8 := by
      simpa only [e8] using thetaCuspLikelihoodSourceLogPartitionJetEight_pos hx
    have hcoupling : (1 / 69 : ℝ) * As ^ (2 : ℕ) * e6 < e8 := by
      simpa only [As, e6, e8] using
        oneSixtyNinth_mul_scale_sq_logJetSix_lt_logJetEight hx
    have hAwpos : 0 < Aw := by dsimp only [Aw]; linarith
    have hAwA : Aw ≤ A := by dsimp only [Aw, A]; linarith
    have hBB0 : B < B0 := by dsimp only [B]; linarith
    have hCwC : Cw < C := by dsimp only [Cw, C]; linarith
    have hAwRatio : (177 / 190 : ℝ) * A0 ≤ Aw := by
      dsimp only [Aw]
      nlinarith
    have hratioSq : (177 / 190 : ℝ) ^ (2 : ℕ) * A0 ^ (2 : ℕ) ≤ Aw ^ (2 : ℕ) := by
      have hpow := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ (177 / 190) * A0) hAwRatio 2
      simpa only [mul_pow] using hpow
    have hB0Aw : B0 < (7 / 5 : ℝ) * Aw ^ (2 : ℕ) := by
      have hcoef : (6 / 5 : ℝ) < (7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ) := by norm_num
      have hA0sq : 0 < A0 ^ (2 : ℕ) := by positivity
      have hstrict : (6 / 5 : ℝ) * A0 ^ (2 : ℕ) <
          ((7 / 5 : ℝ) * (177 / 190) ^ (2 : ℕ)) * A0 ^ (2 : ℕ) :=
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
      simpa only [thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient,
        thetaCuspFullReflectionEighthCompactEighthCoefficient] using
      thetaCuspFirstAtomEighthSpectralEffectiveSixthCoefficient_pos hq hqUpper
    have hprofileBase :
        0 < thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline q :=
      thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline_pos_of_fourHundredSixtySevenHundredths_le hq
    have hbaseCompare : thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline q <
        thetaCuspReflectedEighthPolynomial Aw B0 C D := by
      have hgain : 0 < K8 * (e8 - (1 / 69 : ℝ) * As ^ (2 : ℕ) * e6) := by
        exact mul_pos hK8 (sub_pos.mpr hcoupling)
      have hloss : 0 < (62928 - e6) * (L + 62928 + e6) := by positivity
      have htest : thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline q =
          thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 +
            62928 * K8 * (1 / 69) * As ^ (2 : ℕ) := by
        dsimp only [thetaCuspFirstAtomEighthWorstSixthSpectralLossBaseline,
          Aw, Cw, K8]
        rw [hA0profile, hB0profile, hC0profile, hD0profile, hAsq]
        rfl
      rw [htest, ← sub_pos]
      have hdiff :
          thetaCuspReflectedEighthPolynomial Aw B0 C D -
              (thetaCuspReflectedEighthPolynomial Aw B0 Cw D0 +
                62928 * K8 * (1 / 69) * As ^ (2 : ℕ)) =
            K8 * (e8 - (1 / 69) * As ^ (2 : ℕ) * e6) +
              (62928 - e6) * (L + 62928 + e6) := by
        dsimp only [C, D, Cw, L, K8]
        unfold thetaCuspReflectedEighthPolynomial
        ring
      rw [hdiff]
      positivity
    have hbase : 0 < thetaCuspReflectedEighthPolynomial Aw B0 C D :=
      hprofileBase.trans hbaseCompare
    have hG : 0 < 576 * Aw ^ (4 : ℕ) - 672 * Aw ^ (2 : ℕ) * B0 + 76 * B0 ^ (2 : ℕ) +
        48 * Aw * Cw - D := by
      have hprofile :=
        thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracket_pos_of_fourHundredSixtySevenHundredths_le hq
      dsimp only at hprofile
      dsimp only [D, Aw, Cw]
      rw [hA0profile, hB0profile, hC0profile, hD0profile]
      nlinarith
    have hJ : 0 < 2 * Aw * (1152 * Aw ^ (2 : ℕ) - 672 * B0) + 48 * Cw := by
      dsimp only [Aw, Cw]
      rw [hA0profile, hB0profile, hC0profile]
      simpa only using
        thetaCuspFirstAtomEighthWorstSixthLossCurvatureBracketDerivative_pos_of_fourHundredSixtySevenHundredths_le hq
    have hK : 0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 + 204 * B0 ^ (2 : ℕ) - D := by
      have hK0 : 0 < 1344 * Aw ^ (4 : ℕ) - 608 * Aw ^ (2 : ℕ) * B0 +
          204 * B0 ^ (2 : ℕ) - D0 := by
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

/-- Exact rational Taylor certificate placing `x = 169/500` inside the spectral weight chamber. -/
theorem sixHundredSeventeenHundredths_lt_pi_mul_exp_oneHundredSixtyNineTwoHundredFiftieths :
    (617 / 100 : ℝ) < Real.pi * Real.exp (169 / 250 : ℝ) := by
  have he := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 169 / 250) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp := Real.pi_gt_d20
  have hmul := mul_le_mul hp.le he (by norm_num) Real.pi_pos.le
  have htarget : (617 / 100 : ℝ) <
      (3.14159265358979323846 : ℝ) *
        (604774413213484916039 / 307617187500000000000 : ℝ) := by
    norm_num
  exact htarget.trans_le hmul

/-- Native D1 is strictly positive on the complete source half-line `x ≥ 169/500`. -/
theorem thetaCuspFullReflectionEighthHankelCurvature_pos_of_oneHundredSixtyNineFiveHundredths_le
    {x : ℝ} (hx : (169 / 500 : ℝ) ≤ x) :
    0 < thetaCuspFullReflectionEighthHankelCurvature x := by
  have hx0 : 0 ≤ x := by linarith
  have hexp : Real.exp (169 / 250 : ℝ) ≤ Real.exp (2 * x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hprod : (617 / 100 : ℝ) < Real.pi * Real.exp (2 * x) :=
    sixHundredSeventeenHundredths_lt_pi_mul_exp_oneHundredSixtyNineTwoHundredFiftieths.trans_le
      (mul_le_mul_of_nonneg_left hexp Real.pi_pos.le)
  have hqBound : (467 / 100 : ℝ) ≤ thetaCuspBornWittenWeight 1 x := by
    rw [thetaCuspBornWittenWeight_eq, thetaCuspMorseScale]
    norm_num
    rw [show Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring]
    linarith
  exact thetaCuspFullReflectionEighthHankelCurvature_pos_of_fourHundredSixtySevenHundredths_le_weight
    hx0 hqBound

end

end RHTower
