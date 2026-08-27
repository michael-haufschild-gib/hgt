import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScoreRayTransform

open MeasureTheory Set

/-!
# Coefficient-faithful sixth-score bound for the dominant higher theta atom

The square-gap atom `n = 2` dominates every sixth-order higher-likelihood estimate near the
modular seam.  Bounding its score by the leading sixth monomial loses the reflected-Hankel
margin.  Here the mixed Dirac/ray mass is evaluated exactly and bounded through the positive
shifted-score Taylor operator instead.
-/

namespace RHTower

noncomputable section

/-- Literal sixth-score mass of the first higher theta atom. -/
def thetaCuspLikelihoodDominantAtomSixthScoreMass (A B : ℝ) : ℝ :=
  ∫ t : ℝ, thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
    ∂thetaCuspAtomLikelihoodSpectralMeasure 2

/-- Exact mixed Dirac/ray evaluation for the square-gap-three atom. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_eq
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B =
      16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScore (3 * A) * Real.exp (-(3 * B))) +
        18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9)) := by
  let f : ℝ → ℝ := fun t =>
    thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
  have hd : Integrable f (Measure.dirac (3 : ℝ)) := integrable_dirac (by
    dsimp [f]
    finiteness)
  have hr : Integrable f (volume.restrict (Ioi (3 : ℝ))) := by
    change IntegrableOn f (Ioi (3 : ℝ))
    simpa only [f] using
      integrableOn_thetaLikelihoodSixthScore_mul_exp_neg_rate
        A (d := (3 : ℝ)) (by norm_num) hB
  have hd' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) • Measure.dirac (3 : ℝ)) :=
    hd.smul_measure (by simp)
  have hr' : Integrable f
      (ENNReal.ofReal (thetaCuspLikelihoodRayWeight 2) •
        volume.restrict (Ioi (3 : ℝ))) := hr.smul_measure (by simp)
  rw [thetaCuspLikelihoodDominantAtomSixthScoreMass,
    thetaCuspAtomLikelihoodSpectralMeasure]
  norm_num [thetaCuspLikelihoodGap] at hd' hr' ⊢
  rw [integral_add_measure hd' hr', integral_smul_measure, integral_dirac,
    integral_smul_measure]
  change ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2)) * f 3 +
      ENNReal.toReal (ENNReal.ofReal (thetaCuspLikelihoodRayWeight 2)) *
        (∫ t : ℝ in Ioi 3, f t) = _
  rw [ENNReal.toReal_ofReal (thetaCuspLikelihoodAtomWeight_pos (by norm_num)).le,
    ENNReal.toReal_ofReal (thetaCuspLikelihoodRayWeight_pos (by norm_num)).le,
    integral_Ioi_thetaLikelihoodSixthScore_mul_exp_neg_rate A 3 hB]
  dsimp [f]
  norm_num [thetaCuspLikelihoodAtomWeight, thetaCuspLikelihoodRayWeight,
    thetaCuspLikelihoodGap]
  ring_nf

/-- Uniform same-aperture bound for the dominant score mass.  The exponent `471/50` is the
rational seam `9 + 21/50`; every displayed constant comes from the literal atom and ray weights. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_le_seamEnvelope_sharp
    (A : ℝ) {B : ℝ} (hA : (157 / 50 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B ≤
      (16 * 50000 + 18 * (25 / 41 : ℝ) * 950000) *
        Real.exp (-(471 / 50 : ℝ)) := by
  have hB : 0 < B := by rw [hBA]; linarith
  have hy : (21 / 50 : ℝ) ≤ 3 * A - 9 := by linarith
  let s := 3 * A - 9 - 21 / 50
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hyrw : 3 * A - 9 = 21 / 50 + s := by dsimp [s]; ring
  have hr0 : 0 ≤ A / B := div_nonneg (by linarith) hB.le
  have hr : A / B ≤ (48 / 25 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hpinv : 1 / B ≤ (25 / 41 : ℝ) := by
    apply (div_le_iff₀ hB).2
    rw [hBA]
    nlinarith
  have hqmono :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9) ≤
        thetaLikelihoodSixthScoreRayTransformPolynomial (48 / 25) (3 * A - 9) := by
    dsimp only [thetaLikelihoodSixthScoreRayTransformPolynomial]
    have hp1 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivOne (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivOne]
      positivity
    have hp2 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivTwo (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivTwo]
      positivity
    have hp3 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivThree (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivThree]
      positivity
    have hp4 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivFour (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivFour]
      positivity
    have hp5 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivFive (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivFive]
      positivity
    have hp6 : 0 ≤ thetaLikelihoodSixthScoreShiftDerivSix (3 * A - 9) := by
      dsimp [thetaLikelihoodSixthScoreShiftDerivSix]
      positivity
    have hr2 := pow_le_pow_left₀ hr0 hr 2
    have hr3 := pow_le_pow_left₀ hr0 hr 3
    have hr4 := pow_le_pow_left₀ hr0 hr 4
    have hr5 := pow_le_pow_left₀ hr0 hr 5
    have hr6 := pow_le_pow_left₀ hr0 hr 6
    have ht1 := mul_le_mul_of_nonneg_right hr hp1
    have ht2 := mul_le_mul_of_nonneg_right hr2 hp2
    have ht3 := mul_le_mul_of_nonneg_right hr3 hp3
    have ht4 := mul_le_mul_of_nonneg_right hr4 hp4
    have ht5 := mul_le_mul_of_nonneg_right hr5 hp5
    have ht6 := mul_le_mul_of_nonneg_right hr6 hp6
    nlinarith
  have hq :
      thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9) ≤
        950000 * Real.exp s := by
    calc
      _ ≤ thetaLikelihoodSixthScoreRayTransformPolynomial
          (48 / 25) (3 * A - 9) := hqmono
      _ = thetaLikelihoodSixthScoreRayTransformPolynomial
          (48 / 25) (21 / 50 + s) := by rw [hyrw]
      _ ≤ _ := thetaLikelihoodSixthScoreRayTransformPolynomial_seam_envelope_sharp hs
  have hp : thetaLikelihoodSixthScore (3 * A) ≤ 50000 * Real.exp s := by
    rw [thetaLikelihoodSixthScore_eq_shiftNine, hyrw]
    exact thetaLikelihoodSixthScoreShift_seam_envelope hs
  have hpoint :
      16 * Real.exp (-(9 / 2 : ℝ)) *
          (thetaLikelihoodSixthScore (3 * A) * Real.exp (-(3 * B))) ≤
        (16 * 50000) * Real.exp (-(471 / 50 : ℝ)) := by
    calc
      _ ≤ 16 * Real.exp (-(9 / 2 : ℝ)) *
          ((50000 * Real.exp s) * Real.exp (-(3 * B))) := by gcongr
      _ = _ := by
        rw [show 16 * Real.exp (-(9 / 2 : ℝ)) *
            ((50000 * Real.exp s) * Real.exp (-(3 * B))) =
          16 * 50000 * (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) *
            Real.exp s) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        rw [hBA]
        dsimp [s]
        ring
  have hray :
      18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) / B *
            thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (3 * A - 9)) ≤
        (18 * (25 / 41 : ℝ) * 950000) * Real.exp (-(471 / 50 : ℝ)) := by
    calc
      _ ≤ 18 * Real.exp (-(9 / 2 : ℝ)) *
          (Real.exp (-(3 * B)) * (25 / 41 : ℝ) *
            (950000 * Real.exp s)) := by
          have hq0 : 0 ≤ thetaLikelihoodSixthScoreRayTransformPolynomial
              (A / B) (3 * A - 9) := by
            dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
              thetaLikelihoodSixthScoreShift,
              thetaLikelihoodSixthScoreShiftDerivOne,
              thetaLikelihoodSixthScoreShiftDerivTwo,
              thetaLikelihoodSixthScoreShiftDerivThree,
              thetaLikelihoodSixthScoreShiftDerivFour,
              thetaLikelihoodSixthScoreShiftDerivFive,
              thetaLikelihoodSixthScoreShiftDerivSix]
            positivity
          calc
            _ = 18 * Real.exp (-(9 / 2 : ℝ)) *
                (Real.exp (-(3 * B)) * (1 / B) *
                  thetaLikelihoodSixthScoreRayTransformPolynomial
                    (A / B) (3 * A - 9)) := by ring
            _ ≤ 18 * Real.exp (-(9 / 2 : ℝ)) *
                (Real.exp (-(3 * B)) * (25 / 41 : ℝ) *
                  thetaLikelihoodSixthScoreRayTransformPolynomial
                    (A / B) (3 * A - 9)) := by gcongr
            _ ≤ _ := by gcongr
      _ = _ := by
        rw [show 18 * Real.exp (-(9 / 2 : ℝ)) *
            (Real.exp (-(3 * B)) * (25 / 41 : ℝ) *
              (950000 * Real.exp s)) =
          (18 * (25 / 41 : ℝ) * 950000) *
            (Real.exp (-(9 / 2 : ℝ)) * Real.exp (-(3 * B)) *
              Real.exp s) by ring]
        rw [← Real.exp_add, ← Real.exp_add]
        rw [hBA]
        dsimp [s]
        ring
  rw [thetaCuspLikelihoodDominantAtomSixthScoreMass_eq A hB]
  nlinarith

/-- Compatibility form with the original round ray constant. -/
theorem thetaCuspLikelihoodDominantAtomSixthScoreMass_le_seamEnvelope
    (A : ℝ) {B : ℝ} (hA : (157 / 50 : ℝ) ≤ A)
    (hBA : B = A - 3 / 2) :
    thetaCuspLikelihoodDominantAtomSixthScoreMass A B ≤
      (16 * 50000 + 18 * (25 / 41 : ℝ) * 1000000) *
        Real.exp (-(471 / 50 : ℝ)) := by
  have h := thetaCuspLikelihoodDominantAtomSixthScoreMass_le_seamEnvelope_sharp
    A hA hBA
  have he := Real.exp_pos (-(471 / 50 : ℝ))
  nlinarith

end

end RHTower
