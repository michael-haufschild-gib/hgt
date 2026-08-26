import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthSourceUpperOrientation
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodSixthScoreRayTransform

open MeasureTheory Set

namespace RHTower

noncomputable section

theorem integrable_thetaLikelihoodSixthScore_mul_exp_neg_higherSpectral
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ =>
      thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t)))
      thetaCuspHigherLikelihoodSpectralMeasure := by
  have h6 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 6 hB).const_mul
    (A ^ 6)
  have h5 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB).const_mul
    (15 * A ^ 5)
  have h4 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB).const_mul
    (65 * A ^ 4)
  have h3 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB).const_mul
    (90 * A ^ 3)
  have h2 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB).const_mul
    (31 * A ^ 2)
  have h1 := (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB).const_mul A
  convert ((((h6.sub h5).add h4).sub h3).add h2).sub h1 using 1
  funext t
  unfold thetaLikelihoodSixthScore
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

set_option maxHeartbeats 1600000 in
theorem thetaCuspLikelihoodSourceOrdinaryJetSix_eq_spectralIntegral
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceOrdinaryJetSix x =
      64 / thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) *
        (∫ t : ℝ,
          thetaLikelihoodSixthScore
              (thetaCuspSingleAtomReflectionScale 1 x * t) *
            Real.exp (-(thetaCuspLikelihoodCoordinate x * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) := by
  let A := thetaCuspSingleAtomReflectionScale 1 x
  let B := thetaCuspLikelihoodCoordinate x
  let P := thetaCuspLikelihoodPartition B
  have hB : 0 < B := by simpa only [B] using thetaCuspLikelihoodCoordinate_pos hx
  have h6 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 6 hB
  have h5 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 5 hB
  have h4 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 4 hB
  have h3 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 3 hB
  have h2 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 2 hB
  have h1 := integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure 1 hB
  have hscore :
      (∫ t : ℝ, thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =
        A ^ 6 * thetaCuspHigherLikelihoodSpectralMoment B 6 -
          15 * A ^ 5 * thetaCuspHigherLikelihoodSpectralMoment B 5 +
          65 * A ^ 4 * thetaCuspHigherLikelihoodSpectralMoment B 4 -
          90 * A ^ 3 * thetaCuspHigherLikelihoodSpectralMoment B 3 +
          31 * A ^ 2 * thetaCuspHigherLikelihoodSpectralMoment B 2 -
          A * thetaCuspHigherLikelihoodSpectralMoment B 1 := by
    unfold thetaLikelihoodSixthScore
    rw [show (fun t : ℝ =>
        ((A * t) ^ 6 - 15 * (A * t) ^ 5 + 65 * (A * t) ^ 4 -
          90 * (A * t) ^ 3 + 31 * (A * t) ^ 2 - A * t) *
            Real.exp (-(B * t))) =
      fun t => A ^ 6 * (t ^ 6 * Real.exp (-(B * t))) -
        (15 * A ^ 5) * (t ^ 5 * Real.exp (-(B * t))) +
        (65 * A ^ 4) * (t ^ 4 * Real.exp (-(B * t))) -
        (90 * A ^ 3) * (t ^ 3 * Real.exp (-(B * t))) +
        (31 * A ^ 2) * (t ^ 2 * Real.exp (-(B * t))) -
        A * (t ^ 1 * Real.exp (-(B * t))) by funext t; ring]
    let f6 : ℝ → ℝ := fun t => A ^ 6 * (t ^ 6 * Real.exp (-(B * t)))
    let f5 : ℝ → ℝ := fun t => (15 * A ^ 5) * (t ^ 5 * Real.exp (-(B * t)))
    let f4 : ℝ → ℝ := fun t => (65 * A ^ 4) * (t ^ 4 * Real.exp (-(B * t)))
    let f3 : ℝ → ℝ := fun t => (90 * A ^ 3) * (t ^ 3 * Real.exp (-(B * t)))
    let f2 : ℝ → ℝ := fun t => (31 * A ^ 2) * (t ^ 2 * Real.exp (-(B * t)))
    let f1 : ℝ → ℝ := fun t => A * (t ^ 1 * Real.exp (-(B * t)))
    have hf6 : Integrable f6 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f6, neg_mul] using h6.const_mul (A ^ 6)
    have hf5 : Integrable f5 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f5, neg_mul] using h5.const_mul (15 * A ^ 5)
    have hf4 : Integrable f4 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f4, neg_mul] using h4.const_mul (65 * A ^ 4)
    have hf3 : Integrable f3 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f3, neg_mul] using h3.const_mul (90 * A ^ 3)
    have hf2 : Integrable f2 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f2, neg_mul] using h2.const_mul (31 * A ^ 2)
    have hf1 : Integrable f1 thetaCuspHigherLikelihoodSpectralMeasure := by
      simpa only [f1, neg_mul] using h1.const_mul A
    rw [show (fun t : ℝ =>
        A ^ 6 * (t ^ 6 * Real.exp (-(B * t))) -
          15 * A ^ 5 * (t ^ 5 * Real.exp (-(B * t))) +
          65 * A ^ 4 * (t ^ 4 * Real.exp (-(B * t))) -
          90 * A ^ 3 * (t ^ 3 * Real.exp (-(B * t))) +
          31 * A ^ 2 * (t ^ 2 * Real.exp (-(B * t))) -
          A * (t ^ 1 * Real.exp (-(B * t)))) =
        ((((f6 - f5) + f4) - f3) + f2) - f1 by
      funext t
      simp only [Pi.add_apply, Pi.sub_apply, f6, f5, f4, f3, f2, f1]]
    rw [integral_sub' (((hf6.sub hf5).add hf4).sub hf3 |>.add hf2) hf1,
      integral_add' ((hf6.sub hf5).add hf4 |>.sub hf3) hf2,
      integral_sub' ((hf6.sub hf5).add hf4) hf3,
      integral_add' (hf6.sub hf5) hf4,
      integral_sub' hf6 hf5]
    simp only [f6, f5, f4, f3, f2, f1, integral_const_mul]
    have hM (m : ℕ) :
        (∫ t : ℝ, t ^ m * Real.exp (-(B * t))
          ∂thetaCuspHigherLikelihoodSpectralMeasure) =
          thetaCuspHigherLikelihoodSpectralMoment B m := by
      rw [thetaCuspHigherLikelihoodSpectralMoment_eq_integral]
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      ring
    rw [hM 6, hM 5, hM 4, hM 3, hM 2, hM 1]
  rw [thetaCuspLikelihoodSourceOrdinaryJetSix]
  dsimp only [A, B, P] at hscore ⊢
  rw [hscore]
  unfold thetaCuspLikelihoodNormalizedMoment thetaCuspLikelihoodMean
  ring

theorem thetaCuspLikelihoodSixthScoreIntegral_eq_tsum_atom
    (A : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspHigherLikelihoodSpectralMeasure) =
      ∑' k : ℕ, ∫ t : ℝ,
        thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))
        ∂thetaCuspAtomLikelihoodSpectralMeasure (k + 2) := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure,
    integral_sum_measure
      (integrable_thetaLikelihoodSixthScore_mul_exp_neg_higherSpectral A hB)]

end

end RHTower
