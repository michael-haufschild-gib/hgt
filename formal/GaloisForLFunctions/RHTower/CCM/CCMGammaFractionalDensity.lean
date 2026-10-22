import GaloisForLFunctions.RHTower.CCM.CCMGammaLogTranslationKernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integrable fractional power of the remaining Gamma density

The inverse-lag singularity is not integrable, but its three-quarter power
is. This supplies a finite capacity for testing a uniform absorption of
actual displaced prime mass. No source positivity is inferred.
-/

open MeasureTheory Set Filter
noncomputable section
namespace RHTower

theorem ccmGammaHigherBinetModeDensity_le_exp_div
    (s : {s : ℝ // 0 < s}) :
    ccmGammaHigherBinetModeDensity s ≤ Real.exp (-(s : ℝ) / 2) / (s : ℝ) := by
  have he : Real.exp (2 * (s : ℝ)) * Real.exp (-(2 * (s : ℝ))) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * (s : ℝ)))
    (Real.exp_pos (-(2 * (s : ℝ)))).le
  have hd : (s : ℝ) * Real.exp (-(2 * (s : ℝ))) ≤
      1 - Real.exp (-(2 * (s : ℝ))) := by
    nlinarith [mul_pos s.property (Real.exp_pos (-(2 * (s : ℝ))))]
  have hden : 0 < 1 - Real.exp (-(2 * (s : ℝ))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [s.property]))
  unfold ccmGammaHigherBinetModeDensity
  apply (div_le_div_iff₀ hden s.property).mpr
  have h := mul_le_mul_of_nonneg_left hd (Real.exp_pos (-(s : ℝ) / 2)).le
  simpa only [neg_div, mul_assoc, mul_left_comm, mul_comm] using h

theorem integrableOn_ccmGammaHigherBinetModeDensity_threeQuarters :
    IntegrableOn (fun s : ℝ => ccmGammaHigherBinetModeDensity s ^ (3 / 4 : ℝ))
      (Ioi (0 : ℝ)) := by
  have hmajor : IntegrableOn
      (fun s : ℝ => s ^ (-(3 / 4 : ℝ)) * Real.exp (-(3 / 8 : ℝ) * s))
      (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := -(3 / 4 : ℝ)) (b := (3 / 8 : ℝ))
        (by norm_num) le_rfl (by norm_num))
  refine Integrable.mono' hmajor ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold ccmGammaHigherBinetModeDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      (ccmGammaHigherBinetModeDensity_pos hs).le _)]
    calc
      _ ≤ (Real.exp (-s / 2) / s) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (ccmGammaHigherBinetModeDensity_pos hs).le
          (ccmGammaHigherBinetModeDensity_le_exp_div ⟨s, hs⟩) (by norm_num)
      _ = _ := by
        rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hs),
          Real.log_div (Real.exp_pos _).ne' hs.ne', Real.log_exp,
          Real.rpow_def_of_pos hs, ← Real.exp_add]
        congr 1
        ring

theorem integrable_ccmGammaHigherBinetSymmetricDensity_threeQuarters :
    Integrable (fun r : ℝ => ccmGammaHigherBinetModeDensity |r| ^ (3 / 4 : ℝ)) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hp : IntegrableOn (fun r : ℝ => ccmGammaHigherBinetModeDensity |r| ^ (3 / 4 : ℝ))
      (Ioi (0 : ℝ)) := by
    exact integrableOn_ccmGammaHigherBinetModeDensity_threeQuarters.congr_fun
      (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

end RHTower
