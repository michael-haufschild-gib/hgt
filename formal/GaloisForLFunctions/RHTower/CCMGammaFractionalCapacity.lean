import GaloisForLFunctions.RHTower.CCMGammaFractionalDensity

/-!
# Fractional capacities for the actual higher Gamma density

Every power strictly between zero and one is integrable. The exponent can
therefore be chosen to test signed completed transport, whose height grows
faster than the unsigned mass lower bound used previously.
-/

open MeasureTheory Set Filter
noncomputable section
namespace RHTower

theorem integrableOn_ccmGammaHigherBinetModeDensity_fractional
    (p : {p : ℝ // 0 < p ∧ p < 1}) :
    IntegrableOn (fun s : ℝ => ccmGammaHigherBinetModeDensity s ^ (p : ℝ))
      (Ioi (0 : ℝ)) := by
  have hmajor : IntegrableOn
      (fun s : ℝ => s ^ (-(p : ℝ)) * Real.exp (-((p : ℝ) / 2) * s))
      (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := -(p : ℝ)) (b := (p : ℝ) / 2)
        (by linarith [p.property.2]) le_rfl (by linarith [p.property.1]))
  refine Integrable.mono' hmajor ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold ccmGammaHigherBinetModeDensity
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
      (ccmGammaHigherBinetModeDensity_pos hs).le _)]
    calc
      _ ≤ (Real.exp (-s / 2) / s) ^ (p : ℝ) :=
        Real.rpow_le_rpow (ccmGammaHigherBinetModeDensity_pos hs).le
          (ccmGammaHigherBinetModeDensity_le_exp_div ⟨s, hs⟩) p.property.1.le
      _ = _ := by
        rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hs),
          Real.log_div (Real.exp_pos _).ne' hs.ne', Real.log_exp,
          Real.rpow_def_of_pos hs, ← Real.exp_add]
        congr 1
        ring

theorem integrable_ccmGammaHigherBinetSymmetricDensity_fractional
    (p : {p : ℝ // 0 < p ∧ p < 1}) :
    Integrable (fun r : ℝ => ccmGammaHigherBinetModeDensity |r| ^ (p : ℝ)) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  have hp : IntegrableOn (fun r : ℝ => ccmGammaHigherBinetModeDensity |r| ^ (p : ℝ))
      (Ioi (0 : ℝ)) :=
    (integrableOn_ccmGammaHigherBinetModeDensity_fractional p).congr_fun
      (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  refine ⟨?_, hp⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using hp

end RHTower
