import GaloisForLFunctions.RHTower.CCM.CCMActualHeadQuantileGammaChiSquareProducer

/-!
# Short-lag Gamma control of the complete translation defect

The higher Binet density retains an inverse-lag lower bound on every fixed
positive interval. The Hilbert translation triangle applies to the whole
complex source, so coefficient cross terms remain inside the squared norm.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- The first Binet mode has already been removed; the remaining Gamma
density still controls the singular inverse-lag weight. -/
theorem one_div_le_ccmGammaHigherBinetModeDensity
    (L : {L : ℝ // 0 < L}) (s : Set.Ioc (0 : ℝ) (L : ℝ)) :
    1 / (s : ℝ) ≤ 2 * Real.exp (5 * (L : ℝ) / 2) *
      ccmGammaHigherBinetModeDensity s := by
  have hs : 0 < (s : ℝ) := s.property.1
  have hd : 0 < 1 - Real.exp (-(2 * (s : ℝ))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden : 1 - Real.exp (-(2 * (s : ℝ))) ≤ 2 * (s : ℝ) := by
    linarith [Real.add_one_le_exp (-(2 * (s : ℝ)))]
  have hnum : Real.exp (-(5 * (L : ℝ) / 2)) ≤
      Real.exp (-(5 * (s : ℝ) / 2)) :=
    Real.exp_le_exp.mpr (by linarith [s.property.2])
  have hlow : Real.exp (-(5 * (L : ℝ) / 2)) / (2 * (s : ℝ)) ≤
      ccmGammaHigherBinetModeDensity s := by
    rw [ccmGammaHigherBinetModeDensity, ← Real.exp_add,
      show -((s : ℝ) / 2) + -(2 * (s : ℝ)) = -(5 * (s : ℝ) / 2) by ring]
    exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hd hden)
  calc
    _ = (2 * Real.exp (5 * (L : ℝ) / 2)) *
        (Real.exp (-(5 * (L : ℝ) / 2)) / (2 * (s : ℝ))) := by
      rw [← mul_div_assoc, mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- Two translated copies bound the full defect at a third lag, with no
dimension, smoothness, or coefficient restriction on the source. -/
theorem ccmActualHeadTranslationDefect_le_two_add (h s : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect h f ≤
      2 * ccmActualHeadTranslationDefect s f +
        2 * ccmActualHeadTranslationDefect (s - h) f := by
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logTranslationCLM h f) (logTranslationCLM s f) f
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hnorm : ‖logTranslationCLM h f - logTranslationCLM s f‖ ^ 2 =
      ccmActualHeadTranslationDefect (s - h) f := by
    rw [norm_logTranslationCLM_sub_logTranslationCLM_eq_sqrt_defect,
      Real.sq_sqrt (by unfold ccmActualHeadTranslationDefect; positivity),
      show h - s = -(s - h) by ring, ccmActualHeadTranslationDefect_neg]
  have haux := sq_nonneg
    (‖logTranslationCLM h f - logTranslationCLM s f‖ - ‖logTranslationCLM s f - f‖)
  unfold ccmActualHeadTranslationDefect at *
  nlinarith only [hsq, haux, hnorm]

end RHTower
