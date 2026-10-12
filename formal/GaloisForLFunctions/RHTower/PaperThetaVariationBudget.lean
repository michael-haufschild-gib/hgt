import GaloisForLFunctions.RHTower.PaperThetaSourceRatio

/-! # A decreasing variation budget for the actual source-relative mode

Positive source-ratio differences are integrated before taking norms. This
retains the cancellation needed to telescope over arbitrary partitions.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open ThetaFiniteTransport HedenmalmQuantile

def quotientVariationBudget (z : ℂ) (x : ℝ) : ℝ :=
  ‖z‖ * ∫ h in Ioi (0 : ℝ), sourceRatio h x * Real.exp (-z.im*h)

theorem quotientVariationBudget_nonneg (z : ℂ) (x : ℝ) :
    0 ≤ quotientVariationBudget z x := by
  apply mul_nonneg (norm_nonneg _)
  exact integral_nonneg fun h => mul_nonneg (sourceRatio_pos h x).le (Real.exp_pos _).le

theorem quotientVariationBudget_antitone (z : ℂ) :
    Antitone (quotientVariationBudget z) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  apply setIntegral_mono_on (integrable_sourceRatio_tilt (-z.im) b).integrableOn
    (integrable_sourceRatio_tilt (-z.im) a).integrableOn measurableSet_Ioi
  intro h hh
  exact mul_le_mul_of_nonneg_right (sourceRatio_antitone_all ⟨h, hh.le⟩ hab)
    (Real.exp_pos _).le

private theorem quotient_increment_le {z : ℂ} {a b : ℝ} (hab : a ≤ b) :
    ‖flatQuotient z b - flatQuotient z a‖ ≤
      quotientVariationBudget z a - quotientVariationBudget z b := by
  have hdiff : flatQuotient z b - flatQuotient z a = (Complex.I*z) *
      ∫ h in Ioi (0 : ℝ), ((sourceRatio h a : ℂ) - sourceRatio h b)*sourceChar z h := by
    rw [show (fun h : ℝ => ((sourceRatio h a : ℂ) - sourceRatio h b)*sourceChar z h) =
      (fun h => (sourceRatio h a : ℂ)*sourceChar z h -
        (sourceRatio h b : ℂ)*sourceChar z h) by funext h; ring,
      integral_sub (integrable_sourceRatio_character z a).integrableOn
        (integrable_sourceRatio_character z b).integrableOn]
    calc
      _ = (flatQuotient z b + 1) - (flatQuotient z a + 1) := by ring
      _ = _ := by rw [flatQuotient_eq_sourceRatio_integral,
        flatQuotient_eq_sourceRatio_integral]; ring
  have hn : ∀ᵐ h ∂volume.restrict (Ioi (0 : ℝ)),
      ‖((sourceRatio h a : ℂ) - sourceRatio h b)*sourceChar z h‖ =
        (sourceRatio h a - sourceRatio h b)*Real.exp (-z.im*h) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hmono : sourceRatio h b ≤ sourceRatio h a :=
      sourceRatio_antitone_all ⟨h, hh.le⟩ hab
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hmono),
      norm_sourceChar]
  calc
    _ = ‖z‖ * ‖∫ h in Ioi (0 : ℝ),
        ((sourceRatio h a : ℂ) - sourceRatio h b)*sourceChar z h‖ := by
      rw [hdiff, norm_mul, norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖z‖ * ∫ h in Ioi (0 : ℝ),
        ‖((sourceRatio h a : ℂ) - sourceRatio h b)*sourceChar z h‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = quotientVariationBudget z a - quotientVariationBudget z b := by
      rw [integral_congr_ae hn]
      simp_rw [sub_mul]
      rw [integral_sub (integrable_sourceRatio_tilt (-z.im) a).integrableOn
        (integrable_sourceRatio_tilt (-z.im) b).integrableOn]
      unfold quotientVariationBudget
      ring

/-- The decreasing native budget controls every increment, for every complex parameter. -/
theorem flatQuotient_increment_budget (z : ℂ) (a b : ℝ) :
    ‖flatQuotient z b - flatQuotient z a‖ ≤
      |quotientVariationBudget z b - quotientVariationBudget z a| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (quotientVariationBudget_antitone z hab)), neg_sub]
    exact quotient_increment_le hab
  · rw [norm_sub_rev, abs_of_nonneg (sub_nonneg.mpr (quotientVariationBudget_antitone z hba))]
    exact quotient_increment_le hba

end RHTower.PaperThetaEndpoint
