import GaloisForLFunctions.RHTower.MobiusDivisorCriticalPrimeAbelMellinFactorization
import GaloisForLFunctions.RHTower.DivisorSourceEntire

/-!
# Exact first Mellin coefficient of the critical prime source

The critical step source has a simple boundary zero, with coefficient equal
to the positive harmonic boundary of the literal divisor source. The exact
Abel and prime-dilation welds therefore identify the first logarithmic term
of the actual prime head: its coefficient is that boundary divided by three,
and is at least `1/90`. This sharpens the previously existential finite jet;
it does not estimate the remaining finite-cutoff signed residual.
-/

noncomputable section
open Complex Filter Topology MeasureTheory
namespace RHTower

/-- The filled zeta pole exposes the exact vanishing factor of the literal
critical step-source Mellin transform. -/
theorem criticalStepSourceMellin_eq_poleUnit_quotient
    {s : ℂ} (hs : 1 < s.re) :
    criticalStepSourceMellin s =
      (s - 1) * divisorSourceEntire s / (s * zetaPoleUnit s) := by
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  rw [criticalStepSourceMellin_eq_centeredCurrentGap hs,
    ← criticalSourceMellinNumerator_eq_centeredCurrentGap hs,
    divisorSourceEntire_eq hs1, zetaPoleUnit_of_ne hs1]
  simp only [logDeriv, Pi.div_apply]
  field_simp [hs0, sub_ne_zero.mpr hs1, hz]

private theorem source_one :
    divisorSourceEntire 1 = (divisorHarmonicBoundary : ℂ) := by
  rw [divisorSourceEntire_eq_divisorSourceDirichlet (by norm_num),
    divisorSourceDirichlet_one]

private theorem one_add_complex_tendsto :
    Tendsto (fun δ : ℝ => (1 : ℂ) + (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hδ : Tendsto (fun δ : ℝ => (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa using tendsto_const_nhds.add hδ

/-- The first critical Mellin coefficient is the actual positive divisor
boundary, rather than an unspecified nonzero finite-order coefficient. -/
theorem criticalStepSourceMellin_simpleJet :
    Tendsto (fun δ : ℝ =>
      criticalStepSourceMellin (1 + (δ : ℂ)) / (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (divisorHarmonicBoundary : ℂ)) := by
  have hc : ContinuousAt
      (fun s : ℂ => divisorSourceEntire s / (s * zetaPoleUnit s)) 1 :=
    (differentiable_divisorSourceEntire 1).continuousAt.div
      (continuousAt_id.mul (differentiable_zetaPoleUnit 1).continuousAt)
      (by simp [zetaPoleUnit_one])
  have hlim := hc.tendsto.comp one_add_complex_tendsto
  simp only [source_one, zetaPoleUnit_one, mul_one, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  simp only [Function.comp_def]
  have hs : 1 < ((1 : ℂ) + (δ : ℂ)).re := by
    simp only [add_re, one_re, ofReal_re]
    exact lt_add_of_pos_right 1 hδ
  have hδ0 : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hδ)
  rw [criticalStepSourceMellin_eq_poleUnit_quotient hs,
    show (1 : ℂ) + (δ : ℂ) - 1 = (δ : ℂ) by ring]
  field_simp [hδ0]

/-- The literal critical Abel source has an exact first-order Mellin zero
with coefficient `divisorHarmonicBoundary / 3`. -/
theorem criticalAbelMellin_simpleJet :
    Tendsto (fun δ : ℝ =>
      mellin (fun x : ℝ => (criticalContinuousAbel x : ℂ))
        (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) / (δ : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((divisorHarmonicBoundary : ℂ) / 3)) := by
  have hden : Tendsto (fun δ : ℝ => 2 * ((1 : ℂ) + (δ : ℂ)) + 1)
      (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℂ)) := by
    convert ((tendsto_const_nhds (x := (2 : ℂ))).mul one_add_complex_tendsto).add
      (tendsto_const_nhds (x := (1 : ℂ))) using 1
    norm_num
  have hlim := criticalStepSourceMellin_simpleJet.div hden (by norm_num)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  simp only [Pi.div_apply]
  have hs : (3 / 2 : ℝ) < ((1 : ℂ) + (δ : ℂ) + 1 / 2).re := by
    simp only [add_re, one_re, ofReal_re]
    norm_num
    linarith
  rw [(hasMellin_criticalContinuousAbel hs).2,
    show (1 : ℂ) + (δ : ℂ) + 1 / 2 - 1 / 2 = 1 + (δ : ℂ) by ring]
  rw [show 2 * ((1 : ℂ) + (δ : ℂ) + 1 / 2) =
    2 * ((1 : ℂ) + (δ : ℂ)) + 1 by ring]
  simp only [div_eq_mul_inv]
  ring

private theorem one_add_real_tendsto :
    Tendsto (fun δ : ℝ => 1 + δ)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun δ : ℝ => 1 + δ) (𝓝 0) (𝓝 (1 + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    simpa using hδ

/-- The actual all-prime head has a first-order logarithmic Mellin term,
with its positive coefficient fixed by the original arithmetic source. -/
theorem criticalPrimeAbelHead_simpleLogJet :
    Tendsto (fun δ : ℝ =>
      mellin criticalPrimeAbelHead
        (-((1 : ℂ) + (δ : ℂ) + 1 / 2)) /
        (δ : ℂ) / (abscissaLog (1 + δ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((divisorHarmonicBoundary : ℂ) / 3)) := by
  have hprimeR := tendsto_primeZeta_div_abscissaLog.comp one_add_real_tendsto
  have hprimeC : Tendsto
      (fun δ : ℝ => ((primeZeta (1 + δ) / abscissaLog (1 + δ) : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using
      (Complex.continuous_ofReal.tendsto 1).comp hprimeR
  have hlim := criticalAbelMellin_simpleJet.mul hprimeC
  simp only [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  have hσ : 3 / 2 < (1 + δ + 1 / 2 : ℝ) := by linarith
  have harg : -((1 : ℂ) + (δ : ℂ) + 1 / 2) =
      -(((1 + δ + 1 / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [harg, mellin_criticalPrimeAbelHead _ hσ,
    show (1 + δ + 1 / 2 : ℝ) - 1 / 2 = 1 + δ by ring]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Quantitative nonvanishing of the exact prime-head logarithmic coefficient. -/
theorem criticalPrimeAbelHead_simpleLogJet_coefficient_lower :
    (1 / 90 : ℝ) ≤ divisorHarmonicBoundary / 3 := by
  linarith [one_thirtieth_le_divisorHarmonicBoundary]

end RHTower
