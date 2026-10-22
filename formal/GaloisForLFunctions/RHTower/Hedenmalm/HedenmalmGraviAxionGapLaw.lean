import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaIndexInfinite
import GaloisForLFunctions.RHTower.StationaryRecurrenceSupportIntervalLaw

/-!
# State-dependent spectral gap on the existing unit-interval source

A closed corpus realization of Proposition 1 and Corollary 1 of arXiv:2609.04191.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unit-slope conditional mass squared on the Hedenmalm parameter state. -/
def unitIntervalConditionalMassSq (alpha : ℝ) : ℝ := alpha

/-- Pushforward spectral measure of conditional mass squared. -/
def unitIntervalGraviAxionSpectralMeasure : Measure ℝ :=
  Measure.map unitIntervalConditionalMassSq unitIntervalMeasure

/-- Lower edge of a real spectral measure. -/
def lowerSpectralEdge (mu : Measure ℝ) : ℝ := sInf mu.support

theorem unitIntervalMeasure_support :
    unitIntervalMeasure.support = Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Icc
    rw [unitIntervalMeasure]
    exact ae_restrict_mem measurableSet_Icc
  · rw [← closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    apply closure_minimal _ Measure.isClosed_support
    intro x hx
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    have hne : (V ∩ Ioo (0 : ℝ) 1).Nonempty := ⟨x, hxV, hx⟩
    have hvolne : volume (V ∩ Ioo (0 : ℝ) 1) ≠ 0 :=
      hVopen.inter isOpen_Ioo |>.measure_ne_zero volume hne
    have hvolpos : 0 < volume (V ∩ Ioo (0 : ℝ) 1) := bot_lt_iff_ne_bot.mpr hvolne
    have hsmall : V ∩ Ioo (0 : ℝ) 1 ⊆ V ∩ Icc (0 : ℝ) 1 := by
      intro y hy
      exact ⟨hy.1, hy.2.1.le, hy.2.2.le⟩
    have hVpos : 0 < unitIntervalMeasure V := by
      rw [unitIntervalMeasure, Measure.restrict_apply hVopen.measurableSet]
      exact lt_of_lt_of_le hvolpos (measure_mono hsmall)
    exact lt_of_lt_of_le hVpos (measure_mono hVU)

theorem unitIntervalGraviAxionSpectralMeasure_eq :
    unitIntervalGraviAxionSpectralMeasure = unitIntervalMeasure := by
  rw [unitIntervalGraviAxionSpectralMeasure]
  change Measure.map (fun x : ℝ => x) unitIntervalMeasure = unitIntervalMeasure
  simp

theorem unitIntervalGraviAxionSpectralMeasure_support :
    unitIntervalGraviAxionSpectralMeasure.support = Icc (0 : ℝ) 1 := by
  rw [unitIntervalGraviAxionSpectralMeasure_eq, unitIntervalMeasure_support]

theorem lowerSpectralEdge_unitIntervalGraviAxionSpectralMeasure :
    lowerSpectralEdge unitIntervalGraviAxionSpectralMeasure = 0 := by
  rw [lowerSpectralEdge, unitIntervalGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le (bddBelow_Icc) ⟨le_rfl, zero_le_one⟩
  · apply le_csInf
    · exact nonempty_Icc.mpr zero_le_one
    · intro x hx
      exact hx.1

/-- Strictly positive sector residue testing the paper's weighted spectral measure. -/
def unitIntervalGraviAxionResidue (alpha : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp alpha)

/-- Residue-weighted ensemble spectral measure. -/
def unitIntervalResidueWeightedGraviAxionSpectralMeasure : Measure ℝ :=
  unitIntervalGraviAxionSpectralMeasure.withDensity unitIntervalGraviAxionResidue

theorem measurable_unitIntervalGraviAxionResidue :
    Measurable unitIntervalGraviAxionResidue := by
  exact ENNReal.measurable_ofReal.comp Real.continuous_exp.measurable

theorem unitIntervalGraviAxionResidue_ne_zero (alpha : ℝ) :
    unitIntervalGraviAxionResidue alpha ≠ 0 := by
  simp [unitIntervalGraviAxionResidue, ENNReal.ofReal_eq_zero,
    not_le, Real.exp_pos]

theorem unitIntervalResidueWeightedGraviAxionSpectralMeasure_support :
    unitIntervalResidueWeightedGraviAxionSpectralMeasure.support = Icc (0 : ℝ) 1 := by
  rw [unitIntervalResidueWeightedGraviAxionSpectralMeasure,
    support_withDensity_eq unitIntervalGraviAxionSpectralMeasure
      measurable_unitIntervalGraviAxionResidue
      (Filter.Eventually.of_forall unitIntervalGraviAxionResidue_ne_zero),
    unitIntervalGraviAxionSpectralMeasure_support]

theorem lowerSpectralEdge_unitIntervalResidueWeightedGraviAxionSpectralMeasure :
    lowerSpectralEdge unitIntervalResidueWeightedGraviAxionSpectralMeasure = 0 := by
  rw [lowerSpectralEdge, unitIntervalResidueWeightedGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le (bddBelow_Icc) ⟨le_rfl, zero_le_one⟩
  · apply le_csInf
    · exact nonempty_Icc.mpr zero_le_one
    · intro x hx
      exact hx.1

theorem unitIntervalConditionalMassSq_ae_pos :
    ∀ᵐ alpha ∂unitIntervalMeasure, 0 < unitIntervalConditionalMassSq alpha := by
  have hmem : ∀ᵐ alpha ∂unitIntervalMeasure, alpha ∈ Icc (0 : ℝ) 1 := by
    rw [unitIntervalMeasure]
    exact ae_restrict_mem measurableSet_Icc
  have hne : ∀ᵐ alpha ∂unitIntervalMeasure, alpha ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hmem, hne] with alpha halpha hne
  exact lt_of_le_of_ne halpha.1 (Ne.symm hne)

theorem integral_unitIntervalConditionalMassSq :
    ∫ alpha, unitIntervalConditionalMassSq alpha ∂unitIntervalMeasure = 1 / 2 := by
  have h := integral_unitInterval_coordinate
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa [unitIntervalConditionalMassSq] using h)

theorem integral_unitIntervalConditionalMassSq_pos :
    0 < ∫ alpha, unitIntervalConditionalMassSq alpha ∂unitIntervalMeasure := by
  rw [integral_unitIntervalConditionalMassSq]
  positivity

/-- Existing Hedenmalm source realizes the paper's central phenomenon: almost every conditional
mass is positive and the mean is positive, while the ensemble lower spectral edge is zero. -/
theorem unitInterval_positiveMean_gapless_package :
    (∀ᵐ alpha ∂unitIntervalMeasure, 0 < unitIntervalConditionalMassSq alpha) ∧
      0 < ∫ alpha, unitIntervalConditionalMassSq alpha ∂unitIntervalMeasure ∧
      lowerSpectralEdge unitIntervalGraviAxionSpectralMeasure = 0 := by
  exact ⟨unitIntervalConditionalMassSq_ae_pos,
    integral_unitIntervalConditionalMassSq_pos,
    lowerSpectralEdge_unitIntervalGraviAxionSpectralMeasure⟩

end
end RHTower
