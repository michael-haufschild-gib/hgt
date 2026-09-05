import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport
import GaloisForLFunctions.RHTower.HedenmalmGraviAxionGapLaw
import GaloisForLFunctions.RHTower.StationaryRecurrenceSupportIntervalLaw
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian state-dependent spectral gap

A noncompact Gaussian realization of Proposition 1 and Corollary 1 of arXiv:2609.04191.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard real Gaussian used as a continuous baby-universe state. -/
def standardGaussianBabyUniverseMeasure : Measure ℝ := gaussianReal 0 1

/-- Unit-coupling conditional mass squared `|α|`. -/
def gaussianConditionalMassSq (alpha : ℝ) : ℝ := |alpha|

theorem continuous_gaussianConditionalMassSq : Continuous gaussianConditionalMassSq := by
  change Continuous fun alpha : ℝ => |alpha|
  exact continuous_abs

theorem measurable_gaussianConditionalMassSq : Measurable gaussianConditionalMassSq :=
  continuous_gaussianConditionalMassSq.measurable

/-- Ensemble spectral measure obtained by pushing the Gaussian state through `|α|`. -/
def gaussianGraviAxionSpectralMeasure : Measure ℝ :=
  Measure.map gaussianConditionalMassSq standardGaussianBabyUniverseMeasure

theorem standardGaussianBabyUniverseMeasure_support :
    standardGaussianBabyUniverseMeasure.support = Set.univ := by
  have hOne : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← Measure.support_eq_univ (μ := (volume : Measure ℝ))]
  exact (gaussianReal_absolutelyContinuous' 0 hOne).support_mono

theorem gaussianGraviAxionSpectralMeasure_support :
    gaussianGraviAxionSpectralMeasure.support = Ici (0 : ℝ) := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Ici
    rw [mem_ae_iff]
    rw [gaussianGraviAxionSpectralMeasure,
      Measure.map_apply measurable_gaussianConditionalMassSq
        measurableSet_Ici.compl]
    have hpre : gaussianConditionalMassSq ⁻¹' (Ici (0 : ℝ))ᶜ = ∅ := by
      ext alpha
      simp [gaussianConditionalMassSq]
    rw [hpre]
    simp
  · intro y hy
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    have hpreOpen : IsOpen (gaussianConditionalMassSq ⁻¹' V) :=
      hVopen.preimage continuous_gaussianConditionalMassSq
    have hy0 : 0 ≤ y := hy
    have hyAbs : gaussianConditionalMassSq y = y := by
      simp [gaussianConditionalMassSq, abs_of_nonneg hy0]
    have hpreNhd : gaussianConditionalMassSq ⁻¹' V ∈ 𝓝 y :=
      hpreOpen.mem_nhds (by simpa [hyAbs] using hyV)
    have hySupport : y ∈ standardGaussianBabyUniverseMeasure.support := by
      rw [standardGaussianBabyUniverseMeasure_support]
      exact mem_univ y
    have hpos : 0 < standardGaussianBabyUniverseMeasure
        (gaussianConditionalMassSq ⁻¹' V) :=
      (Measure.mem_support_iff_forall y).mp hySupport _ hpreNhd
    have hmapPos : 0 < gaussianGraviAxionSpectralMeasure V := by
      rw [gaussianGraviAxionSpectralMeasure,
        Measure.map_apply measurable_gaussianConditionalMassSq
          hVopen.measurableSet]
      exact hpos
    exact lt_of_lt_of_le hmapPos (measure_mono hVU)

theorem lowerSpectralEdge_gaussianGraviAxionSpectralMeasure :
    lowerSpectralEdge gaussianGraviAxionSpectralMeasure = 0 := by
  rw [lowerSpectralEdge, gaussianGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le (bddBelow_Ici) Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

theorem gaussianConditionalMassSq_ae_pos :
    ∀ᵐ alpha ∂standardGaussianBabyUniverseMeasure,
      0 < gaussianConditionalMassSq alpha := by
  rw [standardGaussianBabyUniverseMeasure]
  have hOne : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  letI : NullSingletonClass (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    nullSingletonClass_gaussianReal hOne
  simp [gaussianConditionalMassSq, ae_iff, abs_pos]

theorem integrable_gaussianConditionalMassSq :
    Integrable gaussianConditionalMassSq standardGaussianBabyUniverseMeasure := by
  rw [standardGaussianBabyUniverseMeasure]
  have hid : Integrable (fun alpha : ℝ => alpha) (gaussianReal 0 1) := by
    apply integrable_of_mem_interior_integrableExpSet
    simp
  change Integrable (fun alpha : ℝ => |alpha|) (gaussianReal 0 1)
  exact hid.abs

theorem integral_gaussianConditionalMassSq_pos :
    0 < ∫ alpha, gaussianConditionalMassSq alpha ∂standardGaussianBabyUniverseMeasure := by
  apply (integral_pos_iff_support_of_nonneg
    (fun alpha => abs_nonneg alpha) integrable_gaussianConditionalMassSq).2
  rw [show Function.support (fun alpha : ℝ => |alpha|) = ({0} : Set ℝ)ᶜ by
    ext alpha
    simp [Function.support]]
  rw [standardGaussianBabyUniverseMeasure]
  have hOne : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  letI : NullSingletonClass (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    nullSingletonClass_gaussianReal hOne
  rw [MeasureTheory.measure_compl (measurableSet_singleton 0) (by finiteness), measure_singleton]
  simp

/-- Positive spectral residue preserving every support point. -/
def gaussianGraviAxionResidue (massSq : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp massSq)

theorem measurable_gaussianGraviAxionResidue : Measurable gaussianGraviAxionResidue := by
  exact ENNReal.measurable_ofReal.comp Real.continuous_exp.measurable

theorem gaussianGraviAxionResidue_ne_zero (massSq : ℝ) :
    gaussianGraviAxionResidue massSq ≠ 0 := by
  simp [gaussianGraviAxionResidue, ENNReal.ofReal_eq_zero,
    not_le, Real.exp_pos]

def gaussianResidueWeightedGraviAxionSpectralMeasure : Measure ℝ :=
  gaussianGraviAxionSpectralMeasure.withDensity gaussianGraviAxionResidue

theorem gaussianResidueWeightedGraviAxionSpectralMeasure_support :
    gaussianResidueWeightedGraviAxionSpectralMeasure.support = Ici (0 : ℝ) := by
  rw [gaussianResidueWeightedGraviAxionSpectralMeasure,
    support_withDensity_eq gaussianGraviAxionSpectralMeasure
      measurable_gaussianGraviAxionResidue
      (Filter.Eventually.of_forall gaussianGraviAxionResidue_ne_zero),
    gaussianGraviAxionSpectralMeasure_support]

theorem lowerSpectralEdge_gaussianResidueWeightedGraviAxionSpectralMeasure :
    lowerSpectralEdge gaussianResidueWeightedGraviAxionSpectralMeasure = 0 := by
  rw [lowerSpectralEdge, gaussianResidueWeightedGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le (bddBelow_Ici) Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

/-- Gaussian version of the paper's central effect: positive mass almost surely and positive mean,
but zero lower spectral edge before and after strictly positive residue reweighting. -/
theorem gaussian_positiveMean_gapless_package :
    (∀ᵐ alpha ∂standardGaussianBabyUniverseMeasure,
        0 < gaussianConditionalMassSq alpha) ∧
      0 < ∫ alpha, gaussianConditionalMassSq alpha ∂standardGaussianBabyUniverseMeasure ∧
      lowerSpectralEdge gaussianGraviAxionSpectralMeasure = 0 ∧
      lowerSpectralEdge gaussianResidueWeightedGraviAxionSpectralMeasure = 0 := by
  exact ⟨gaussianConditionalMassSq_ae_pos,
    integral_gaussianConditionalMassSq_pos,
    lowerSpectralEdge_gaussianGraviAxionSpectralMeasure,
    lowerSpectralEdge_gaussianResidueWeightedGraviAxionSpectralMeasure⟩

end
end RHTower
