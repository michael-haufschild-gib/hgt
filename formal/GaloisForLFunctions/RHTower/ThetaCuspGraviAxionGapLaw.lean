import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport
import GaloisForLFunctions.RHTower.HedenmalmGraviAxionGapLaw
import GaloisForLFunctions.RHTower.ThetaCuspC5SharpTailMeasures

/-!
# Theta-cusp positive spectral gap as a gravi-axion application

The corpus's first higher theta atom supplies a closed positive-gap branch of Proposition 1 in
arXiv:2609.04191: one edge atom plus a continuum ray, with positive residue reweighting.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- First higher theta atom (`n = 2`) as a concrete mixed discrete-continuum spectrum. -/
def thetaCuspFirstHigherGraviAxionSpectralMeasure : Measure ℝ :=
  thetaCuspAtomLikelihoodSpectralMeasure 2

theorem thetaCuspFirstHigherGraviAxionSpectralMeasure_support :
    thetaCuspFirstHigherGraviAxionSpectralMeasure.support = Ici (3 : ℝ) := by
  rw [← thetaCuspLikelihoodGap_two]
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Ici
    rw [mem_ae_iff]
    simp [thetaCuspFirstHigherGraviAxionSpectralMeasure,
      thetaCuspAtomLikelihoodSpectralMeasure]
    right
    rw [show Iio (thetaCuspLikelihoodGap 2) ∩ Ioi (thetaCuspLikelihoodGap 2) = ∅ by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false,
        not_and]
      exact fun ht hgt => (not_lt_of_ge ht.le) hgt]
    exact measure_empty
  · intro y hy
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hyV⟩ := mem_nhds_iff.mp hU
    have hmeasureV : 0 < thetaCuspFirstHigherGraviAxionSpectralMeasure V := by
      by_cases hyEq : y = thetaCuspLikelihoodGap 2
      · subst y
        have hweight : 0 < ENNReal.ofReal (thetaCuspLikelihoodAtomWeight 2) :=
          ENNReal.ofReal_pos.mpr (thetaCuspLikelihoodAtomWeight_pos (by norm_num))
        rw [thetaCuspFirstHigherGraviAxionSpectralMeasure,
          thetaCuspAtomLikelihoodSpectralMeasure, Measure.add_apply,
          Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply_of_mem hyV]
        exact lt_of_lt_of_le (by simpa using hweight) (self_le_add_right _ _)
      · have hyStrict : thetaCuspLikelihoodGap 2 < y :=
          lt_of_le_of_ne hy (Ne.symm hyEq)
        have hne : (V ∩ Ioi (thetaCuspLikelihoodGap 2)).Nonempty :=
          ⟨y, hyV, hyStrict⟩
        have hvol : 0 < volume (V ∩ Ioi (thetaCuspLikelihoodGap 2)) :=
          bot_lt_iff_ne_bot.mpr
            ((hVopen.inter isOpen_Ioi).measure_ne_zero volume hne)
        have hweight : 0 < ENNReal.ofReal (thetaCuspLikelihoodRayWeight 2) :=
          ENNReal.ofReal_pos.mpr (thetaCuspLikelihoodRayWeight_pos (by norm_num))
        rw [thetaCuspFirstHigherGraviAxionSpectralMeasure,
          thetaCuspAtomLikelihoodSpectralMeasure, Measure.add_apply,
          Measure.smul_apply, Measure.smul_apply,
          Measure.restrict_apply hVopen.measurableSet]
        exact lt_of_lt_of_le (ENNReal.mul_pos hweight.ne' hvol.ne')
          (self_le_add_left _ _)
    exact lt_of_lt_of_le hmeasureV (measure_mono hVU)

theorem lowerSpectralEdge_thetaCuspFirstHigherGraviAxionSpectralMeasure :
    lowerSpectralEdge thetaCuspFirstHigherGraviAxionSpectralMeasure = 3 := by
  rw [lowerSpectralEdge, thetaCuspFirstHigherGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le bddBelow_Ici Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

/-- Strictly positive residue on the theta-cusp mixed spectrum. -/
def thetaCuspGraviAxionResidue (massSq : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp massSq)

theorem measurable_thetaCuspGraviAxionResidue : Measurable thetaCuspGraviAxionResidue := by
  exact ENNReal.measurable_ofReal.comp Real.continuous_exp.measurable

theorem thetaCuspGraviAxionResidue_ne_zero (massSq : ℝ) :
    thetaCuspGraviAxionResidue massSq ≠ 0 := by
  simp [thetaCuspGraviAxionResidue, ENNReal.ofReal_eq_zero,
    not_le, Real.exp_pos]

def thetaCuspResidueWeightedGraviAxionSpectralMeasure : Measure ℝ :=
  thetaCuspFirstHigherGraviAxionSpectralMeasure.withDensity thetaCuspGraviAxionResidue

theorem thetaCuspResidueWeightedGraviAxionSpectralMeasure_support :
    thetaCuspResidueWeightedGraviAxionSpectralMeasure.support = Ici (3 : ℝ) := by
  rw [thetaCuspResidueWeightedGraviAxionSpectralMeasure,
    support_withDensity_eq thetaCuspFirstHigherGraviAxionSpectralMeasure
      measurable_thetaCuspGraviAxionResidue
      (Filter.Eventually.of_forall thetaCuspGraviAxionResidue_ne_zero),
    thetaCuspFirstHigherGraviAxionSpectralMeasure_support]

theorem lowerSpectralEdge_thetaCuspResidueWeightedGraviAxionSpectralMeasure :
    lowerSpectralEdge thetaCuspResidueWeightedGraviAxionSpectralMeasure = 3 := by
  rw [lowerSpectralEdge, thetaCuspResidueWeightedGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le bddBelow_Ici Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

/-- Theta-cusp corpus supplies a positive-gap version of positive-residue support invariance. -/
theorem thetaCusp_positiveGap_residueInvariant_package :
    thetaCuspFirstHigherGraviAxionSpectralMeasure.support = Ici (3 : ℝ) ∧
      lowerSpectralEdge thetaCuspFirstHigherGraviAxionSpectralMeasure = 3 ∧
      thetaCuspResidueWeightedGraviAxionSpectralMeasure.support = Ici (3 : ℝ) ∧
      lowerSpectralEdge thetaCuspResidueWeightedGraviAxionSpectralMeasure = 3 := by
  exact ⟨thetaCuspFirstHigherGraviAxionSpectralMeasure_support,
    lowerSpectralEdge_thetaCuspFirstHigherGraviAxionSpectralMeasure,
    thetaCuspResidueWeightedGraviAxionSpectralMeasure_support,
    lowerSpectralEdge_thetaCuspResidueWeightedGraviAxionSpectralMeasure⟩

theorem thetaCuspHigherLikelihoodSpectralMeasure_ae_mem_Ici_three :
    ∀ᵐ massSq ∂thetaCuspHigherLikelihoodSpectralMeasure, massSq ∈ Ici (3 : ℝ) := by
  rw [thetaCuspHigherLikelihoodSpectralMeasure, Measure.ae_sum_iff]
  intro k
  have hgap : (3 : ℝ) ≤ thetaCuspLikelihoodGap (k + 2) := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
    simp only [thetaCuspLikelihoodGap, Nat.cast_add, Nat.cast_ofNat]
    nlinarith [sq_nonneg (k : ℝ)]
  rw [thetaCuspAtomLikelihoodSpectralMeasure, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    change ∀ᵐ massSq ∂Measure.dirac (thetaCuspLikelihoodGap (k + 2)), (3 : ℝ) ≤ massSq
    rw [ae_dirac_iff measurableSet_Ici]
    exact hgap
  · apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with massSq hmassSq
    exact hgap.trans hmassSq.le

theorem thetaCuspHigherLikelihoodSpectralMeasure_support :
    thetaCuspHigherLikelihoodSpectralMeasure.support = Ici (3 : ℝ) := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_Ici
    rw [mem_ae_iff]
    exact thetaCuspHigherLikelihoodSpectralMeasure_ae_mem_Ici_three
  · intro massSq hmassSq
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hVopen, hmassSqV⟩ := mem_nhds_iff.mp hU
    have hfirstSupport :
        massSq ∈ thetaCuspFirstHigherGraviAxionSpectralMeasure.support := by
      rw [thetaCuspFirstHigherGraviAxionSpectralMeasure_support]
      exact hmassSq
    have hfirstPos : 0 < thetaCuspFirstHigherGraviAxionSpectralMeasure V :=
      (Measure.mem_support_iff_forall massSq).mp hfirstSupport V
        (hVopen.mem_nhds hmassSqV)
    have hsumPos : 0 < thetaCuspHigherLikelihoodSpectralMeasure V := by
      rw [thetaCuspHigherLikelihoodSpectralMeasure,
        Measure.sum_apply _ hVopen.measurableSet]
      exact lt_of_lt_of_le hfirstPos (ENNReal.le_tsum 0)
    exact lt_of_lt_of_le hsumPos (measure_mono hVU)

theorem lowerSpectralEdge_thetaCuspHigherLikelihoodSpectralMeasure :
    lowerSpectralEdge thetaCuspHigherLikelihoodSpectralMeasure = 3 := by
  rw [lowerSpectralEdge, thetaCuspHigherLikelihoodSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le bddBelow_Ici Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

def thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure : Measure ℝ :=
  thetaCuspHigherLikelihoodSpectralMeasure.withDensity thetaCuspGraviAxionResidue

theorem thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure_support :
    thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure.support = Ici (3 : ℝ) := by
  rw [thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure,
    support_withDensity_eq thetaCuspHigherLikelihoodSpectralMeasure
      measurable_thetaCuspGraviAxionResidue
      (Filter.Eventually.of_forall thetaCuspGraviAxionResidue_ne_zero),
    thetaCuspHigherLikelihoodSpectralMeasure_support]

theorem lowerSpectralEdge_thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure :
    lowerSpectralEdge thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure = 3 := by
  rw [lowerSpectralEdge,
    thetaCuspHigherResidueWeightedGraviAxionSpectralMeasure_support]
  apply le_antisymm
  · exact csInf_le bddBelow_Ici Set.self_mem_Ici
  · exact le_csInf Set.nonempty_Ici fun _ hx => hx

end
end RHTower
