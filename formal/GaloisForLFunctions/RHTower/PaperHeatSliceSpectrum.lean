import GaloisForLFunctions.RHTower.PaperHeatSliceCutoff
import GaloisForLFunctions.HTGeometry.ContinuousLpMultiplierSpectrum
import Mathlib.Topology.Order.IntermediateValue

/-!
# The complete spectrum of the positive-time LA defect

The all-order negative Taylor mass has compact support and is nonnegative and continuous.
Its exact continuum spectrum is the full real interval from zero to its operator norm.
-/

namespace RHTower.PaperHeatSlice
noncomputable section
open MeasureTheory Set
open RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open scoped Topology NNReal ENNReal

theorem exists_mass_zero (lam : Radius) (r : Radius) :
    ∃ t : ℝ, mass ⟨lam, lam.property.le⟩ r t = 0 := by
  obtain ⟨T, hT⟩ := exists_mass_support lam
  refine ⟨|T| + 1, hT r _ ?_⟩
  rw [abs_of_nonneg (by positivity : 0 ≤ |T| + 1)]
  linarith [le_abs_self T]

/-- At positive time the exact continuum operator norm is attained by the source symbol. -/
theorem exists_mass_eq_operator_norm (lam : Radius) (r : Radius) :
    ∃ t : ℝ, mass ⟨lam, lam.property.le⟩ r t = ‖massOperator ⟨lam, lam.property.le⟩ r‖ := by
  obtain ⟨t, ht⟩ := (continuous_mass ⟨lam, lam.property.le⟩ r).exists_forall_ge_of_hasCompactSupport
    (hasCompactSupport_mass lam r)
  refine ⟨t, le_antisymm (mass_le_operator_norm _ r t) ?_⟩
  apply MeasureTheory.norm_le_of_ae_mul (ψ := fun u => (mass ⟨lam, lam.property.le⟩ r u : ℂ))
    (mass_nonneg _ r t) _ (massOperator_apply_ae _ r)
  intro u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mass_nonneg _ r u)]
  exact ht u

theorem range_mass (lam : Radius) (r : Radius) :
    range (mass ⟨lam, lam.property.le⟩ r) = Icc 0 ‖massOperator ⟨lam, lam.property.le⟩ r‖ := by
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact ⟨mass_nonneg _ r t, mass_le_operator_norm _ r t⟩
  · obtain ⟨a, ha⟩ := exists_mass_zero lam r
    obtain ⟨b, hb⟩ := exists_mass_eq_operator_norm lam r
    simpa only [ha, hb] using intermediate_value_univ a b (continuous_mass ⟨lam, lam.property.le⟩ r)

/-- Every value between zero and the full defect norm survives in the spectrum. -/
theorem massOperator_spectrum (lam : Radius) (r : Radius) :
    spectrum ℂ (massOperator ⟨lam, lam.property.le⟩ r) =
      Complex.ofReal '' Icc 0 ‖massOperator ⟨lam, lam.property.le⟩ r‖ := by
  refine (spectrum_eq_closure_range_of_ae_mul_continuous
    (Complex.continuous_ofReal.comp (continuous_mass _ r)) (massOperator_apply_ae _ r)).trans ?_
  rw [range_comp, range_mass, (isCompact_Icc.image Complex.continuous_ofReal).isClosed.closure_eq]

theorem massOperator_spectrum_eq_zero_iff_threshold (lam : Radius) (r : Radius) :
    spectrum ℂ (massOperator ⟨lam, lam.property.le⟩ r) = {0} ↔ newmanConstant ≤ (lam : ℝ) := by
  constructor
  · intro h
    have hm : (‖massOperator ⟨lam, lam.property.le⟩ r‖ : ℂ) ∈
        spectrum ℂ (massOperator ⟨lam, lam.property.le⟩ r) := by
      rw [massOperator_spectrum]
      exact ⟨_, ⟨norm_nonneg _, le_rfl⟩, rfl⟩
    rw [h, mem_singleton_iff] at hm
    have hn : ‖massOperator ⟨lam, lam.property.le⟩ r‖ = 0 := by exact_mod_cast hm
    exact (massOperator_eq_zero_iff_threshold _ r).mp (norm_eq_zero.mp hn)
  · intro h
    have hz := (massOperator_eq_zero_iff_threshold ⟨lam, lam.property.le⟩ r).mpr h
    rw [massOperator_spectrum, hz, norm_zero]
    simp

end
end RHTower.PaperHeatSlice
