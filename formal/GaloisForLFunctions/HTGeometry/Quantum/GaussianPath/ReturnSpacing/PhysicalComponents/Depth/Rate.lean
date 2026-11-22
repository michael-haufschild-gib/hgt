import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.Depth.Counts
import Mathlib.Analysis.SpecificLimits.Basic

/-! # A unit displacement of the terminal date preserves the entry rate -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
noncomputable section

/-- A count bounded by the same arrival count at dates T and T+1 has
that arrival rate. Dividing by all visits gives the marking fraction. -/
theorem fraction_of_count_bounds (A B M : ℝ → ℕ) (a p q : ℝ) (hp : 0<p)
    (hA : Tendsto (fun T => (A T:ℝ)/(T-a)) atTop (𝓝 p))
    (hB : Tendsto (fun T => (B T:ℝ)/(T-a)) atTop (𝓝 q))
    (hb : ∀ T, B T≤M T ∧ M T≤B (T+1)) :
    Tendsto (fun T => (M T:ℝ)/(A T:ℝ)) atTop (𝓝 (q/p)) := by
  have ht : Tendsto (fun T : ℝ => T-a) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-a) tendsto_id
  have hc := (ht.const_div_atTop 1).const_add 1
  rw [add_zero] at hc
  have hs := (hB.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)).mul hc
  rw [mul_one] at hs
  have hh : Tendsto (fun T : ℝ => (B (T+1):ℝ)/(T-a)) atTop (𝓝 q) := by
    refine hs.congr' ?_
    filter_upwards [eventually_gt_atTop a] with T hT
    change (B (T+1):ℝ)/(T+1-a)*(1+1/(T-a))=_
    field_simp [(sub_pos.mpr hT).ne',(show 0<T+1-a by linarith only [hT]).ne']
    ring
  have hm : Tendsto (fun T => (M T:ℝ)/(T-a)) atTop (𝓝 q) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hB hh
    · filter_upwards [eventually_gt_atTop a] with T hT
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hb T).1) (sub_pos.mpr hT).le
    · filter_upwards [eventually_gt_atTop a] with T hT
      exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hb T).2) (sub_pos.mpr hT).le
  refine (hm.div hA hp.ne').congr' ?_
  filter_upwards [eventually_gt_atTop a] with T hT
  exact div_div_div_cancel_right₀ (sub_pos.mpr hT).ne' _ _

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.Depth
