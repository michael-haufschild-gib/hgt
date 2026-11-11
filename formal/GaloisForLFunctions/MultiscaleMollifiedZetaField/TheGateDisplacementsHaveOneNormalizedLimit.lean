import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShortMollifierKeepsItsLogarithmicScale
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFixedLinearMollifierChangesLittleAcrossTheGate

/-!
# One normalized displacement throughout the gate strip

The gate width bounds `(d−R/log U) log N` by `R/(U−1)`. Thus every
admissible moving abscissa has normalized displacement tending to
`R·13/50`, while its physical displacement tends to zero.
-/

open Filter Metric Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- Every selection from the gate strip has the same normalized displacement limit. -/
theorem tendsto_gate_normalized_displacement {ι : Type*} {l : Filter ι}
    {U d : ι → ℝ} (hU : Tendsto U l atTop) {R : ℝ} (hR : 0 ≤ R)
    (hgate : ∀ᶠ i in l, R ≤ d i * Real.log (U i) ∧ d i * Real.log (U i - 1) ≤ R) :
    Tendsto (fun i => d i * Real.log (shortLevinsonCutoff (U i))) l (𝓝 (R * (13 / 50 : ℝ))) := by
  have hn := tendsto_shortLevinsonCutoff.comp hU
  have hUm : Tendsto (fun i => U i - 1) l atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    filter_upwards [hU.eventually_ge_atTop (A + 1)] with i hi
    linarith only [hi]
  have hwidth : ∀ᶠ i in l,
      0 ≤ d i * Real.log (shortLevinsonCutoff (U i)) -
        R * (Real.log (shortLevinsonCutoff (U i)) / Real.log (U i)) ∧
      d i * Real.log (shortLevinsonCutoff (U i)) -
        R * (Real.log (shortLevinsonCutoff (U i)) / Real.log (U i)) ≤ R / (U i - 1) := by
    filter_upwards [hgate, hn.eventually_ge_atTop 2, hU.eventually_gt_atTop 2,
      (Real.tendsto_log_atTop.comp hUm).eventually_ge_atTop 1,
      hU.eventually eventually_shortLevinsonCutoff_add_one_le] with i hgi hni hUi hlog hcut
    have hN : 1 < shortLevinsonCutoff (U i) := by omega
    have hNU : (shortLevinsonCutoff (U i) : ℝ) ≤ U i := by
      push_cast at hcut
      linarith only [hcut]
    have hw := levinsonGate_coefficient_shift_width hUi hlog hR hN hNU hgi.1 hgi.2
    have hL : 0 < Real.log (shortLevinsonCutoff (U i) : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have he : d i * Real.log (shortLevinsonCutoff (U i)) -
        R * (Real.log (shortLevinsonCutoff (U i)) / Real.log (U i)) =
        (d i - R / Real.log (U i)) * Real.log (shortLevinsonCutoff (U i)) := by ring
    rw [he]
    exact ⟨mul_nonneg (sub_nonneg.mpr hw.1) hL.le, hw.2⟩
  have hsmall : Tendsto (fun i => R / (U i - 1)) l (𝓝 0) := tendsto_const_nhds.div_atTop hUm
  have herr : Tendsto (fun i => d i * Real.log (shortLevinsonCutoff (U i)) -
      R * (Real.log (shortLevinsonCutoff (U i)) / Real.log (U i))) l (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hwidth, hsmall.eventually (Iio_mem_nhds hε)] with i hi hsi
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hi.1]
    exact hi.2.trans_lt hsi
  have hbase := (tendsto_log_shortLevinsonCutoff_div_log.comp hU).const_mul R
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using herr.add hbase

/-- The physical gate displacement tends to zero uniformly along arbitrary admissible selections. -/
theorem tendsto_gate_displacement_zero {ι : Type*} {l : Filter ι}
    {U d : ι → ℝ} (hU : Tendsto U l atTop) {R : ℝ} (hR : 0 ≤ R)
    (hgate : ∀ᶠ i in l, R ≤ d i * Real.log (U i) ∧ d i * Real.log (U i - 1) ≤ R) :
    Tendsto d l (𝓝 0) := by
  have hn := tendsto_shortLevinsonCutoff.comp hU
  have hL : Tendsto (fun i => Real.log (shortLevinsonCutoff (U i) : ℝ)) l atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hn)
  apply ((tendsto_gate_normalized_displacement hU hR hgate).div_atTop hL).congr'
  filter_upwards [hn.eventually_ge_atTop 2] with i hi
  have hne : Real.log (shortLevinsonCutoff (U i) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < shortLevinsonCutoff (U i)))).ne'
  exact mul_div_cancel_right₀ (d i) hne

/-- The entire admissible gate strip eventually lies in every positive displacement neighbourhood. -/
theorem eventually_gate_displacements_small {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    ∀ᶠ U : ℝ in atTop, ∀ d : ℝ,
      R ≤ d * Real.log U → d * Real.log (U - 1) ≤ R → 0 < d ∧ d ≤ r := by
  have hUm : Tendsto (fun U : ℝ => U - 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro A
    filter_upwards [eventually_ge_atTop (A + 1)] with U hi
    linarith only [hi]
  have hL := Real.tendsto_log_atTop.comp hUm
  have hs : Tendsto (fun U : ℝ => R / Real.log (U - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hL
  filter_upwards [eventually_gt_atTop (2 : ℝ), hL.eventually_gt_atTop 0,
    hs.eventually (Iio_mem_nhds hr)] with U hU hLU hsU
  intro d hlo hhi
  have hlog : 0 < Real.log U := Real.log_pos (by linarith only [hU])
  exact ⟨(div_pos hR hlog).trans_le ((div_le_iff₀ hlog).mpr hlo),
    ((le_div_iff₀ hLU).mpr hhi).trans hsU.le⟩

end GaloisForLFunctions.MultiscaleMollifiedZetaField
