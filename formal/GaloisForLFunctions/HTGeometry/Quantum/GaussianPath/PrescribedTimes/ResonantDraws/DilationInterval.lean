import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TrajectoryProfiles.ReplayDensity

/-! # Physical occupation on a fixed interval of dilation factors -/
open Set Filter MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
noncomputable section

/-- Uniform dilation samples the corresponding physical time interval
with the reciprocal-time Jacobian. -/
theorem dilation_interval_volume (A : Set ℝ) (a b : ℝ) {t : ℝ} (ht : 0<t) :
    (volume.restrict (Icc a b)).real ((fun z : ℝ => z*t) ⁻¹' A) =
      t⁻¹*volume.real (A ∩ Icc (a*t) (b*t)) := by
  have he : ((fun z : ℝ => z*t) ⁻¹' A) ∩ Icc a b =
      (fun z : ℝ => t*z) ⁻¹' (A ∩ Icc (a*t) (b*t)) := by
    ext z
    change (z*t∈A ∧ a≤z ∧ z≤b) ↔ t*z∈A ∧ a*t≤t*z ∧ t*z≤b*t
    rw [mul_comm t z]
    exact and_congr_right' (and_congr (mul_le_mul_iff_left₀ ht).symm (mul_le_mul_iff_left₀ ht).symm)
  rw [measureReal_restrict_apply' measurableSet_Icc,he,Measure.real,Real.volume_preimage_mul_left ht.ne',
    ENNReal.toReal_mul,abs_of_pos (inv_pos.mpr ht),ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)]
  rfl

/-- A limiting positive-time density fixes the mass seen by dilation
factors from one to b. Subtracting the two prefix masses removes all
dependence on the early part of the orbit. -/
theorem dilation_interval_limit {A : Set ℝ} (hA : MeasurableSet A) (p : ℝ)
    (h : Tendsto (fun t : ℝ => volume.real (A ∩ Icc 0 t)/t) atTop (𝓝 p)) {b : ℝ} (hb : 1<b) :
    Tendsto (fun t : ℝ => (volume.restrict (Icc 1 b)).real ((fun a : ℝ => a*t) ⁻¹' A))
      atTop (𝓝 ((b-1)*p)) := by
  let M (t : ℝ) := volume.real (A ∩ Icc 0 t)
  have hb₀ : 0<b := zero_lt_one.trans hb
  have hh := ((h.comp (tendsto_id.const_mul_atTop hb₀)).const_mul b).sub h
  rw [show b*p-p=(b-1)*p by ring] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have hbt := le_mul_of_one_le_left ht.le hb.le
  have hjoin : (A ∩ Icc 0 t) ∪ (A ∩ Ioc t (b*t)) = A ∩ Icc 0 (b*t) := by
    ext a
    change ((a∈A ∧ 0≤a ∧ a≤t) ∨ (a∈A ∧ t<a ∧ a≤b*t)) ↔ a∈A ∧ 0≤a ∧ a≤b*t
    constructor
    · rintro (⟨ha,h₀,hl⟩ | ⟨ha,hl,hu⟩)
      exacts [⟨ha,h₀,hl.trans hbt⟩,⟨ha,ht.le.trans hl.le,hu⟩]
    · rintro ⟨ha,h₀,hu⟩
      exact (le_or_gt a t).elim (fun hl => Or.inl ⟨ha,h₀,hl⟩) (fun hl => Or.inr ⟨ha,hl,hu⟩)
  have hdis : Disjoint (A ∩ Icc 0 t) (A ∩ Ioc t (b*t)) :=
    disjoint_left.mpr fun _ hl hr => hr.2.1.not_ge hl.2.2
  have hsum := measureReal_union (μ:=volume) hdis (hA.inter measurableSet_Ioc)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
    (measure_ne_top_of_subset inter_subset_right measure_Ioc_lt_top.ne)
  have hic : volume.real (A ∩ Ioc t (b*t))=volume.real (A ∩ Icc t (b*t)) :=
    measureReal_congr (ae_eq_set_inter EventuallyEq.rfl Ioc_ae_eq_Icc)
  rw [hjoin,hic] at hsum
  change M (b*t)=M t+volume.real (A ∩ Icc t (b*t)) at hsum
  change b*(M (b*t)/(b*t))-M t/t=_
  rw [dilation_interval_volume A 1 b ht,one_mul,hsum]
  field_simp
  <;> ring

#print axioms dilation_interval_limit
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws
