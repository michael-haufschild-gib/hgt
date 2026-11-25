import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Cuts

/-! # Positive critical mass near every ordered prime spectrum in the closed band -/

noncomputable section
open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal
namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
/-- Strict increase of the critical one-prime distribution across every interior interval. -/
private theorem interval_pos {c a b d : ℝ} (hc : 0 < c) (hca : c ≤ a) (hab : a < b) (hbd : b ≤ d) :
    0 < (draw hc (hca.trans (hab.le.trans hbd)) 0 (Ioc a b) : ℝ) := by
  have hcd := (hca.trans_lt hab).trans_le hbd
  let μ := draw hc hcd.le 0
  have he : Ioc a b = Iic b \ Iic a := by ext t; simp [and_comm]
  have hμ := measureReal_sdiff (μ := (μ : Measure ℝ)) (Iic_subset_Iic.mpr hab.le) measurableSet_Iic
  rw [← he] at hμ
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn] at hμ
  change 0 < (μ (Ioc a b) : ℝ)
  rw [hμ]
  change 0 < (draw hc hcd.le 0 (Iic b) : ℝ)-(draw hc hcd.le 0 (Iic a) : ℝ)
  have hm {z : ℝ} (hz : 0 < z) : VacuumCalibration.mass c z 0 = Real.log (z/c) := by
    simp only [VacuumCalibration.mass,neg_zero,zero_mul,Real.exp_zero,integral_one_div_of_pos hc hz]
  rw [draw_cut hc (hca.trans hab.le) hbd hcd,draw_cut hc hca (hab.le.trans hbd) hcd,
    hm (hc.trans_le (hca.trans hab.le)),hm (hc.trans_le hca),hm (hc.trans hcd)]
  exact sub_pos.mpr (div_lt_div_of_pos_right (Real.log_lt_log (div_pos (hc.trans_le hca) hc)
    (div_lt_div_of_pos_right hab hc)) (Real.log_pos ((one_lt_div hc).mpr hcd)))

private theorem ball_pos {c d x r : ℝ} (hc : 0 < c) (hcd : c < d) (hx : x ∈ Icc c d) (hr : 0 < r) :
    0 < (draw hc hcd.le 0 (Metric.ball x r) : ℝ) := by
  let l := max c (x-r)
  let t := min d (x+r)
  have hlt : l < t := max_lt (lt_min hcd (hx.1.trans_lt (lt_add_of_pos_right x hr)))
    (lt_min ((sub_lt_self x hr).trans_le hx.2) ((sub_lt_self x hr).trans (lt_add_of_pos_right x hr)))
  obtain ⟨b,hlb,hbt⟩ := exists_between hlt
  have hi := interval_pos hc (le_max_left c (x-r)) hlb (hbt.le.trans (min_le_left _ _))
  have hs : Ioc l b ⊆ Metric.ball x r := by
    rw [Real.ball_eq_Ioo]
    exact fun y hy => ⟨(le_max_right c (x-r)).trans_lt hy.1,hy.2.trans_lt (hbt.trans_le (min_le_right _ _))⟩
  have H := measureReal_mono (μ := (draw hc hcd.le 0 : Measure ℝ)) hs
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn] at H
  exact hi.trans_le H

/-- Every neighborhood of an ordered tuple in the closed band has positive critical probability. -/
theorem open_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} {v : Fin k → ℝ}
    (hm : Monotone v) (hv : ∀ i, v i ∈ Icc c d) {G : Set (Fin k → ℝ)} (hG : IsOpen G) (hg : v ∈ G) :
    0 < (orderStatistics k (draw hc hcd.le 0) G : ℝ) := by
  let μ := draw hc hcd.le 0
  have hsort : sortedTuple v = v := by
    unfold sortedTuple
    rw [(Tuple.sort_eq_refl_iff_monotone (f := v)).mpr hm]
    rfl
  obtain ⟨r,hr,hB⟩ := Metric.isOpen_iff.mp (hG.preimage (continuous_sort k)) v (show sortedTuple v ∈ G by rwa [hsort])
  rw [orderStatistics,ProbabilityMeasure.map_apply _ _ hG.measurableSet]
  have H := measureReal_mono (μ := (iid k μ : Measure _)) hB
  simp only [ProbabilityMeasure.measureReal_eq_coe_coeFn] at H
  apply lt_of_lt_of_le _ H
  rw [ball_pi v hr]
  change 0 < (ProbabilityMeasure.pi (fun _ : Fin k => μ) _ : ℝ)
  rw [ProbabilityMeasure.pi_pi,NNReal.coe_prod]
  exact Finset.prod_pos fun i _ => ball_pos hc hcd (hv i) hr
/-- At unit inverse temperature every fixed neighborhood carries a uniformly positive conditional mass. -/
theorem eventually_open_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} {v : Fin k → ℝ}
    (hm : Monotone v) (hv : ∀ i, v i ∈ Icc c d) {G : Set (Fin k → ℝ)} (hG : IsOpen G) (hg : v ∈ G) :
    ∃ m > (0:ℝ), ∀ᶠ h in criticalApproach, m ≤ (conditional c d 0 h k G : ℝ) := by
  let μ := orderStatistics k (draw hc hcd.le 0)
  have hpos : 0 < μ G := by exact_mod_cast open_pos hc hcd hm hv hG hg
  obtain ⟨m,hm,hM⟩ := exists_between hpos
  have hμ : (m : ℝ≥0∞) < (μ : Measure _) G := by
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact ENNReal.coe_lt_coe.mpr hM
  have H := ProbabilityMeasure.le_liminf_measure_open_of_tendsto (conditional_limit hc hcd 0 k) hG
  refine ⟨m,by exact_mod_cast hm,?_⟩
  filter_upwards [eventually_lt_of_lt_liminf (hμ.trans_le H)] with h hh
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
  exact_mod_cast (ENNReal.coe_lt_coe.mp hh).le

#print axioms open_pos
#print axioms eventually_open_pos

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
