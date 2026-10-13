import GaloisForLFunctions.RHTower.PaperHurwitzObservationProfile

/-! # Exact moving-prefix detection thresholds

Every finite limiting ratio has exactly its corresponding profile value;
the full norm gap is recovered exactly when the ratio tends to infinity.
All sequences here are the actual native coordinate prefixes.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

/-- Complete finite-scale classification, including the zero-defect threshold at `c = 0`. -/
theorem paperHurwitzPrefixDefect_tendsto_iff (t : ℝ) (M : ℕ → ℕ) (c : ℝ≥0) :
    Tendsto (fun N => ‖paperHurwitzPrefixDefect t N (M N)‖) atTop
      (𝓝 (paperHurwitzObservationProfile c)) ↔
    Tendsto (fun N => (M N : ℝ) / ((N : ℝ) + 3)) atTop (𝓝 (c : ℝ)) := by
  simp only [norm_paperHurwitzPrefixDefect_profile]
  constructor
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      by_cases ha0 : a < 0
      · exact Eventually.of_forall fun N => ha0.trans_le (by positivity)
      have ha0' : 0 ≤ a := le_of_not_gt ha0
      have hp := paperHurwitzObservationProfile_strictMonoOn ha0' c.property ha
      filter_upwards [h.eventually (lt_mem_nhds hp)] with N hN
      by_contra hn
      have hm := paperHurwitzObservationProfile_strictMonoOn.monotoneOn
        (by positivity : 0 ≤ (M N : ℝ) / ((N : ℝ) + 3)) ha0' (le_of_not_gt hn)
      exact (not_lt_of_ge hm) hN
    · intro b hb
      have hb0 : 0 ≤ b := c.property.trans hb.le
      have hp := paperHurwitzObservationProfile_strictMonoOn c.property hb0 hb
      filter_upwards [h.eventually (gt_mem_nhds hp)] with N hN
      by_contra hn
      have hm := paperHurwitzObservationProfile_strictMonoOn.monotoneOn hb0
        (by positivity : 0 ≤ (M N : ℝ) / ((N : ℝ) + 3)) (le_of_not_gt hn)
      exact (not_lt_of_ge hm) hN
  · intro h
    exact (paperHurwitzObservationProfile_continuous.tendsto (c : ℝ)).comp h

/-- The complete unit gap appears exactly at prefixes faster than the inverse wall distance. -/
theorem paperHurwitzPrefixDefect_tendsto_one_iff (t : ℝ) (M : ℕ → ℕ) :
    Tendsto (fun N => ‖paperHurwitzPrefixDefect t N (M N)‖) atTop (𝓝 1) ↔
    Tendsto (fun N => (M N : ℝ) / ((N : ℝ) + 3)) atTop atTop := by
  simp only [norm_paperHurwitzPrefixDefect_profile]
  constructor
  · intro h
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [h.eventually (lt_mem_nhds (paperHurwitzObservationProfile_lt_one (max b 0)))]
      with N hN
    by_contra hb
    have hm := paperHurwitzObservationProfile_strictMonoOn.monotoneOn
      (by positivity : 0 ≤ (M N : ℝ) / ((N : ℝ) + 3)) (le_max_right b 0)
      ((le_of_lt (lt_of_not_ge hb)).trans (le_max_left b 0))
    exact (not_lt_of_ge hm) hN
  · intro h
    exact paperHurwitzObservationProfile_atTop.comp h

theorem norm_paperHurwitzPrefixDefect_linear (t : ℝ) (N m : ℕ) :
    ‖paperHurwitzPrefixDefect t N ((N + 3) * m)‖ = paperHurwitzObservationProfile m := by
  rw [norm_paperHurwitzPrefixDefect_profile]
  congr 1
  push_cast
  have h : (N : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/-- A linearly moving native prefix already retains the exact positive gap `9/25`. -/
theorem norm_paperHurwitzPrefixDefect_linear_one (t : ℝ) (N : ℕ) :
    ‖paperHurwitzPrefixDefect t N (N + 3)‖ = 9 / 25 := by
  have h := norm_paperHurwitzPrefixDefect_linear t N 1
  norm_num [paperHurwitzObservationProfile, Real.sinh_log (by norm_num : (0 : ℝ) < 2)] at h
  exact h

/-- Quadratically growing prefixes recover the full unit gap. -/
theorem paperHurwitzPrefixDefect_square_tendsto (t : ℝ) :
    Tendsto (fun N => ‖paperHurwitzPrefixDefect t N ((N + 3) ^ 2)‖) atTop (𝓝 1) := by
  apply (paperHurwitzPrefixDefect_tendsto_one_iff t (fun N => (N + 3) ^ 2)).mpr
  have h : Tendsto (fun N : ℕ => (N : ℝ) + 3) atTop atTop := by
    exact tendsto_atTop_mono (fun N => by linarith)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  convert h using 1
  funext N
  push_cast
  have hN : (N : ℝ) + 3 ≠ 0 := by positivity
  field_simp

/-- Even moving prefixes with a persistent norm gap vanish on every fixed full history. -/
theorem paperHurwitzPrefixDefect_strong_tendsto (t : ℝ) (M : ℕ → ℕ)
    (f : PaperHurwitzHistory) :
    Tendsto (fun N => paperHurwitzPrefixDefect t N (M N) f) atTop (𝓝 0) := by
  have h : Tendsto (fun N =>
      (paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1) f) atTop (𝓝 0) := by
    simpa only [sub_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply, sub_self] using
      (tendsto_paperHurwitzApproachPoint_strong t f).sub (tendsto_const_nhds (x := f))
  apply squeeze_zero_norm (fun N => ?_) (by simpa only [norm_zero] using h.norm)
  have heq : paperHurwitzPrefixDefect t N (M N) f = paperCoordinateProjection (M N + 1)
      ((paperHurwitzResolvent (paperHurwitzApproachPoint t N) - 1) f) := by
    ext k
    simp only [paperHurwitzPrefixDefect_apply, paperCoordinateProjection_coordinate,
      Nat.lt_succ_iff, sub_apply, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply,
      lp.coeFn_sub, Pi.sub_apply, paperHurwitzResolvent_apply]
    split_ifs <;> ring
  rw [heq]
  exact norm_paperCoordinateProjection_apply_le _ _

end
end RHTower
