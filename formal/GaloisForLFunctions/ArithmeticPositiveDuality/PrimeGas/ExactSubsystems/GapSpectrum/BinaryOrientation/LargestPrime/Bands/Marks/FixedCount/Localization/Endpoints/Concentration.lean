import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry

/-! # Conditional prime bands at diverging positive and negative thermal drift -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Set Filter Topology MeasureTheory _root_.RHTower

/-- A gap between numerator and denominator exponents suppresses a physical conditional event. -/
private theorem vanish {c d b e x y : ℝ} (hc : 0 < c) (hcd : c < d) (hb : 0 < b) (hbe : b < e)
    (hxy : x < y) {u : Ioi (0:ℝ) → ℝ} (hu : Tendsto u criticalApproach atTop)
    (s : Ioi (0:ℝ) → ℝ) (k : ℕ) {F : Set (Fin k → ℝ)} (hF : MeasurableSet F)
    (hU : ∀ᶠ h in criticalApproach, eventWeight (added c d h) (s h) h k F ≤
      Real.exp (u h*x)*coefficient (added c d h) 1 k)
    (hL : ∀ᶠ h in criticalApproach, Real.exp (u h*y)*coefficient (added b e h) 1 k ≤
      coefficient (added c d h) (s h) k) :
    Tendsto (fun h => (thermalLaw c d h (s h) k F : ℝ)) criticalApproach (𝓝 0) := by
  have hB := coefficient_limit hb hbe k
  have hpos := critical_limit_pos hb hbe k
  have hexp := Real.tendsto_exp_atBot.comp (hu.atTop_mul_const_of_neg (sub_neg.mpr hxy))
  have H := hexp.mul ((coefficient_limit hc hcd k).div hB hpos.ne')
  rw [zero_mul] at H
  apply squeeze_zero' (Eventually.of_forall fun h => (thermalLaw c d h (s h) k F).property) _ H
  filter_upwards [hU,hL,hB.eventually_const_lt hpos] with h hU' hL' hB'
  have hl := mul_pos (Real.exp_pos (u h*y)) hB'
  have hd := hl.trans_le hL'
  have ha := mul_nonneg (Real.exp_pos (u h*x)).le (show 0 ≤ coefficient (added c d h) 1 k by
    rw [coefficient,← slice_mass (added c d h) 1 h k]
    exact mul_nonneg (finiteSquarefreePartition_pos _ _).le (slice _ _ _ _).mass.property)
  calc (thermalLaw c d h (s h) k F : ℝ) = eventWeight (added c d h) (s h) h k F /
         coefficient (added c d h) (s h) k := thermalLaw_event h k hF hd
       _ ≤ (Real.exp (u h*x)*coefficient (added c d h) 1 k)/coefficient (added c d h) (s h) k :=
         div_le_div_of_nonneg_right hU' hd.le
       _ ≤ (Real.exp (u h*x)*coefficient (added c d h) 1 k)/(Real.exp (u h*y)*coefficient (added b e h) 1 k) :=
         div_le_div_of_nonneg_left ha hl hL'
       _ = Real.exp (u h*(x-y))*(coefficient (added c d h) 1 k/coefficient (added b e h) 1 k) := by
         rw [mul_sub,Real.exp_sub,div_mul_div_comm]

private theorem missed_ball {k : ℕ} {F : Set (Fin k → ℝ)} (hF : IsClosed F) {z : Fin k → ℝ} (hz : z ∉ F) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ F, ε ≤ dist v z := by
  obtain ⟨ε,hε,hB⟩ := Metric.isOpen_iff.mp hF.isOpen_compl z hz
  exact ⟨ε,hε,fun v hv => le_of_not_gt fun h => (hB (Metric.mem_ball.mpr h)) hv⟩

/-- With positive diverging drift, closed sets missing the lower endpoint vector have vanishing probability. -/
theorem lower_tail {c d : ℝ} (hc : 0 < c) (hcd : c < d) {u : Ioi (0:ℝ) → ℝ}
    (hu : Tendsto u criticalApproach atTop) {k : ℕ} (hk : 0 < k) {F : Set (Fin k → ℝ)}
    (hF : IsClosed F) (hz : (fun _ : Fin k => c) ∉ F) :
    Tendsto (fun h => (thermalLaw c d h (1+u h*h.val) k F : ℝ)) criticalApproach (𝓝 0) := by
  obtain ⟨ε,hε,hfar⟩ := missed_ball hF hz
  obtain ⟨w,hw,hwd,hwe⟩ := inner_width hcd hε hk
  let b := c+w
  have hcb : c < b := lt_add_of_pos_right _ hw
  have hbd : b ≤ d := by dsimp [b]; linarith only [hwd]
  apply vanish hc hcd hc hcb (x := -(k*c+ε)) (y := -(k*b))
    (by dsimp [b]; nlinarith only [hwe]) hu _ k hF.measurableSet
  · filter_upwards [hu.eventually_ge_atTop 0] with h hs
    apply eventWeight_le
    intro R hr
    have H := (hfar _ hr).trans (lower_distance h R)
    have he : k*c+ε ≤ h.val*energyOf R := by linarith only [H]
    calc _ = -(u h)*(h.val*energyOf R) := by ring
         _ ≤ -(u h)*(k*c+ε) := mul_le_mul_of_nonpos_left he (neg_nonpos.mpr hs)
         _ = _ := by ring
  · filter_upwards [hu.eventually_ge_atTop 0] with h hs
    have ht := (cooling_bounds c b h hs k).1
    exact ht.trans (coefficient_mono (subband le_rfl hbd h) _ h k)

/-- With negative diverging drift, every closed set missing the upper endpoint vector loses its mass. -/
theorem upper_tail {c d : ℝ} (hc : 0 < c) (hcd : c < d) {u : Ioi (0:ℝ) → ℝ}
    (hu : Tendsto u criticalApproach atTop) {k : ℕ} (hk : 0 < k) {F : Set (Fin k → ℝ)}
    (hF : IsClosed F) (hz : (fun _ : Fin k => d) ∉ F) :
    Tendsto (fun h => (thermalLaw c d h (1-u h*h.val) k F : ℝ)) criticalApproach (𝓝 0) := by
  obtain ⟨ε,hε,hfar⟩ := missed_ball hF hz
  obtain ⟨w,hw,hwd,hwe⟩ := inner_width hcd hε hk
  let b := d-w
  have hcb : c ≤ b := by dsimp [b]; linarith only [hwd]
  have hbd : b < d := sub_lt_self _ hw
  apply vanish hc hcd (hc.trans_le hcb) hbd (x := k*d-ε) (y := k*b)
    (by dsimp [b]; nlinarith only [hwe]) hu _ k hF.measurableSet
  · filter_upwards [hu.eventually_ge_atTop 0] with h hs
    apply eventWeight_le
    intro R hr
    have H := (hfar _ hr).trans (upper_distance h R)
    have he : h.val*energyOf R ≤ k*d-ε := by linarith only [H]
    calc _ = u h*(h.val*energyOf R) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left he hs
  · filter_upwards [hu.eventually_ge_atTop 0] with h hs
    have ht := (heating_bounds b d h hs k).1
    exact ht.trans (coefficient_mono (subband hcb le_rfl h) _ h k)

#print axioms lower_tail
#print axioms upper_tail

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
