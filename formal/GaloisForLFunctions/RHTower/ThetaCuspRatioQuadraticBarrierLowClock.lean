import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierTail

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

theorem inverse_clock_le_of_ge {a x : ℝ} (ha : 0<a) (hax : a≤x)
    (hh : (k a)⁻¹≤2/3) : (k x)⁻¹≤2/3 := by
  have hka : 0<k a := lt_trans (by norm_num) (k_gt ha.le)
  have hx : 0<x := ha.trans_le hax
  have hkx : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have hm := k_mono ha.le hx.le hax
  rw [inv_eq_one_div,div_le_iff₀ hka] at hh
  rw [inv_eq_one_div,div_le_iff₀ hkx]
  linarith

/-- The nonlinear source barrier holds throughout the entire lower-clock ray. -/
theorem quadraticSourceError_pos_of_low_clock {a : ℝ} (ha : 0<a) (hh : (k a)⁻¹≤2/3) :
    0<quadraticSourceError a := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 quadraticSourceError_eventually_pos
  let c : ℝ := max a N
  have hac : a≤c := le_max_left a N
  have hNc : N≤c := le_max_right a N
  have hc := hN c hNc
  by_contra hn
  have hna : quadraticSourceError a≤0 := le_of_not_gt hn
  have hnc : quadraticSourceError c≤0 := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := quadraticSourceError) (f' := quadraticSourceSpeed) (a := a) (b := c)
      (fun x hx => (dQuadraticSourceError (ha.trans_le hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => (dQuadraticSourceError (ha.trans_le hx.1)).hasDerivWithinAt)
      (B := fun _ => 0) (B' := fun _ => 0) hna
      (fun x => hasDerivAt_const x (0:ℝ)) ?_ ⟨hac,le_rfl⟩
    intro x hx he
    exact quadraticSourceSpeed_neg_at_low_zero (ha.trans_le hx.1)
      (inverse_clock_le_of_ge ha hx.1 hh) he
  linarith only [hc,hnc]

theorem boundaryRatio_gt_quadratic_barrier_of_low_clock {x : ℝ} (hx : 0<x)
    (hh : (k x)⁻¹≤2/3) :
    1/12-7/(72*k x)<boundaryRatio x-t x*(boundaryRatio x)^2 := by
  have he := quadraticSourceError_pos_of_low_clock hx hh
  unfold quadraticSourceError at he
  rw [criticalError_eq] at he
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hb : HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹)=1/12-7/(72*k x) := by
    unfold HTGeometry.ThetaCriticalBarrier.b
    field_simp [hk]
  rw [hb] at he
  linarith only [he]

end
end RHTower.ThetaCuspModularRatio
