import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryResidual

/-! # First-order trajectory selection at the critical third-slope boundary. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

def shiftedBoundaryRatio (a x : ℝ) : ℝ := boundaryRatio x-1/12-a*(k x)⁻¹

theorem dShiftedBoundaryRatio (a : ℝ) {x : ℝ} (hx : 0<x) :
    HasDerivAt (shiftedBoundaryRatio a)
      ((k x/u x)*(36*shiftedBoundaryRatio a x+(k x)⁻¹*boundaryResidual a x)) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  convert ((dBoundaryRatio hx).sub_const (1/12:ℝ)).sub ((dInverseK hx.le).const_mul a)
    using 1 <;> first | rfl | skip
  simp only [shiftedBoundaryRatio,boundaryResidual]
  field_simp [hk,hu]
  ring

theorem boundaryGain_lower {x : ℝ} (hx : 0<x) : 1/3≤k x/u x := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  apply (le_div_iff₀ hu).mpr
  have hu3 := thetaCuspModularMassDrift_lt_three hx.le
  have hk := k_gt_fiveFourths hx.le
  linarith

theorem shiftedBoundaryRatio_bounded (a : ℝ) {x : ℝ} (hx : 1≤x) :
    -(3/(2*u 1^2)+|a|+1) ≤ shiftedBoundaryRatio a x ∧
    shiftedBoundaryRatio a x ≤ 3/(2*u 1^2)+|a|+1 := by
  have hk : 1<k x := by linarith [k_gt_fiveFourths (show 0≤x by linarith)]
  have hh0 : 0≤(k x)⁻¹ := inv_nonneg.mpr (by linarith)
  have hh1 : (k x)⁻¹≤1 := (inv_lt_one_of_one_lt₀ hk).le
  have hq0 := boundaryRatio_nonneg (show 0<x by linarith)
  have hqB := boundaryRatio_bound hx
  have hB : 0≤3/(2*u 1^2) := by positivity
  have hl := mul_le_mul_of_nonneg_right (neg_abs_le a) hh0
  have hu := mul_le_mul_of_nonneg_right (le_abs_self a) hh0
  have hb := mul_le_mul_of_nonneg_left hh1 (abs_nonneg a)
  unfold shiftedBoundaryRatio
  constructor <;> nlinarith only [hl,hu,hb,hq0,hqB,hB]

/-- An upper moving barrier follows from the sign of its complete-source residual. -/
theorem boundaryRatio_eventually_le_barrier (a : ℝ) (ha : -7/72<a) :
    ∀ᶠ x in atTop, boundaryRatio x≤1/12+a*(k x)⁻¹ := by
  have hr : 0<36*a+7/2 := by linarith only [ha]
  have hR := (boundaryResidual_tendsto a).eventually_const_lt hr
  obtain ⟨N,hN⟩ := eventually_atTop.1 hR
  refine eventually_atTop.2 ⟨max 1 N,?_⟩
  intro b hb
  have hb1 : 1≤b := (le_max_left 1 N).trans hb
  have hbN : N≤b := (le_max_right 1 N).trans hb
  by_contra hn
  have hf : 0<shiftedBoundaryRatio a b := by
    unfold shiftedBoundaryRatio
    linarith only [lt_of_not_ge hn]
  apply HTGeometry.BoundedUnstableSelection.no_bounded_escape
    (shiftedBoundaryRatio a)
    (fun x => (k x/u x)*(36*shiftedBoundaryRatio a x+(k x)⁻¹*boundaryResidual a x))
    b (3/(2*u 1^2)+|a|+1) (12*shiftedBoundaryRatio a b) (by positivity)
    (fun x hx => dShiftedBoundaryRatio a (by linarith))
    (fun x hx => (shiftedBoundaryRatio_bounded a (hb1.trans hx)).2)
  intro x hbx hfx
  have hx : 0<x := by linarith
  have hgain := boundaryGain_lower hx
  have hg0 : 0≤k x/u x := by linarith only [hgain]
  have hh : 0≤(k x)⁻¹ := inv_nonneg.mpr (by linarith [k_gt hx.le])
  have hres := (hN x (hbN.trans hbx)).le
  have hlin : 36*shiftedBoundaryRatio a b≤
      36*shiftedBoundaryRatio a x+(k x)⁻¹*boundaryResidual a x := by
    nlinarith only [hfx,mul_nonneg hh hres]
  have hp := mul_le_mul_of_nonneg_left hlin hg0
  have hgg := mul_le_mul_of_nonneg_right hgain (show 0≤36*shiftedBoundaryRatio a b by positivity)
  nlinarith only [hp,hgg]

/-- The lower moving barrier uses the same complete-ray escape in the opposite direction. -/
theorem boundaryRatio_eventually_ge_barrier (a : ℝ) (ha : a< -7/72) :
    ∀ᶠ x in atTop, 1/12+a*(k x)⁻¹≤boundaryRatio x := by
  have hr : 36*a+7/2<0 := by linarith only [ha]
  have hR := (boundaryResidual_tendsto a).eventually_lt_const hr
  obtain ⟨N,hN⟩ := eventually_atTop.1 hR
  refine eventually_atTop.2 ⟨max 1 N,?_⟩
  intro b hb
  have hb1 : 1≤b := (le_max_left 1 N).trans hb
  have hbN : N≤b := (le_max_right 1 N).trans hb
  by_contra hn
  have hf : shiftedBoundaryRatio a b<0 := by
    unfold shiftedBoundaryRatio
    linarith only [lt_of_not_ge hn]
  apply HTGeometry.BoundedUnstableSelection.no_bounded_escape
    (fun x => -shiftedBoundaryRatio a x)
    (fun x => -((k x/u x)*(36*shiftedBoundaryRatio a x+(k x)⁻¹*boundaryResidual a x)))
    b (3/(2*u 1^2)+|a|+1) (-12*shiftedBoundaryRatio a b) (by nlinarith only [hf])
    (fun x hx => (dShiftedBoundaryRatio a (show 0<x by linarith)).neg)
    (fun x hx => by linarith only [(shiftedBoundaryRatio_bounded a (hb1.trans hx)).1])
  intro x hbx hfx
  have hx : 0<x := by linarith
  have hgain := boundaryGain_lower hx
  have hg0 : 0≤k x/u x := by linarith only [hgain]
  have hh : 0≤(k x)⁻¹ := inv_nonneg.mpr (by linarith [k_gt hx.le])
  have hres := (hN x (hbN.trans hbx)).le
  have hlin : 36*shiftedBoundaryRatio a x+(k x)⁻¹*boundaryResidual a x≤
      36*shiftedBoundaryRatio a b := by
    nlinarith only [hfx,mul_nonpos_of_nonneg_of_nonpos hh hres]
  have hp := mul_le_mul_of_nonneg_left hlin hg0
  have hgg := mul_le_mul_of_nonpos_right hgain (show 36*shiftedBoundaryRatio a b≤0 by linarith)
  nlinarith only [hp,hgg]

/-- The first transverse coefficient is forced by the complete modular orbit. -/
theorem boundaryRatio_firstOrder_tendsto :
    Tendsto (fun x => k x*(boundaryRatio x-1/12)) atTop (𝓝 (-7/72:ℝ)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    let a : ℝ := (b+(-7/72))/2
    have ha : a< -7/72 := by dsimp [a]; linarith only [hb]
    have hab : b<a := by dsimp [a]; linarith only [hb]
    filter_upwards [boundaryRatio_eventually_ge_barrier a ha,eventually_ge_atTop (0:ℝ)] with x hx hx0
    have hk : 0<k x := lt_trans (by norm_num) (k_gt hx0)
    have he := mul_le_mul_of_nonneg_left hx hk.le
    have hi : k x*(1/12+a*(k x)⁻¹)=k x/12+a := by field_simp [hk.ne']
    rw [hi] at he
    nlinarith only [he,hab]
  · intro b hb
    let a : ℝ := (b+(-7/72))/2
    have ha : -7/72<a := by dsimp [a]; linarith only [hb]
    have hab : a<b := by dsimp [a]; linarith only [hb]
    filter_upwards [boundaryRatio_eventually_le_barrier a ha,eventually_ge_atTop (0:ℝ)] with x hx hx0
    have hk : 0<k x := lt_trans (by norm_num) (k_gt hx0)
    have he := mul_le_mul_of_nonneg_left hx hk.le
    have hi : k x*(1/12+a*(k x)⁻¹)=k x/12+a := by field_simp [hk.ne']
    rw [hi] at he
    nlinarith only [he,hab]

end
end RHTower.ThetaCuspModularRatio
