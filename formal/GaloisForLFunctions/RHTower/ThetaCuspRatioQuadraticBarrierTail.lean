import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierNormalized

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

theorem quadraticSourceForce_eventually_neg : ∀ᶠ x in atTop, quadraticSourceForce x<0 := by
  have hs := quadraticSourceForce_scaled_tendsto.eventually_lt_const (show (-7/16:ℝ)<0 by norm_num)
  filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with x hx hx0
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx0.le)
  by_contra hn
  have hm := mul_nonneg hk.le (le_of_not_gt hn)
  linarith only [hx,hm]

theorem quadraticNormalizedSpeed_tail : ∀ᶠ x in atTop,
    quadraticNormalizedError x≤0 → quadraticNormalizedSpeed x<10*quadraticNormalizedError x := by
  have hr := quadraticNormalizedRate_tendsto.eventually_const_lt (show (30:ℝ)<54 by norm_num)
  filter_upwards [hr,quadraticSourceForce_eventually_neg,eventually_gt_atTop (0:ℝ)]
    with x hrate hforce hx he
  have hg := boundaryGain_lower hx
  have hg0 : 0<k x/u x := lt_of_lt_of_le (by norm_num) hg
  have hl := mul_le_mul_of_nonpos_right hrate.le he
  have hb : quadraticNormalizedRate x*quadraticNormalizedError x+quadraticSourceForce x<
      30*quadraticNormalizedError x := by linarith only [hl,hforce]
  have hm := mul_lt_mul_of_pos_left hb hg0
  have hn := mul_le_mul_of_nonpos_right hg (show 30*quadraticNormalizedError x≤0 by linarith)
  unfold quadraticNormalizedSpeed
  nlinarith only [hm,hn]

theorem quadraticNormalizedError_eventually_nonneg :
    ∀ᶠ x in atTop, 0≤quadraticNormalizedError x := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 quadraticNormalizedSpeed_tail
  refine eventually_atTop.2 ⟨max 1 N,?_⟩
  intro b hb
  have hb1 := (le_max_left 1 N).trans hb
  have hbN := (le_max_right 1 N).trans hb
  by_contra hn
  have hf : quadraticNormalizedError b<0 := lt_of_not_ge hn
  apply HTGeometry.BoundedUnstableSelection.no_bounded_escape
    (fun x => -quadraticNormalizedError x) (fun x => -quadraticNormalizedSpeed x)
    b ((3/(2*u 1^2))^2) (-10*quadraticNormalizedError b) (by nlinarith only [hf])
    (fun x hx => (dQuadraticNormalizedError (show 0<x by linarith)).neg)
    (fun x hx => by linarith only [quadraticNormalizedError_lower (hb1.trans hx)])
  intro x hbx hfx
  have hle : quadraticNormalizedError x≤quadraticNormalizedError b := by linarith only [hfx]
  have hs := hN x (hbN.trans hbx) (hle.trans hf.le)
  linarith only [hs,hle]

theorem quadraticNormalizedError_eventually_pos : ∀ᶠ x in atTop, 0<quadraticNormalizedError x := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 quadraticNormalizedError_eventually_nonneg
  filter_upwards [quadraticNormalizedSpeed_tail,eventually_ge_atTop N,eventually_gt_atTop (0:ℝ)]
    with x hs hx hx0
  have hn := hN x hx
  rcases hn.eq_or_lt with he | he
  · have hz : quadraticNormalizedError x=0 := he.symm
    have hd : 0≤quadraticNormalizedSpeed x := by
      apply ge_of_tendsto ((dQuadraticNormalizedError hx0).tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field,hz,sub_zero]
      exact div_nonneg (hN y (hx.trans hy.le)) (sub_pos.mpr hy).le
    have hf := hs hz.le
    rw [hz,mul_zero] at hf
    exact False.elim ((not_lt_of_ge hd) hf)
  · exact he

theorem quadraticSourceError_eventually_pos : ∀ᶠ x in atTop, 0<quadraticSourceError x := by
  filter_upwards [quadraticNormalizedError_eventually_pos,eventually_gt_atTop (0:ℝ)] with x he hx
  have ht := t_pos hx.le
  exact (div_pos_iff_of_pos_right ht).mp he

end
end RHTower.ThetaCuspModularRatio
