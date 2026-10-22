import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalBarrierDynamics
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryEscape

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

def criticalNumerator (x : ℝ) : ℝ :=
  u x*(1+7*t x/72-k x*t x/12)-3*J x

theorem criticalNumerator_eq {x : ℝ} (hx : 0<x) :
    criticalNumerator x=u x*k x*t x*criticalError x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have ht := (t_pos hx.le).ne'
  unfold criticalNumerator criticalError shiftedBoundaryRatio boundaryRatio
  field_simp [hu,hk,ht]
  ring

theorem dCriticalNumerator_zero :
    HasDerivAt criticalNumerator (12+(279/8)*k 0-(135/4)*(k 0)^2) 0 := by
  have h0 : (0:ℝ)≤0 := le_rfl
  have hu0 : u 0=0 := thetaCuspModularMassDrift_zero
  have ht0 : t 0=9 := by simp [t,hu0]
  have hk : k 0≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt h0))
  have hd := ((du h0).mul ((((dt h0).const_mul 7).div_const 72).const_add 1 |>.sub
    (((dk h0).mul (dt h0)).div_const 12))).sub ((dJ h0).const_mul 3)
  convert hd using 1 <;> first | rfl | skip
  simp only [Pi.sub_apply,Pi.mul_apply,hu0,ht0,J_zero,zero_mul,mul_zero,zero_add,add_zero,D]
  field_simp [hk]
  ring

theorem criticalNumerator_derivative_pos : 0<12+(279/8)*k 0-(135/4)*(k 0)^2 := by
  have hk0 := k_gt_fiveFourths (show (0:ℝ)≤0 by rfl)
  have hkval : k 0=thetaCuspSelfDualModularScale^2/12-1/3 := by
    simp [k,t,u,A,thetaCuspModularGapAmplitude_zero]
    ring
  have hs := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths
  have hk1 : k 0<19/15 := by rw [hkval]; linarith
  have hksq : (k 0)^2≤(19/15)*k 0 := by
    nlinarith only [mul_nonneg (show 0≤k 0 by linarith) (show 0≤19/15-k 0 by linarith)]
  nlinarith only [hk0,hk1,hksq]

theorem criticalError_seam_pos : ∀ᶠ x in 𝓝[>] (0:ℝ), 0<criticalError x := by
  have hlim := dCriticalNumerator_zero.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))
  have hp := hlim.eventually_const_lt criticalNumerator_derivative_pos
  have hz : criticalNumerator 0=0 := by simp [criticalNumerator,u,J_zero]
  filter_upwards [self_mem_nhdsWithin,hp] with x hx hs
  rw [slope_def_field,hz,sub_zero,sub_zero] at hs
  have hn : 0<criticalNumerator x := (div_pos_iff_of_pos_right hx).mp hs
  rw [criticalNumerator_eq hx] at hn
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have ht := t_pos hx.le
  exact (mul_pos_iff_of_pos_left (show 0<u x*k x*t x by positivity)).mp hn

theorem criticalErrorSpeed_tail :
    ∀ᶠ x in atTop, criticalError x≤0 → criticalErrorSpeed x<10*criticalError x := by
  have hclock := inverse_k_tendsto_zero.eventually_lt_const (show (0:ℝ)<2/3 by norm_num)
  have hV := drift_square_tendsto.eventually_const_lt (show (8:ℝ)<9 by norm_num)
  filter_upwards [hclock,hV,eventually_gt_atTop (0:ℝ)] with x hh hv hx he
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hhp := (criticalClock_bounds hx).1
  have hv9 : u x^2<9 := by have ht := t_pos hx.le; dsimp [t] at ht; linarith
  have hq := boundaryRatio_nonneg hx
  have hd := HTGeometry.ThetaCriticalBarrier.D_neg_low hhp.le hh.le (sq_nonneg (u x)) hv9.le
  have hA := HTGeometry.ThetaCriticalBarrier.A_pos_tail hhp.le hh.le hv.le hv9.le hq
  have hG : HTGeometry.ThetaCriticalBarrier.G ((k x)⁻¹) (u x^2) (boundaryRatio x)<
      30*criticalError x := by
    rw [HTGeometry.ThetaCriticalBarrier.G_split,← criticalError_eq]
    have hp := mul_neg_of_pos_of_neg (show 0<9-u x^2 by linarith) hd
    have hm := mul_le_mul_of_nonpos_left hA he
    linarith
  have hg := boundaryGain_lower hx
  have hg0 : 0<k x/u x := lt_of_lt_of_le (by norm_num) hg
  have hm := mul_lt_mul_of_pos_left hG hg0
  have hn := mul_le_mul_of_nonpos_right hg (show 30*criticalError x≤0 by linarith)
  unfold criticalErrorSpeed
  nlinarith only [hm,hn]

theorem criticalError_eventually_nonneg : ∀ᶠ x in atTop, 0≤criticalError x := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 criticalErrorSpeed_tail
  refine eventually_atTop.2 ⟨max 1 N,?_⟩
  intro b hb
  have hb1 := (le_max_left 1 N).trans hb
  have hbN := (le_max_right 1 N).trans hb
  by_contra hn
  have hf : criticalError b<0 := lt_of_not_ge hn
  apply HTGeometry.BoundedUnstableSelection.no_bounded_escape
    (fun x => -criticalError x) (fun x => -criticalErrorSpeed x)
    b (3/(2*u 1^2)+|(-7/72:ℝ)|+1) (-10*criticalError b) (by nlinarith only [hf])
    (fun x hx => (dCriticalError (show 0<x by linarith)).neg)
    (fun x hx => by
      have he := (shiftedBoundaryRatio_bounded (-7/72) (hb1.trans hx)).1
      change -(3/(2*u 1^2)+|(-7/72:ℝ)|+1)≤criticalError x at he
      linarith)
  intro x hbx hfx
  have hle : criticalError x≤criticalError b := by linarith only [hfx]
  have hs := hN x (hbN.trans hbx) (hle.trans hf.le)
  linarith only [hs,hle]

theorem criticalError_eventually_pos : ∀ᶠ x in atTop, 0<criticalError x := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 criticalError_eventually_nonneg
  filter_upwards [criticalErrorSpeed_tail,eventually_ge_atTop N,
    eventually_gt_atTop (0:ℝ)] with x hs hx hx0
  have hn := hN x hx
  rcases hn.eq_or_lt with he | he
  · have hz : criticalError x=0 := he.symm
    have hd : 0≤criticalErrorSpeed x := by
      apply ge_of_tendsto ((dCriticalError hx0).tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field,hz,sub_zero]
      exact div_nonneg (hN y (hx.trans hy.le)) (sub_pos.mpr hy).le
    have hf := hs hz.le
    rw [hz,mul_zero] at hf
    exact False.elim ((not_lt_of_ge hd) hf)
  · exact he


end
end RHTower.ThetaCuspModularRatio
