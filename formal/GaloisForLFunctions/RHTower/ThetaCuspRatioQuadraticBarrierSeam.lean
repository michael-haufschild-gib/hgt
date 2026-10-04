import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierLowClock
/-! Exact seam ratio and strict nonlinear source barrier near the seam. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

def seamRatio (h : ℝ) : ℝ := 4*h^2/27+h/3-1/3

theorem seam_quadratic_error_pos {h : ℝ} (hh0 : 15/19≤h) (hh1 : h≤4/5) :
    0<seamRatio h-b h-9*(seamRatio h)^2 := by
  have hh : 0≤h := by linarith only [hh0]
  have hs0 : (15/19:ℝ)^2≤h^2 := by nlinarith only [hh0]
  have hs1 : h^2≤(4/5:ℝ)^2 := by nlinarith only [hh,hh1]
  have hq0 : 1/50 ≤ seamRatio h := by unfold seamRatio; linarith only [hh0,hs0]
  have hq1 : seamRatio h≤1/30 := by unfold seamRatio; linarith only [hh1,hs1]
  have hqp : 0 ≤ seamRatio h := by linarith only [hq0]
  have hb : b h≤1/144 := by unfold b; linarith only [hh0]
  have hp := mul_nonneg hqp (sub_nonneg.mpr hq1)
  nlinarith only [hq0,hb,hp]
end
end HTGeometry.ThetaCriticalBarrier
namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

theorem inverse_clock_zero_bounds : 15/19≤(k 0)⁻¹ ∧ (k 0)⁻¹≤4/5 := by
  have hk0 := k_gt_fiveFourths (show (0:ℝ)≤0 by rfl)
  have hk : 0<k 0 := by linarith only [hk0]
  have hkval : k 0=thetaCuspSelfDualModularScale^2/12-1/3 := by
    simp [k,t,u,A,thetaCuspModularGapAmplitude_zero]
    ring
  have hs := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths
  have hk1 : k 0<19/15 := by rw [hkval]; linarith only [hs]
  constructor
  · rw [inv_eq_one_div,le_div_iff₀ hk]
    linarith only [hk1]
  · rw [inv_eq_one_div,div_le_iff₀ hk]
    linarith only [hk0]

theorem boundaryRatio_seam_tendsto :
    Tendsto boundaryRatio (𝓝[>] (0:ℝ))
      (𝓝 (HTGeometry.ThetaCriticalBarrier.seamRatio ((k 0)⁻¹))) := by
  have h0 : (0:ℝ)≤0 := le_rfl
  have hk : 0<k 0 := lt_trans (by norm_num) (k_gt h0)
  have hu0 : u 0=0 := thetaCuspModularMassDrift_zero
  have ht0 : t 0=9 := by simp [t,hu0]
  have hdN : HasDerivAt (fun x => u x-3*J x) (12+27*k 0-27*(k 0)^2) 0 := by
    convert (du h0).sub ((dJ h0).const_mul 3) using 1 <;> first | rfl | skip
    dsimp [D]
    rw [hu0,ht0]
    field_simp [hk.ne']
    ring
  have hN : Tendsto (fun x => (u x-3*J x)/x) (𝓝[>] (0:ℝ))
      (𝓝 (12+27*k 0-27*(k 0)^2)) := by
    apply (hdN.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))).congr'
    filter_upwards [] with x
    rw [slope_def_field,hu0,J_zero]
    simp
  have hU : Tendsto (fun x => u x/x) (𝓝[>] (0:ℝ)) (𝓝 (k 0*9)) := by
    have hdU := du h0
    rw [ht0] at hdU
    apply (hdU.tendsto_slope.mono_left (nhdsGT_le_nhdsNE (0:ℝ))).congr'
    filter_upwards [] with x
    rw [slope_def_field,hu0,sub_zero,sub_zero]
  have hK : Tendsto k (𝓝[>] (0:ℝ)) (𝓝 (k 0)) :=
    (dk h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hT : Tendsto t (𝓝[>] (0:ℝ)) (𝓝 (9:ℝ)) := by
    simpa only [ht0] using (dt h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hd : (k 0*9)*k 0*9≠0 := by positivity
  have hl := hN.div ((hU.mul hK).mul hT) hd
  have hlim : Tendsto boundaryRatio (𝓝[>] (0:ℝ))
      (𝓝 ((12+27*k 0-27*(k 0)^2)/((k 0*9)*k 0*9))) := by
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0<x at hx
    have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
    have hkx : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
    have ht := (t_pos hx.le).ne'
    simp only [Pi.div_apply]
    unfold boundaryRatio
    field_simp [hx.ne',hu,hkx,ht]
  have he : (12+27*k 0-27*(k 0)^2)/((k 0*9)*k 0*9)=
      HTGeometry.ThetaCriticalBarrier.seamRatio ((k 0)⁻¹) := by
    unfold HTGeometry.ThetaCriticalBarrier.seamRatio
    field_simp [hk.ne']
    ring
  rwa [he] at hlim

theorem quadraticSourceError_seam_pos : ∀ᶠ x in 𝓝[>] (0:ℝ), 0<quadraticSourceError x := by
  have h0 : (0:ℝ)≤0 := le_rfl
  have hu0 : u 0=0 := thetaCuspModularMassDrift_zero
  have ht0 : t 0=9 := by simp [t,hu0]
  have hh : Tendsto (fun x => (k x)⁻¹) (𝓝[>] (0:ℝ)) (𝓝 ((k 0)⁻¹)) :=
    (dInverseK h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun x => HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹)) (𝓝[>] (0:ℝ))
      (𝓝 (HTGeometry.ThetaCriticalBarrier.b ((k 0)⁻¹))) := by
    unfold HTGeometry.ThetaCriticalBarrier.b
    exact tendsto_const_nhds.sub ((hh.const_mul 7).div_const 72)
  have hT : Tendsto t (𝓝[>] (0:ℝ)) (𝓝 (9:ℝ)) := by
    simpa only [ht0] using (dt h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hQ := boundaryRatio_seam_tendsto
  have hl := (hQ.sub hb).sub (hT.mul (hQ.pow 2))
  have hlY : Tendsto quadraticSourceError (𝓝[>] (0:ℝ))
      (𝓝 (HTGeometry.ThetaCriticalBarrier.seamRatio ((k 0)⁻¹)-
        HTGeometry.ThetaCriticalBarrier.b ((k 0)⁻¹)-
          9*(HTGeometry.ThetaCriticalBarrier.seamRatio ((k 0)⁻¹))^2)) := by
    convert hl using 1
    funext x
    exact congrArg (fun z => z-t x*(boundaryRatio x)^2) (criticalError_eq x)
  have hb0 := inverse_clock_zero_bounds
  exact hlY.eventually_const_lt (HTGeometry.ThetaCriticalBarrier.seam_quadratic_error_pos hb0.1 hb0.2)

end
end RHTower.ThetaCuspModularRatio
