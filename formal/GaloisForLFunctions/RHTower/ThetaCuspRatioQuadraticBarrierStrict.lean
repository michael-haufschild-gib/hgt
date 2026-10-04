import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierGlobal
/-! Strict global nonlinear barrier for the complete modular source. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

private theorem quadraticSourceRate_differentiable {x : ℝ} (hx : 0<x) :
    DifferentiableAt ℝ quadraticSourceRate x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hdK := (dk hx.le).differentiableAt
  have hdU := (du hx.le).differentiableAt
  have hdT := (dt hx.le).differentiableAt
  have hdQ := (dBoundaryRatio hx).differentiableAt
  unfold quadraticSourceRate HTGeometry.ThetaCriticalBarrier.A HTGeometry.ThetaCriticalBarrier.b
  fun_prop

private theorem quadraticWeight_differentiable {x : ℝ} (hx : 0<x) :
    DifferentiableAt ℝ criticalWeight x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  exact ((dk hx.le).differentiableAt.div (du hx.le).differentiableAt hu).mul
    (dt hx.le).differentiableAt

theorem quadraticSourceError_pos {x : ℝ} (hx : 0<x) : 0<quadraticSourceError x := by
  have hn := quadraticSourceError_nonneg hx
  rcases hn.eq_or_lt with he | he
  · have hz : quadraticSourceError x=0 := he.symm
    have hm : IsLocalMin quadraticSourceError x := by
      change ∀ᶠ y in 𝓝 x, quadraticSourceError x≤quadraticSourceError y
      filter_upwards [eventually_gt_nhds hx] with y hy
      rw [hz]
      exact quadraticSourceError_nonneg hy
    have hdz : quadraticSourceSpeed x=0 := hm.hasDerivAt_eq_zero (dQuadraticSourceError hx)
    have hw : 0<criticalWeight x := by
      have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
      have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
      exact mul_pos (div_pos hk hu) (t_pos hx.le)
    have hg : quadraticSourceForce x=0 := by
      have hb := quadraticSourceSpeed_boundary hz
      rw [hdz] at hb
      exact (mul_eq_zero.mp hb.symm).resolve_left hw.ne'
    have hd := ((quadraticSourceRate_differentiable hx).hasDerivAt.mul (dQuadraticSourceError hx)).add
      ((quadraticWeight_differentiable hx).hasDerivAt.mul (dQuadraticSourceForce hx))
    have hds : HasDerivAt quadraticSourceSpeed (criticalWeight x*quadraticSourceForceSpeed x) x := by
      convert hd using 1 <;> first | rfl | skip
      · funext y
        exact quadraticSourceSpeed_split y
      · simp [hz,hdz,hg]
    have heq : deriv quadraticSourceError =ᶠ[𝓝 x] quadraticSourceSpeed := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact (dQuadraticSourceError hy).deriv
    have hdd := hds.congr_of_eventuallyEq heq
    have hneg : deriv (deriv quadraticSourceError) x<0 := by
      rw [hdd.deriv]
      exact mul_neg_of_pos_of_neg hw (quadraticSourceForceSpeed_neg hx hz.le hg)
    have hnonneg := RHTower.DeBruijn.deriv_deriv_nonneg_of_isLocalMin hm
      (dQuadraticSourceError hx).continuousAt
    exact False.elim ((not_lt_of_ge hnonneg) hneg)
  · exact he

theorem boundaryRatio_gt_quadratic_barrier {x : ℝ} (hx : 0<x) :
    1/12-7/(72*k x)<boundaryRatio x-t x*(boundaryRatio x)^2 := by
  have he := quadraticSourceError_pos hx
  unfold quadraticSourceError at he
  rw [criticalError_eq] at he
  unfold HTGeometry.ThetaCriticalBarrier.b at he
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hb : 7*(k x)⁻¹/72=7/(72*k x) := by field_simp [hk]
  rw [hb] at he
  linarith only [he]

end
end RHTower.ThetaCuspModularRatio
