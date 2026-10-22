import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalBarrierSeamTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioBoundaryTrap

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

/-- The complete modular source lies above its exact affine critical barrier. -/
theorem criticalError_nonneg {x : ℝ} (hx : 0<x) : 0≤criticalError x := by
  have hax : ∀ᶠ a in 𝓝[>] (0:ℝ), a<x :=
    (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds
  have hap : ∀ᶠ a in 𝓝[>] (0:ℝ), 0<a := self_mem_nhdsWithin
  obtain ⟨a,ha,hfa,hax⟩ :=
    (hap.and (criticalError_seam_pos.and hax)).exists
  obtain ⟨c,hfc,hxc⟩ := (criticalError_eventually_pos.and (eventually_ge_atTop x)).exists
  have h0 (y : ℝ) (hy : y∈Icc a c) : 0<y := ha.trans_le hy.1
  have hn := HTGeometry.TwoFunctionTrap.nonneg_between
    (f := criticalError) (g := criticalBoundaryForce)
    (f' := criticalErrorSpeed) (g' := criticalForceSpeed)
    (w := fun y => (k y/u y)*t y)
    (fun y hy => dCriticalError (h0 y hy))
    (fun y hy => dCriticalForce (h0 y hy))
    (fun y hy => by
      have hu : 0<u y := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (h0 y hy))
      have hk : 0<k y := lt_trans (by norm_num) (k_gt (h0 y hy).le)
      exact mul_pos (div_pos hk hu) (t_pos (h0 y hy).le))
    (fun y hy he => criticalErrorSpeed_boundary (h0 y hy) he)
    (fun y hy he hg => criticalForceSpeed_neg (h0 y hy) he hg) hfa hfc
  exact hn x ⟨hax.le,hxc⟩

theorem boundaryRatio_ge_critical_barrier {x : ℝ} (hx : 0<x) :
    1/12-7/(72*k x)≤boundaryRatio x := by
  have he := criticalError_nonneg hx
  rw [criticalError_eq] at he
  unfold HTGeometry.ThetaCriticalBarrier.b at he
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hb : 7*(k x)⁻¹/72=7/(72*k x) := by field_simp [hk]
  rw [hb] at he
  linarith only [he]


end
end RHTower.ThetaCuspModularRatio
