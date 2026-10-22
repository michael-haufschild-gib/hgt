import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBarrierTrap
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBarrierSeam
/-! Global nonnegativity of the nonlinear source error by the two-function trap. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

def quadraticSourceRate (x : ℝ) : ℝ :=
  (k x/u x)*(1-2*t x*boundaryRatio x)*
    HTGeometry.ThetaCriticalBarrier.A ((k x)⁻¹) (u x^2) (boundaryRatio x)

theorem quadraticSourceSpeed_split (x : ℝ) :
    quadraticSourceSpeed x=quadraticSourceRate x*quadraticSourceError x+
      criticalWeight x*quadraticSourceForce x := by
  unfold quadraticSourceSpeed
  rw [HTGeometry.ThetaCriticalBarrier.quadraticField_split,←quadraticSourceError_eq]
  unfold quadraticSourceRate criticalWeight quadraticSourceForce t
  by_cases hu : u x=0
  · simp [hu]
  · field_simp [hu]
    ring

theorem quadraticSourceSpeed_boundary {x : ℝ} (hz : quadraticSourceError x=0) :
    quadraticSourceSpeed x=criticalWeight x*quadraticSourceForce x := by
  rw [quadraticSourceSpeed_split,hz,mul_zero,zero_add]

theorem quadraticSourceError_nonneg {x : ℝ} (hx : 0<x) : 0≤quadraticSourceError x := by
  have hax : ∀ᶠ a in 𝓝[>] (0:ℝ), a<x :=
    (eventually_lt_nhds hx).filter_mono nhdsWithin_le_nhds
  have hap : ∀ᶠ a in 𝓝[>] (0:ℝ), 0<a := self_mem_nhdsWithin
  obtain ⟨a,ha,hfa,hax⟩ := (hap.and (quadraticSourceError_seam_pos.and hax)).exists
  obtain ⟨c,hfc,hxc⟩ := (quadraticSourceError_eventually_pos.and (eventually_ge_atTop x)).exists
  have h0 (y : ℝ) (hy : y∈Icc a c) : 0<y := ha.trans_le hy.1
  have hn := HTGeometry.TwoFunctionTrap.nonneg_between
    (f := quadraticSourceError) (g := quadraticSourceForce)
    (f' := quadraticSourceSpeed) (g' := quadraticSourceForceSpeed)
    (w := criticalWeight)
    (fun y hy => dQuadraticSourceError (h0 y hy))
    (fun y hy => dQuadraticSourceForce (h0 y hy))
    (fun y hy => by
      have hu : 0<u y := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos (h0 y hy))
      have hk : 0<k y := lt_trans (by norm_num) (k_gt (h0 y hy).le)
      exact mul_pos (div_pos hk hu) (t_pos (h0 y hy).le))
    (fun _ _ he => quadraticSourceSpeed_boundary he)
    (fun y hy he hg => quadraticSourceForceSpeed_neg (h0 y hy) he hg) hfa hfc
  exact hn x ⟨hax.le,hxc⟩

end
end RHTower.ThetaCuspModularRatio
