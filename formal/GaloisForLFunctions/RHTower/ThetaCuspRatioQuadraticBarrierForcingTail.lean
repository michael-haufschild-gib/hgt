import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticBarrierDynamics

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

/-- The first-order source forcing, expressed using finite limiting coordinates. -/
def scaledForceModel (h v q z e : ℝ) : ℝ :=
  (-2*z*q)*(D h v+q^2*A h v q)+
    (4*h/27+31/72-z/216+v*(-5/72-7*h/216)/18)+
    e*(q+1/12)*(A h v q+18)+
    (1/144)*(-5*z+(2/9)*v*(3-h)+
      (2/3)*v*(1+h/3)*z*(q+b h)+(7/108)*v*(1+h/3)*(9-v))+
    (7/216)*q*(-(4/3)*(3+h)*v*(h-q*(9-v)))-2*z*q^2

theorem scaled_force_model (k v q : ℝ) (hk : k≠0) :
    k*quadraticBoundaryCore (k⁻¹) v q=
      scaledForceModel (k⁻¹) v q (k*(9-v)) (k*(q-1/12)) := by
  unfold quadraticBoundaryCore scaledForceModel D A fieldH b
  field_simp [hk]
  ring

theorem scaledForceModel_base : scaledForceModel 0 9 (1/12) 0 (-7/72)= -7/16 := by
  norm_num [scaledForceModel,D,A,b]

end
end HTGeometry.ThetaCriticalBarrier
namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Filter Topology

def quadraticSourceForce (x : ℝ) : ℝ :=
  HTGeometry.ThetaCriticalBarrier.quadraticBoundaryCore ((k x)⁻¹) (u x^2) (boundaryRatio x)

theorem quadraticSourceForce_scaled_tendsto :
    Tendsto (fun x => k x*quadraticSourceForce x) atTop (𝓝 (-7/16:ℝ)) := by
  let f : ℝ×ℝ×ℝ×ℝ×ℝ → ℝ := fun p =>
    HTGeometry.ThetaCriticalBarrier.scaledForceModel p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  have hc : Continuous f := by
    dsimp [f,HTGeometry.ThetaCriticalBarrier.scaledForceModel,
      HTGeometry.ThetaCriticalBarrier.D,HTGeometry.ThetaCriticalBarrier.A,HTGeometry.ThetaCriticalBarrier.b]
    fun_prop
  have hp := inverse_k_tendsto_zero.prodMk_nhds
    (drift_square_tendsto.prodMk_nhds (boundaryRatio_tendsto.prodMk_nhds
      (k_mul_t_tendsto_zero.prodMk_nhds boundaryRatio_firstOrder_tendsto)))
  have hl := (hc.tendsto (0,9,1/12,0,(-7/72:ℝ))).comp hp
  change Tendsto (fun x => HTGeometry.ThetaCriticalBarrier.scaledForceModel
      ((k x)⁻¹) (u x^2) (boundaryRatio x) (k x*t x) (k x*(boundaryRatio x-1/12)))
    atTop (𝓝 (HTGeometry.ThetaCriticalBarrier.scaledForceModel 0 9 (1/12) 0 (-7/72))) at hl
  rw [HTGeometry.ThetaCriticalBarrier.scaledForceModel_base] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  exact (HTGeometry.ThetaCriticalBarrier.scaled_force_model (k x) (u x^2)
    (boundaryRatio x) hk).symm

end
end RHTower.ThetaCuspModularRatio
