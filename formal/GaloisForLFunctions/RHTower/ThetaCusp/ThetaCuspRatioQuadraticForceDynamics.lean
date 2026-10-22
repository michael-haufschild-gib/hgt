import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticForceCompletion
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBarrierLowClock
/-! Incidence of the polynomial forcing field with the actual modular source. -/

namespace HTGeometry.ThetaCriticalBarrier
noncomputable section

theorem dQuadraticBoundaryCore_comp {h v q : ℝ → ℝ} {h' v' q' x : ℝ}
    (hh : HasDerivAt h h' x) (hv : HasDerivAt v v' x) (hq : HasDerivAt q q' x) :
    HasDerivAt (fun y => quadraticBoundaryCore (h y) (v y) (q y))
      (Rh (h x) (v x) (q x)*h'+Rv (h x) (v x) (q x)*v'+Rq (h x) (v x) (q x)*q') x := by
  have dh := hh.differentiableAt
  have dv := hv.differentiableAt
  have dq := hq.differentiableAt
  have hd : DifferentiableAt ℝ (fun y => quadraticBoundaryCore (h y) (v y) (q y)) x := by
    unfold quadraticBoundaryCore D A b fieldH
    fun_prop
  convert hd.hasDerivAt using 1 <;> first | rfl | skip
  change Rh (h x) (v x) (q x)*h'+Rv (h x) (v x) (q x)*v'+Rq (h x) (v x) (q x)*q'=
    deriv (fun y => quadraticBoundaryCore (h y) (v y) (q y)) x
  simp only [quadraticBoundaryCore,D,A,b,fieldH,Rh,Rv,Rq,Ah,Av,Aq,Hhh,Hhv,Hhq,Dh,Dv,forcingFactor]
  simp (disch := fun_prop) [deriv_div_const,hh.deriv,hv.deriv,hq.deriv]
  ring
end
end HTGeometry.ThetaCriticalBarrier
namespace RHTower.ThetaCuspModularRatio
noncomputable section

def quadraticFieldScale (x : ℝ) : ℝ := k x/(6*u x)
def quadraticSourceForceSpeed (x : ℝ) : ℝ :=
  quadraticFieldScale x*HTGeometry.ThetaCriticalBarrier.forcingDrift
    ((k x)⁻¹) (u x^2) (boundaryRatio x)

theorem quadraticFieldScale_pos {x : ℝ} (hx : 0<x) : 0<quadraticFieldScale x := by
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  unfold quadraticFieldScale
  positivity

theorem dInverseK_quadratic_field {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => (k y)⁻¹)
      (quadraticFieldScale x*HTGeometry.ThetaCriticalBarrier.fieldH ((k x)⁻¹) (u x^2) (boundaryRatio x)) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  convert dInverseK hx.le using 1
  unfold quadraticFieldScale HTGeometry.ThetaCriticalBarrier.fieldH inverseKVelocity
  rw [J_boundaryRatio hx]
  field_simp [hk,hu]
  simp only [t]
  ring

theorem dSquareU_quadratic_field {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => u y^2)
      (quadraticFieldScale x*HTGeometry.ThetaCriticalBarrier.fieldV (u x^2)) x := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  convert (du hx.le).pow 2 using 1 <;> first | rfl | skip
  unfold quadraticFieldScale HTGeometry.ThetaCriticalBarrier.fieldV
  field_simp [hu]
  simp only [t]
  ring

theorem dBoundaryRatio_quadratic_field {x : ℝ} (hx : 0<x) :
    HasDerivAt boundaryRatio
      (quadraticFieldScale x*HTGeometry.ThetaCriticalBarrier.qField ((k x)⁻¹) (u x^2) (boundaryRatio x)) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  convert dBoundaryRatio hx using 1
  unfold quadraticFieldScale HTGeometry.ThetaCriticalBarrier.qField HTGeometry.ThetaCriticalBarrier.G
    HTGeometry.ThetaCriticalBarrier.fieldH boundaryError
  field_simp [hk,hu]
  simp only [t]
  ring

theorem dQuadraticSourceForce {x : ℝ} (hx : 0<x) :
    HasDerivAt quadraticSourceForce (quadraticSourceForceSpeed x) x := by
  have hd := HTGeometry.ThetaCriticalBarrier.dQuadraticBoundaryCore_comp
    (dInverseK_quadratic_field hx) (dSquareU_quadratic_field hx) (dBoundaryRatio_quadratic_field hx)
  convert hd using 1 <;> first | rfl | skip
  unfold quadraticSourceForceSpeed HTGeometry.ThetaCriticalBarrier.forcingDrift
  ring

end
end RHTower.ThetaCuspModularRatio
