import GaloisForLFunctions.RHTower.ThetaCuspRatioCriticalBarrierAlgebra
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryFirstOrder

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

def criticalError : ℝ → ℝ := shiftedBoundaryRatio (-7/72)
def criticalBoundaryForce (x : ℝ) : ℝ :=
  HTGeometry.ThetaCriticalBarrier.D ((k x)⁻¹) (u x^2)
def criticalErrorSpeed (x : ℝ) : ℝ :=
  (k x/u x)*HTGeometry.ThetaCriticalBarrier.G ((k x)⁻¹) (u x^2) (boundaryRatio x)
def criticalForceSpeed (x : ℝ) : ℝ :=
  HTGeometry.ThetaCriticalBarrier.fieldD ((k x)⁻¹) (u x^2) (boundaryRatio x)/
    (6*u x*(k x)⁻¹)

theorem criticalError_eq (x : ℝ) :
    criticalError x=boundaryRatio x-HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹) := by
  unfold criticalError shiftedBoundaryRatio HTGeometry.ThetaCriticalBarrier.b
  ring

theorem J_boundaryRatio {x : ℝ} (hx : 0<x) :
    J x=(u x/3)*(1-k x*t x*boundaryRatio x) := by
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have ht := (t_pos hx.le).ne'
  unfold boundaryRatio
  field_simp [hu,hk,ht]
  ring

theorem dCriticalError {x : ℝ} (hx : 0<x) :
    HasDerivAt criticalError (criticalErrorSpeed x) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  convert dShiftedBoundaryRatio (-7/72) hx using 1 <;> first | rfl | skip
  unfold criticalErrorSpeed HTGeometry.ThetaCriticalBarrier.G shiftedBoundaryRatio
    boundaryResidual boundaryError inverseKVelocity
  rw [J_boundaryRatio hx]
  field_simp [hk,hu]
  simp only [t]
  ring

private theorem dD_poly {h v : ℝ → ℝ} {h' v' x : ℝ}
    (hh : HasDerivAt h h' x) (hv : HasDerivAt v v' x) :
    HasDerivAt (fun y => HTGeometry.ThetaCriticalBarrier.D (h y) (v y))
      (HTGeometry.ThetaCriticalBarrier.Dh (h x) (v x)*h'+
        HTGeometry.ThetaCriticalBarrier.Dv (h x)*v') x := by
  have hb := ((hh.const_mul 7).div_const 72).const_sub (1/12:ℝ)
  have hd := ((((hh.pow 2).const_mul 4).div_const 27).add
    ((hh.const_mul 31).div_const 72)).sub_const (5/12:ℝ)
  have he := hd.add (((hv.mul ((hh.div_const 3).const_add 1)).mul hb).div_const 18)
  convert he using 1 <;> first | rfl | skip
  simp only [Pi.mul_apply,Pi.pow_apply,HTGeometry.ThetaCriticalBarrier.Dh,HTGeometry.ThetaCriticalBarrier.Dv,
    HTGeometry.ThetaCriticalBarrier.b]
  ring

theorem dCriticalForce {x : ℝ} (hx : 0<x) :
    HasDerivAt criticalBoundaryForce (criticalForceSpeed x) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hd := dD_poly (dInverseK hx.le) ((du hx.le).pow 2)
  simp only [Pi.pow_apply] at hd
  convert hd using 1 <;> first | rfl | skip
  unfold criticalForceSpeed HTGeometry.ThetaCriticalBarrier.fieldD
    HTGeometry.ThetaCriticalBarrier.fieldH HTGeometry.ThetaCriticalBarrier.fieldV
    inverseKVelocity
  rw [J_boundaryRatio hx]
  field_simp [hk,hu]
  simp only [t]
  ring

theorem criticalClock_bounds {x : ℝ} (hx : 0<x) : 0<(k x)⁻¹ ∧ (k x)⁻¹≤4/5 := by
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  refine ⟨inv_pos.mpr hk,?_⟩
  rw [inv_eq_one_div,div_le_iff₀ hk]
  linarith [k_gt_fiveFourths hx.le]

theorem criticalForceSpeed_neg {x : ℝ} (hx : 0<x) (he : criticalError x≤0)
    (hD : criticalBoundaryForce x=0) : criticalForceSpeed x<0 := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hh := criticalClock_bounds hx
  have hv : u x^2≤9 := by have ht := t_pos hx.le; dsimp [t] at ht; linarith
  rw [criticalError_eq] at he
  have hg := HTGeometry.ThetaCriticalBarrier.fieldD_neg_at_zero hh.1.le hh.2
    (sq_pos_of_pos hu) hv (sub_nonpos.mp he) hD
  have hhp : 0<(k x)⁻¹ := hh.1
  exact div_neg_of_neg_of_pos hg (show 0<6*u x*(k x)⁻¹ by positivity)

theorem criticalErrorSpeed_boundary {x : ℝ} (hx : 0<x) (he : criticalError x=0) :
    criticalErrorSpeed x=(k x/u x)*t x*criticalBoundaryForce x := by
  have hq : boundaryRatio x=HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹) := by
    rw [criticalError_eq] at he
    exact sub_eq_zero.mp he
  unfold criticalErrorSpeed
  rw [hq,HTGeometry.ThetaCriticalBarrier.G_boundary]
  simp only [criticalBoundaryForce,t]
  ring


end
end RHTower.ThetaCuspModularRatio
