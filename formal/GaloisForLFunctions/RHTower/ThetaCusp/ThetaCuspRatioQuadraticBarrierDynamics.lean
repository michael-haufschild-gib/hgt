import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioQuadraticBoundaryLowClock
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioCriticalBarrierStrict

namespace RHTower.ThetaCuspModularRatio
noncomputable section

def quadraticSourceError (x : ℝ) : ℝ := criticalError x-t x*(boundaryRatio x)^2
def quadraticSourceSpeed (x : ℝ) : ℝ :=
  (k x/(6*u x))*HTGeometry.ThetaCriticalBarrier.quadraticField
    ((k x)⁻¹) (u x^2) (boundaryRatio x)

theorem quadraticSourceError_eq (x : ℝ) : quadraticSourceError x=
    HTGeometry.ThetaCriticalBarrier.quadraticError ((k x)⁻¹) (u x^2) (boundaryRatio x) := by
  unfold quadraticSourceError HTGeometry.ThetaCriticalBarrier.quadraticError
  rw [criticalError_eq]
  dsimp [t]
  ring

theorem dQuadraticSourceError {x : ℝ} (hx : 0<x) :
    HasDerivAt quadraticSourceError (quadraticSourceSpeed x) x := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have hu : u x≠0 := ne_of_gt (neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx))
  have hd := (dCriticalError hx).sub ((dt hx.le).mul ((dBoundaryRatio hx).pow 2))
  simp only [Pi.pow_apply] at hd
  convert hd using 1 <;> first | rfl | skip
  simp only [quadraticSourceSpeed,criticalErrorSpeed,HTGeometry.ThetaCriticalBarrier.quadraticField,
    HTGeometry.ThetaCriticalBarrier.G,HTGeometry.ThetaCriticalBarrier.fieldH,boundaryError]
  field_simp [hk,hu]
  simp only [t]
  ring

theorem source_ratio_gap {x : ℝ} (hx : 0<x) : t x*boundaryRatio x<(k x)⁻¹ := by
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hj := J_pos hx
  have he := J_boundaryRatio hx
  have hg : k x*t x*boundaryRatio x<1 := by
    by_contra hn
    have hn0 : 0≤k x*t x*boundaryRatio x-1 := by linarith
    have hn1 := mul_nonneg (show 0≤u x/3 by positivity) hn0
    nlinarith only [he,hj,hn1]
  have hm := mul_lt_mul_of_pos_left hg (inv_pos.mpr hk)
  have heq : (k x)⁻¹*(k x*t x*boundaryRatio x)=t x*boundaryRatio x := by
    field_simp [hk.ne']
  simpa only [heq,mul_one] using hm

theorem quadraticSourceSpeed_neg_at_low_zero {x : ℝ} (hx : 0<x)
    (hh : (k x)⁻¹≤2/3) (he : quadraticSourceError x=0) : quadraticSourceSpeed x<0 := by
  have hk : 0<k x := lt_trans (by norm_num) (k_gt hx.le)
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have ht := t_pos hx.le
  have hv : u x^2<9 := by dsimp [t] at ht; linarith
  have hkin := mul_le_mul_of_nonneg_right (kineticGap_lt hx.le).le (sq_nonneg ((k x)⁻¹))
  have hkinEq : k x^2*t x*((k x)⁻¹)^2=t x := by field_simp [hk.ne']
  rw [hkinEq] at hkin
  have hg := source_ratio_gap hx
  rw [quadraticSourceError_eq] at he
  have hf := HTGeometry.ThetaCriticalBarrier.quadratic_boundary_field_neg_low
    (inv_pos.mpr hk) hh (sq_pos_of_pos hu) hv (boundaryRatio_nonneg hx) he hg hkin
  unfold quadraticSourceSpeed
  exact mul_neg_of_pos_of_neg (by positivity) hf

end
end RHTower.ThetaCuspModularRatio
