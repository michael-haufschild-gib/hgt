import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticForceHighSign
import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticForceMidClock
import GaloisForLFunctions.RHTower.ThetaCuspRatioQuadraticForceDynamics
/-! The complete actual-source forcing trap, with no source-sign premise. -/

namespace RHTower.ThetaCuspModularRatio
noncomputable section

theorem source_kinetic_clock_upper {x : ℝ} (hx : 0<x) :
    9-u x^2≤(361/25)*((k x)⁻¹)^2 := by
  have hk : k x≠0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx.le))
  have he := mul_le_mul_of_nonneg_right (kineticGap_lt hx.le).le (sq_nonneg ((k x)⁻¹))
  have hi : k x^2*t x*((k x)⁻¹)^2=t x := by field_simp [hk]
  rwa [hi] at he

theorem source_quadratic_failure_ratio_lt {x : ℝ} (hx : 0<x)
    (hy : quadraticSourceError x≤0) :
    boundaryRatio x<(6/5)*HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹) := by
  have hh := criticalClock_bounds hx
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hv0 : 0<u x^2 := sq_pos_of_pos hu
  have hv1 : u x^2≤9 := by have ht := t_pos hx.le; dsimp [t] at ht; linarith only [ht]
  have hyF : HTGeometry.ThetaCriticalBarrier.quadraticError ((k x)⁻¹) (u x^2) (boundaryRatio x)≤0 := by
    rwa [quadraticSourceError_eq] at hy
  have hs := HTGeometry.ThetaCriticalBarrier.failure_small_branch hh.1.le hh.2 hv0 hv1
    (boundaryRatio_nonneg hx) hyF (source_ratio_gap hx) (source_kinetic_clock_upper hx)
  have hb := HTGeometry.ThetaCriticalBarrier.b_nonneg hh.2
  have hc := criticalError_pos hx
  rw [criticalError_eq] at hc
  have hq : 0<boundaryRatio x := by linarith only [hc,hb]
  have hp := mul_lt_mul_of_pos_left (show (5/6:ℝ)<1-(9-u x^2)*boundaryRatio x by linarith only [hs]) hq
  unfold HTGeometry.ThetaCriticalBarrier.quadraticError at hyF
  nlinarith only [hp,hyF]

theorem source_quadratic_failure_high_box {x : ℝ} (hx : 0<x)
    (hy : quadraticSourceError x≤0) (hR : quadraticSourceForce x=0) :
    HTGeometry.ThetaCriticalBarrier.HighClockBox ((k x)⁻¹) (u x^2) (boundaryRatio x) := by
  have hh := criticalClock_bounds hx
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hv0 : 0≤u x^2 := sq_nonneg (u x)
  have hv1 : u x^2<9 := by have ht := t_pos hx.le; dsimp [t] at ht; linarith only [ht]
  have hsmall := source_quadratic_failure_ratio_lt hx hy
  have hc := criticalError_pos hx
  rw [criticalError_eq] at hc
  have hqLower : HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹)≤boundaryRatio x := by linarith only [hc]
  have hh2 : 2/3<(k x)⁻¹ := by
    by_contra hn
    have hp := quadraticSourceError_pos_of_low_clock hx (le_of_not_gt hn)
    linarith only [hp,hy]
  have hh3 : 3/4≤(k x)⁻¹ := by
    by_contra hn
    have hr := HTGeometry.ThetaCriticalBarrier.mid_force_neg hh2.le (lt_of_not_ge hn)
      hv0 hv1 hqLower hsmall
    change quadraticSourceForce x<0 at hr
    linarith only [hr,hR]
  refine ⟨hh3,hh.2,hv0,hv1.le,boundaryRatio_nonneg hx,?_⟩
  have hb : HTGeometry.ThetaCriticalBarrier.b ((k x)⁻¹)≤1/96 := by
    unfold HTGeometry.ThetaCriticalBarrier.b
    linarith only [hh3]
  linarith only [hsmall,hb]

theorem quadraticSourceForceSpeed_neg {x : ℝ} (hx : 0<x)
    (hy : quadraticSourceError x≤0) (hR : quadraticSourceForce x=0) :
    quadraticSourceForceSpeed x<0 := by
  have H := source_quadratic_failure_high_box hx hy hR
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hyF : HTGeometry.ThetaCriticalBarrier.quadraticError ((k x)⁻¹) (u x^2) (boundaryRatio x)≤0 := by
    rwa [quadraticSourceError_eq] at hy
  have hlow : -(9-u x^2)*(boundaryRatio x)^2≤
      HTGeometry.ThetaCriticalBarrier.quadraticError ((k x)⁻¹) (u x^2) (boundaryRatio x) := by
    rw [←quadraticSourceError_eq]
    unfold quadraticSourceError
    have hc := criticalError_pos hx
    change -t x*(boundaryRatio x)^2≤criticalError x-t x*(boundaryRatio x)^2
    linarith only [hc]
  have hf := HTGeometry.ThetaCriticalBarrier.forcingDrift_neg_high H (sq_pos_of_pos hu) hyF hlow hR
  unfold quadraticSourceForceSpeed
  exact mul_neg_of_pos_of_neg (quadraticFieldScale_pos hx) hf

end
end RHTower.ThetaCuspModularRatio
