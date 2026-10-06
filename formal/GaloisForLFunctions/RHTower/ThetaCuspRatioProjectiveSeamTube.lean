import GaloisForLFunctions.RHTower.ThetaCuspModularRatioSlopeBarrier

namespace RHTower.ThetaCuspModularRatio
noncomputable section
set_option autoImplicit false
open Set

/-- The complete orbit's defect from its regular seam projective surface. -/
def seamDefect (x : ℝ) : ℝ := w x-2*u x/3-4*(u x/k x)/9

def seamDefectVelocity (x : ℝ) : ℝ :=
  (u x)^2*(2*k x/3+4/9)-2*u x*J x/3+
    u x*J x*(8*(k x+1/3)/(9*(k x)^2))

theorem seamDefect_zero : seamDefect 0=0 := by
  simp [seamDefect,u,w,thetaCuspModularTransverseShear,
    thetaCuspModularDrift_re_zero,thetaCuspModularODEState_Z_zero]

theorem dSeamDefect {x : ℝ} (hx : 0≤x) :
    HasDerivAt seamDefect (seamDefectVelocity x) x := by
  have hk : k x≠0 := by linarith [k_gt hx]
  have hd := ((dw hx).sub (((du hx).const_mul 2).div_const 3)).sub
    ((((du hx).div (dk hx) hk).const_mul 4).div_const 9)
  change HasDerivAt seamDefect _ x at hd
  convert hd using 1
  dsimp [seamDefectVelocity,t]
  field_simp [hk]
  ring

theorem seamDefectVelocity_bounds {x : ℝ} (hx : 0<x) :
    0<seamDefectVelocity x ∧ seamDefectVelocity x<2*k x*(u x)^2 := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 1<k x := by linarith [k_gt_fiveFourths hx.le]
  have hj := J_nonneg hx.le
  have hjb := J_le_third_drift hx.le
  have hq0 : 0≤8*(k x+1/3)/(9*(k x)^2) := by positivity
  have hq1 : 8*(k x+1/3)/(9*(k x)^2)<4/3 := by
    apply (div_lt_iff₀ (show 0<9*(k x)^2 by positivity)).mpr
    have hs : k x≤(k x)^2 := by
      nlinarith only [mul_nonneg (show 0≤k x-1 by linarith) (show 0≤k x by linarith)]
    nlinarith only [hk,hs]
  have hslack : 0≤u x/3-J x := sub_nonneg.mpr hjb
  constructor
  · have hpos : 0<(u x)^2*(2*k x/3+2/9) := by positivity
    have hp : 0≤(2*u x/3)*(u x/3-J x) := by positivity
    have hq : 0≤u x*J x*(8*(k x+1/3)/(9*(k x)^2)) := by positivity
    have he : seamDefectVelocity x=(u x)^2*(2*k x/3+2/9)+
        (2*u x/3)*(u x/3-J x)+
        u x*J x*(8*(k x+1/3)/(9*(k x)^2)) := by
      unfold seamDefectVelocity
      ring
    linarith only [he,hpos,hp,hq]
  · have hc : 0<4*k x/3-2/3 := by linarith only [hk]
    have hpos : 0<(u x)^2*(4*k x/3-2/3) := by positivity
    have hp : 0≤(2/3:ℝ)*u x*(u x/3-J x) := by positivity
    have hq : 0≤u x*J x*(4/3-8*(k x+1/3)/(9*(k x)^2)) := by
      exact mul_nonneg (mul_nonneg hu.le hj) (sub_pos.mpr hq1).le
    have he : 2*k x*(u x)^2-seamDefectVelocity x=
        (u x)^2*(4*k x/3-2/3)+(2/3:ℝ)*u x*(u x/3-J x)+
        u x*J x*(4/3-8*(k x+1/3)/(9*(k x)^2)) := by
      unfold seamDefectVelocity
      ring
    linarith only [he,hpos,hp,hq]

theorem seamDefect_strictMonoOn : StrictMonoOn seamDefect (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0:ℝ))
    (fun x hx => (dSeamDefect hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx0 : 0<x := by simpa only [interior_Ici,mem_Ioi] using hx
  rw [(dSeamDefect hx0.le).deriv]
  exact (seamDefectVelocity_bounds hx0).1

theorem seamDefect_pos {x : ℝ} (hx : 0<x) : 0<seamDefect x := by
  have h := seamDefect_strictMonoOn (show (0:ℝ)∈Ici 0 by simp) hx.le hx
  rwa [seamDefect_zero] at h

def seamDefectReserve (x : ℝ) : ℝ := (2/3:ℝ)*(u x)^3-t x*seamDefect x

theorem dSeamDefectReserve {x : ℝ} (hx : 0≤x) :
    HasDerivAt seamDefectReserve
      (t x*(2*k x*(u x)^2-seamDefectVelocity x)+
        2*u x*k x*t x*seamDefect x) x := by
  have hd := (((du hx).pow 3).const_mul (2/3:ℝ)).sub
    ((dt hx).mul (dSeamDefect hx))
  change HasDerivAt seamDefectReserve _ x at hd
  convert hd using 1
  ring

theorem seamDefectReserve_strictMonoOn : StrictMonoOn seamDefectReserve (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0:ℝ))
    (fun x hx => (dSeamDefectReserve hx).continuousAt.continuousWithinAt)
  intro x hx
  have hx0 : 0<x := by simpa only [interior_Ici,mem_Ioi] using hx
  rw [(dSeamDefectReserve hx0.le).deriv]
  have ht := t_pos hx0.le
  have hr := seamDefect_pos hx0
  have hv := sub_pos.mpr (seamDefectVelocity_bounds hx0).2
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx0)
  have hk : 0<k x := by linarith [k_gt hx0.le]
  positivity

theorem seamDefect_weighted_bounds {x : ℝ} (hx : 0<x) :
    0<t x*seamDefect x ∧ t x*seamDefect x<(2/3:ℝ)*(u x)^3 := by
  have h := seamDefectReserve_strictMonoOn
    (show (0:ℝ)∈Ici 0 by simp) hx.le hx
  have hz : seamDefectReserve 0=0 := by simp [seamDefectReserve,seamDefect_zero,u]
  rw [hz] at h
  exact ⟨mul_pos (t_pos hx.le) (seamDefect_pos hx),by
    dsimp [seamDefectReserve] at h
    linarith only [h]⟩

/-- Polynomial seam compatibility, retaining the complete source's projective coordinate. -/
theorem actual_projective_seam_tube {x : ℝ} (hx : 0<x) :
    0<(9-(u x)^2)*(9*(k x)^2-6*k x-4-9*k x*(J x/u x)) ∧
    (9-(u x)^2)*(9*(k x)^2-6*k x-4-9*k x*(J x/u x))<
      6*k x*(u x)^2 := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hk : 0<k x := by linarith [k_gt hx.le]
  have he : (9-(u x)^2)*(9*(k x)^2-6*k x-4-9*k x*(J x/u x))=
      (9*k x/u x)*(t x*seamDefect x) := by
    unfold t seamDefect J
    field_simp [hu.ne',hk.ne']
    ring
  rw [he]
  have hc : 0<9*k x/u x := by positivity
  obtain ⟨h0,h1⟩ := seamDefect_weighted_bounds hx
  constructor
  · exact mul_pos hc h0
  · have hm := mul_lt_mul_of_pos_left h1 hc
    have hi : (9*k x/u x)*((2/3:ℝ)*(u x)^3)=6*k x*(u x)^2 := by
      field_simp [hu.ne']
      ring
    rwa [hi] at hm

end
end RHTower.ThetaCuspModularRatio

