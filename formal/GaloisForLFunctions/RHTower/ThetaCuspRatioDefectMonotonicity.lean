import GaloisForLFunctions.RHTower.ThetaCuspRatioDefectSign
import GaloisForLFunctions.RHTower.ThetaCuspModularRatioSlopeBarrier

/-! # Strict increase of the actual modular ratio defect

A nonpositive speed has negative acceleration. Any negative speed would persist
and force the complete-source defect below zero. The resulting strict source
inequality constrains the transported Schur-gap sign problem; that problem
remains open.
-/

namespace RHTower.ThetaCuspModularRatio
noncomputable section
open Set Filter Topology

def defectVelocity (x : ℝ) : ℝ :=
  k x^2*t x-6*k x-4+2*u x*(k x+2/3)*J x

private def defectAcceleration (x : ℝ) : ℝ :=
  t x*k x*J x*(6*k x+8/3)-2*u x*k x^3*t x-12*(k x+1/3)*J x+
    4*u x*(k x+1/3)*(J x)^2+2*u x*(k x+2/3)*defectVelocity x

private theorem dJ_velocity {x : ℝ} (hx : 0≤x) :
    HasDerivAt J (defectVelocity x) x := by
  have hk : k x≠0 := by linarith [k_gt hx]
  convert dJ hx using 1
  dsimp [D,defectVelocity]
  field_simp [hk]

private theorem dVelocity {x : ℝ} (hx : 0≤x) :
    HasDerivAt defectVelocity (defectAcceleration x) x := by
  have h := (((((dk hx).pow 2).mul (dt hx)).sub ((dk hx).const_mul 6)).sub_const 4).add
    ((((du hx).const_mul 2).mul ((dk hx).add_const (2/3:ℝ))).mul (dJ_velocity hx))
  convert h using 1 <;> first | rfl | (dsimp [defectVelocity,defectAcceleration]; ring)

private theorem velocity_deriv_neg {x : ℝ} (hx : 0<x) (hv : defectVelocity x≤0) :
    deriv defectVelocity x<0 := by
  have hu : 0<u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx)
  have hj0 := J_nonneg hx.le
  have hj1 := J_le_third_drift hx.le
  have hz0 : 0≤J x/u x := div_nonneg hj0 hu.le
  have hz1 : J x/u x≤1/3 := (div_le_iff₀ hu).mpr (by linarith only [hj1])
  have hs : ThetaRatioDefectSlope.speed (u x) (k x) (J x/u x)=defectVelocity x := by
    unfold ThetaRatioDefectSlope.speed defectVelocity t
    field_simp [hu.ne']
  have ha : ThetaRatioDefectSlope.acceleration (u x) (k x) (J x/u x)=
      defectAcceleration x := by
    unfold ThetaRatioDefectSlope.acceleration
    rw [hs]
    unfold defectAcceleration t
    field_simp [hu.ne']
  have hn := ThetaRatioDefectSlope.acceleration_neg hu (t_pos hx.le)
    (k_gt_fiveFourths hx.le) hz0 hz1 (by rwa [hs])
  rwa [ha,← (dVelocity hx.le).deriv] at hn

theorem defectVelocity_nonneg {b : ℝ} (hb : 0<b) : 0≤defectVelocity b := by
  by_contra hn
  have hv : defectVelocity b<0 := lt_of_not_ge hn
  have hbound : ∀ y, b≤y → defectVelocity y≤defectVelocity b := by
    intro y hby
    apply image_le_of_deriv_right_lt_deriv_boundary
      (f := defectVelocity) (f' := fun z => deriv defectVelocity z)
      (a := b) (b := y)
      (fun z hz => (dVelocity (hb.le.trans hz.1)).continuousAt.continuousWithinAt)
      (fun z hz => (dVelocity (hb.le.trans hz.1)).differentiableAt.hasDerivAt.hasDerivWithinAt)
      (B := fun _ => defectVelocity b) (B' := fun _ => 0) le_rfl
      (fun z => hasDerivAt_const z (defectVelocity b)) ?_ ⟨hby,le_rfl⟩
    intro z hz he
    have hneg := velocity_deriv_neg (lt_of_lt_of_le hb hz.1) (by rw [he]; exact hv.le)
    exact hneg
  have hanti : AntitoneOn (fun y => J y-defectVelocity b*y) (Ici b) := by
    have hd (y : ℝ) (hy : b≤y) : HasDerivAt (fun z => J z-defectVelocity b*z)
        (defectVelocity y-defectVelocity b) y := by
      convert (dJ_velocity (hb.le.trans hy)).sub
        ((hasDerivAt_id y).const_mul (defectVelocity b)) using 1 <;> first | rfl | simp
    apply antitoneOn_of_deriv_nonpos (convex_Ici b)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (show b≤y from
        (show b<y by simpa [interior_Ici] using hy).le)).differentiableAt.differentiableWithinAt)
    intro y hy
    have hby : b≤y := (show b<y by simpa [interior_Ici] using hy).le
    rw [(hd y hby).deriv]
    exact sub_nonpos.mpr (hbound y hby)
  let y := b+(J b+1)/(-defectVelocity b)
  have hden : 0< -defectVelocity b := neg_pos.mpr hv
  have hjb := J_nonneg hb.le
  have hby : b≤y := by
    dsimp [y]
    have hp : 0≤(J b+1)/(-defectVelocity b) := by positivity
    linarith only [hp]
  have hi : defectVelocity b*(y-b)= -(J b+1) := by
    dsimp [y]
    field_simp [hv.ne]
    ring
  have hm := hanti (show b∈Ici b by simp) hby hby
  have hjy := J_nonneg (hb.le.trans hby)
  nlinarith only [hi,hm,hjy]

theorem defectVelocity_pos {x : ℝ} (hx : 0<x) : 0<defectVelocity x := by
  have hn := defectVelocity_nonneg hx
  rcases hn.eq_or_lt with he | he
  · have hz : defectVelocity x=0 := he.symm
    have hdnonneg : 0≤defectAcceleration x := by
      apply ge_of_tendsto ((dVelocity hx.le).tendsto_slope.mono_left (nhdsGT_le_nhdsNE x))
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [slope_def_field,hz,sub_zero]
      exact div_nonneg (defectVelocity_nonneg (hx.trans hy)) (sub_pos.mpr hy).le
    have hdneg := velocity_deriv_neg hx (by rw [hz])
    rw [(dVelocity hx.le).deriv] at hdneg
    exact False.elim ((not_lt_of_ge hdnonneg) hdneg)
  · exact he

/-- The actual ratio defect has positive speed at every positive center. -/
theorem J_deriv_pos {x : ℝ} (hx : 0<x) : 0<deriv J x := by
  rw [(dJ_velocity hx.le).deriv]
  exact defectVelocity_pos hx

theorem J_strictMonoOn : StrictMonoOn J (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (0:ℝ))
    (fun x hx => (dJ hx).continuousAt.continuousWithinAt)
  intro x hx
  exact J_deriv_pos (by simpa only [interior_Ici,mem_Ioi] using hx)

theorem J_pos {x : ℝ} (hx : 0<x) : 0<J x := by
  have h := J_strictMonoOn (show (0:ℝ)∈Ici 0 by simp) hx.le hx
  rwa [J_zero] at h

/-- A source-derived differential constraint beyond the static ratio cone. -/
theorem defect_velocity_constraint {x : ℝ} (hx : 0<x) :
    6*k x+4<k x^2*t x+2*u x*(k x+2/3)*J x := by
  have h := defectVelocity_pos hx
  unfold defectVelocity at h
  linarith only [h]

end
end RHTower.ThetaCuspModularRatio
