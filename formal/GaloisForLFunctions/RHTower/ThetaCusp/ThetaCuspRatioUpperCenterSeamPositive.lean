import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamRegularity

namespace RHTower.ThetaCuspUpperSeam
noncomputable section
set_option autoImplicit false
open scoped ContDiff
open Filter Topology MvPolynomial
open ThetaCuspOddDirectionTransport ThetaOddSeamCurvature ThetaCuspModularRatio
open HTGeometry.ThetaRatioWeightedSquare HTGeometry.ThetaRatioInfinity
open HTGeometry.ThetaSeamOddCurvature
local notation "load" => (10000000000000:ℝ)
local notation "scale" => thetaCuspSelfDualModularScale^2

theorem hasDerivAt_shearGap (x : ℝ) :
    HasDerivAt shearGap (2*u x*thetaCuspModularTransverseShear x/3) x := by
  convert ((hasDerivAt_thetaCuspModularTransverseShear x).sub
    ((hasDerivAt_thetaCuspModularMassDrift x).const_mul 2 |>.div_const 3)).sub
      ((hasDerivAt_id x).const_mul 4) using 1 <;>
    first | rfl | (dsimp only [shearGap,u,thetaCuspModularMassDrift,id_eq]; ring)

theorem shearGap_zero : shearGap 0=0 := by
  simp [shearGap,u,thetaCuspModularTransverseShear,thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]

theorem shearGap_deriv_zero : deriv shearGap 0=0 := by
  rw [(hasDerivAt_shearGap 0).deriv]
  simp [u]

def scaledUpperA (x : ℝ) : ℝ :=
  dslope (deriv (normalizedBase load)) 0 x+
    dslope shearGap 0 x*deriv (ThetaCuspHeadGrowth.centerDrive load) x/4

def scaledB (x : ℝ) : ℝ := dslope (deriv normalizedB) 0 x

def scaledD (x : ℝ) : ℝ := dslope (deriv normalizedD) 0 x

theorem scaledUpperA_zero : scaledUpperA 0=deriv (deriv (normalizedBase load)) 0 := by
  simp only [scaledUpperA,dslope_same,shearGap_deriv_zero,zero_mul,zero_div,add_zero]

theorem scaledB_zero : scaledB 0=deriv (deriv normalizedB) 0 := dslope_same _ _

theorem scaledD_zero : scaledD 0=deriv (deriv normalizedD) 0 := dslope_same _ _

private theorem continuous_scaledUpperA : ContinuousAt scaledUpperA 0 := by
  have ha : ContDiff ℝ ∞ (deriv (normalizedBase load)) := by
    simpa using (normalizedBase_regular load).1.iterate_deriv 1
  have hl : ContDiff ℝ ∞ (deriv (ThetaCuspHeadGrowth.centerDrive load)) := by
    simpa using (centerDrive_smooth load).iterate_deriv 1
  exact (continuousAt_dslope_same.mpr (ha.differentiable (by simp) 0)).add
    (((continuousAt_dslope_same.mpr (hasDerivAt_shearGap 0).differentiableAt).mul
      hl.continuous.continuousAt).div_const 4)

private theorem continuous_scaledB : ContinuousAt scaledB 0 := by
  have hb : ContDiff ℝ ∞ (deriv normalizedB) := by
    simpa using normalizedB_regular.1.iterate_deriv 1
  exact continuousAt_dslope_same.mpr (hb.differentiable (by simp) 0)

private theorem continuous_scaledD : ContinuousAt scaledD 0 := by
  have hd : ContDiff ℝ ∞ (deriv normalizedD) := by
    simpa using normalizedD_regular.1.iterate_deriv 1
  exact continuousAt_dslope_same.mpr (hd.differentiable (by simp) 0)

theorem scaled_seam_signs :
    0 < scaledUpperA 0 ∧ 0 < scaledUpperA 0*scaledD 0-scaledB 0^2 := by
  rw [scaledUpperA_zero,scaledB_zero,scaledD_zero]
  constructor
  · simpa using actual_curvature_positive 0
  · have hd : 0 < quadraticDet scale 1 := by
      let u := 192-10*scale
      let v := 10*scale-191
      have hu : 0 ≤ u := by
        dsimp [u]
        linarith [thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths]
      have hv : 0 ≤ v := by
        dsimp [v]
        linarith [thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one]
      have huv : u+v=1 := by dsimp [u,v]; ring
      have hav : (191*u+192*v)/10=scale := by dsimp [u,v]; ring
      have h := quadraticDet_pos hu hv (by rw [huv]; norm_num)
      rwa [hav,huv] at h
    have hp : 0 < pH 0 scale 1 := by
      rw [pH_one]
      norm_num [sourceJet,HTGeometry.modularThetaEvenSeamSourcePolynomial]
      linarith [thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one]
    rw [normalizedBase_second_zero,normalizedB_second_zero,normalizedD_second_zero]
    have he : Na scale 1/(pH 0 scale 1)^7*(Nd scale 1/(pH 0 scale 1)^7)-
        (Nb scale 1/(pH 0 scale 1)^7)^2=quadraticDet scale 1/(pH 0 scale 1)^14 := by
      unfold quadraticDet
      field_simp [hp.ne']
    rw [he]
    exact div_pos hd (pow_pos hp 14)

theorem scaledUpperA_identity (x : ℝ) :
    x*scaledUpperA x=deriv (normalizedBase load) x+
      shearGap x*deriv (ThetaCuspHeadGrowth.centerDrive load) x/4 := by
  have ha := sub_smul_dslope (deriv (normalizedBase load)) 0 x
  simp only [sub_zero,smul_eq_mul,(normalizedBase_regular load).2] at ha
  have he := sub_smul_dslope shearGap 0 x
  simp only [sub_zero,smul_eq_mul,shearGap_zero] at he
  calc
    _ = x*dslope (deriv (normalizedBase load)) 0 x+
        (x*dslope shearGap 0 x)*deriv (ThetaCuspHeadGrowth.centerDrive load) x/4 := by
      unfold scaledUpperA
      ring
    _ = _ := by rw [ha,he]

theorem scaledB_identity (x : ℝ) : x*scaledB x=deriv normalizedB x := by
  simpa only [scaledB,sub_zero,smul_eq_mul,normalizedB_regular.2] using
    sub_smul_dslope (deriv normalizedB) 0 x

theorem scaledD_identity (x : ℝ) : x*scaledD x=deriv normalizedD x := by
  simpa only [scaledD,sub_zero,smul_eq_mul,normalizedD_regular.2] using
    sub_smul_dslope (deriv normalizedD) 0 x

/-- One source neighborhood works simultaneously for every real direction. -/
theorem actual_upper_quadratic_positive_near_seam :
    ∀ᶠ x in 𝓝 (0:ℝ), 0 < x → ∀ eta : ℝ,
      0 < (eval (actualSquarePoint x)
        (upperCenterQuadratic (load:ℂ) (eta:ℂ))).re := by
  have ha : Tendsto scaledUpperA (𝓝 0) (𝓝 (scaledUpperA 0)) := continuous_scaledUpperA
  have hd : Tendsto (fun x => scaledUpperA x*scaledD x-scaledB x^2) (𝓝 0)
      (𝓝 (scaledUpperA 0*scaledD 0-scaledB 0^2)) :=
    (continuous_scaledUpperA.mul continuous_scaledD).sub (continuous_scaledB.pow 2)
  filter_upwards [ha.eventually_const_lt scaled_seam_signs.1,
    hd.eventually_const_lt scaled_seam_signs.2] with x hax hdx
  intro hx eta
  have hq : 0 < scaledUpperA x+2*scaledB x*eta+scaledD x*eta^2 := by
    by_cases ht : eta=0
    · simpa [ht] using hax
    · have hgain := mul_pos hdx (sq_pos_of_ne_zero ht)
      have hs := sq_nonneg (scaledUpperA x+scaledB x*eta)
      by_contra hn
      have hn' := mul_nonpos_of_nonneg_of_nonpos hax.le (le_of_not_gt hn)
      nlinarith only [hgain,hs,hn']
  rw [actual_upper_center_real_identity load eta hx]
  calc
    0 < endpointNormalizer x*(x*(scaledUpperA x+2*scaledB x*eta+scaledD x*eta^2)) :=
      mul_pos (endpointNormalizer_pos hx) (mul_pos hx hq)
    _ = _ := by
      congr 1
      calc
        _ = x*scaledUpperA x+2*(x*scaledB x)*eta+(x*scaledD x)*eta^2 := by ring
        _ = _ := by rw [scaledUpperA_identity,scaledB_identity,scaledD_identity]

end
end RHTower.ThetaCuspUpperSeam
