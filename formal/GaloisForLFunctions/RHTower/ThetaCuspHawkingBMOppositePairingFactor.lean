import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceHorizonGaussBound
import GaloisForLFunctions.HTGeometry.QuadraticEndpointProducts
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceFundamentalContinuation
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSpatialODE
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceParameterHolomorphy
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicComplementarySolutionJet

/-! The original opposite-horizon Gauss product and its uniform logarithmic endpoint bound. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Set Filter Topology Metric GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def oppositePairingFactor (w chi : ℂ) (z : ℝ) : ℂ :=
  gaussFactor w chi false (z:ℂ)*gaussFactor (-w) chi false (z:ℂ)/(2*(Real.sqrt (1-z):ℂ))

/-- The actual incoming/opposite product has one common linear bound at its logarithmic endpoint. -/
theorem oppositePairingFactor_uniform_first_bound (w chi : ℂ) (hw : w.im ≠ 0) :
    ∃ R C M : ℝ, 0 < R ∧ 0 ≤ C ∧ 0 ≤ M ∧
      ∀ u ∈ ball w R, ∀ z ∈ Icc (0:ℝ) (1/2),
        ‖oppositePairingFactor u chi z-(1/2:ℂ)‖ ≤ C*z ∧
        ‖oppositePairingFactor u chi z‖ ≤ M := by
  obtain ⟨Rp,Cp,hRp,hCp,hp⟩ := horizonGauss_uniform_first_bound w chi hw
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨Rm,Cm,hRm,hCm,hm⟩ := horizonGauss_uniform_first_bound (-w) chi
    (by simpa only [Complex.neg_im,neg_ne_zero] using hw)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  let S := Cp*(Cm+1)+Cm
  let C := 2*S+9/4
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨min Rp Rm,C,C+1,lt_min hRp hRm,hC,by positivity,?_⟩
  intro u hu z hz
  have hup := ball_subset_ball (min_le_left Rp Rm) hu
  have hum : -u ∈ ball (-w) Rm := by
    simpa only [mem_ball,dist_neg_neg] using ball_subset_ball (min_le_right Rp Rm) hu
  have hep := hp u hup z hz
  have hem := hm (-u) hum z hz
  have hz0 : 0 ≤ z := hz.1
  have hz1 : z ≤ 1 := by linarith [hz.2]
  let gp := gaussFactor u chi false (z:ℂ)
  let gm := gaussFactor (-u) chi false (z:ℂ)
  let j : ℂ := 1/(2*(Real.sqrt (1-z):ℂ))
  have hgm : ‖gm‖ ≤ Cm+1 := by
    have hn := norm_sub_norm_le gm (1:ℂ)
    rw [norm_one] at hn
    dsimp only [gm] at hn ⊢
    linarith [mul_le_mul_of_nonneg_left hz1 hCm]
  have hprod : ‖gp*gm-1‖ ≤ S*z := by
    rw [show gp*gm-1=(gp-1)*gm+(gm-1) by ring]
    calc
      _ ≤ ‖(gp-1)*gm‖+‖gm-1‖ := norm_add_le _ _
      _ = ‖gp-1‖*‖gm‖+‖gm-1‖ := by rw [norm_mul]
      _ ≤ (Cp*z)*(Cm+1)+Cm*z := by gcongr
      _ = S*z := by dsimp [S]; ring
  have hj : ‖j-(1/2:ℂ)‖ ≤ (9/4:ℝ)*z := by
    have he := inverse_sqrt_jacobian_second_bound hz
    have hn := norm_sub_norm_le (j-(1/2:ℂ)) ((1/4:ℂ)*(z:ℂ))
    rw [norm_mul,show ‖(1/4:ℂ)‖=(1/4:ℝ) by norm_num,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hz.1] at hn
    change ‖j-(1/2:ℂ)-(1/4:ℂ)*(z:ℂ)‖ ≤ 2*z^2 at he
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  have hjb : ‖j‖ ≤ 2 := by
    have hn := norm_sub_norm_le j (1/2:ℂ)
    rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num] at hn
    nlinarith [hz.2]
  have hV : ‖oppositePairingFactor u chi z-(1/2:ℂ)‖ ≤ C*z := by
    calc
      _ = ‖(gp*gm-1)*j+(j-(1/2:ℂ))‖ := by
        congr 1
        dsimp [oppositePairingFactor,gp,gm,j]
        ring
      _ ≤ ‖(gp*gm-1)*j‖+‖j-(1/2:ℂ)‖ := norm_add_le _ _
      _ = ‖gp*gm-1‖*‖j‖+‖j-(1/2:ℂ)‖ := by rw [norm_mul]
      _ ≤ (S*z)*2+(9/4:ℝ)*z := by gcongr
      _ = C*z := by dsimp [C]; ring
  refine ⟨hV,?_⟩
  have hn := norm_sub_norm_le (oppositePairingFactor u chi z) (1/2:ℂ)
  rw [show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num] at hn
  linarith [mul_le_mul_of_nonneg_left hz1 hC]

private theorem gauss_frequency_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => gaussFactor u chi false (z:ℂ)) w := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hw] with u hu
  exact horizonGauss_frequency_differentiableAt u chi (z:ℂ) hu
    (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1] using hz.2)

theorem oppositePairingFactor_analyticAt (w chi : ℂ) (hw : w.im ≠ 0)
    {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    AnalyticAt ℂ (fun u => oppositePairingFactor u chi z) w := by
  have hp := gauss_frequency_analyticAt w chi hw hz
  have hm := (gauss_frequency_analyticAt (-w) chi
    (by simpa only [Complex.neg_im,neg_ne_zero] using hw) hz).comp analyticAt_id.neg
  unfold oppositePairingFactor
  exact (hp.mul hm).div analyticAt_const
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)))))

theorem oppositePairingFactor_continuousAt (w chi : ℂ) {z : ℝ} (hz : z ∈ Ioo (0:ℝ) 1) :
    ContinuousAt (oppositePairingFactor w chi) z := by
  have hp := (gaussFactor_derivatives_continued (w := w) (chi := chi) false
    (enorm_ofReal_lt_one hz.1 hz.2)).1.comp_ofReal.continuousAt
  have hm := (gaussFactor_derivatives_continued (w := -w) (chi := chi) false
    (enorm_ofReal_lt_one hz.1 hz.2)).1.comp_ofReal.continuousAt
  unfold oppositePairingFactor
  exact (hp.mul hm).div (by fun_prop)
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)))))

/-- Removing the opposite indicial powers recovers the literal radial density wherever the incoming quotient is defined. -/
theorem oppositePairingFactor_density (s chi a J K w : ℂ) {z : ℝ}
    (hz : z ∈ Ioo (0:ℝ) 1) (hh : horizon w chi z ≠ 0) :
    (continuedResponse s chi a J K z w/horizon w chi z)*oppositePairingFactor w chi z/(z:ℂ)=
      continuedResponse s chi a J K z w*horizon (-w) chi z/
        (2*(z:ℂ)*(Real.sqrt (1-z):ℂ)) := by
  have hz0 : (z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz.1)
  have hr0 : (Real.sqrt (1-z):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)))
  have hp : horizon w chi z*horizon (-w) chi z=
      gaussFactor w chi false (z:ℂ)*gaussFactor (-w) chi false (z:ℂ) := by
    dsimp only [horizon,dress,power]
    calc
      _ = ((z:ℂ)^(w/2)*(z:ℂ)^(-w/2))*
        (gaussFactor w chi false (z:ℂ)*gaussFactor (-w) chi false (z:ℂ)) := by ring
      _ = _ := by
        rw [← Complex.cpow_add _ _ hz0,show w/2+ -w/2=0 by ring,Complex.cpow_zero,one_mul]
  rw [oppositePairingFactor,← hp]
  field_simp [hh,hz0,hr0]

end
end RHTower.D4BMLaplaceRadial
