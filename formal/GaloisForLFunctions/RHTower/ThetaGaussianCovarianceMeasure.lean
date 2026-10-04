import GaloisForLFunctions.RHTower.ThetaGaussianAmplitudeQuadratic
import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails

/-! The actual coarea measure has the integrable quadratic envelope needed
to retain covariance feedback through the singular node limit. -/

noncomputable section
open Set MeasureTheory Filter Topology
namespace RHTower.ThetaGaussianCoarea
open HedenmalmThetaSource

local notation "k" => thetaCuspFullSource
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet

def coareaWeight (t : ℝ) : ℝ := 2*t*k t^2
def coareaMass : ℝ := ∫ t in Ioi 0, coareaWeight t
def coareaAverage (f : ℝ → ℝ) : ℝ := (∫ t in Ioi 0, coareaWeight t*f t)/coareaMass
def quadraticVariance : ℝ := coareaAverage (fun t => (quadraticProfile t-coareaAverage quadraticProfile)^2)

theorem coareaWeight_continuous : Continuous coareaWeight := by
  unfold coareaWeight
  exact (continuous_const.mul continuous_id).mul (contDiff_thetaCuspFullSource.continuous.pow 2)

theorem coareaWeight_pos {t : ℝ} (ht : 0 < t) : 0 < coareaWeight t :=
  mul_pos (mul_pos (by norm_num) ht) (sq_pos_of_pos (thetaCuspFullSource_pos_all t))

private theorem source_le_center {t : ℝ} (ht : 0 ≤ t) : k t ≤ k 0 := by
  rcases eq_or_lt_of_le ht with he | hp
  · rw [← he]
  · have h := (strictAntiOn_thetaCuspFullSource_mul_reflect 0).antitoneOn
      (le_refl (0:ℝ)) ht ht
    simp only [zero_add,zero_sub,thetaCuspFullSource_neg] at h
    nlinarith [thetaCuspFullSource_pos_all t,thetaCuspFullSource_pos_all 0]

theorem curvature_exp_envelope {t : ℝ} (ht : 0 ≤ t) : c t ≤ c 0*Real.exp (2*t) := by
  have hd (s : ℝ) : HasDerivAt (fun r => Real.exp (-2*r)*c r)
      (Real.exp (-2*s)*(v s-2*c s)) s := by
    convert! (((hasDerivAt_id s).const_mul (-2)).exp).mul
      (hasDerivAt_thetaCuspLogCurvature s) using 1
    dsimp only [id_eq]
    ring
  have hm : AntitoneOn (fun r => Real.exp (-2*r)*c r) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro s _; exact (hd s).continuousAt.continuousWithinAt
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs0 : 0 ≤ s := (show (0:ℝ) < s by simpa only [interior_Ici,mem_Ioi] using hs).le
      rw [(hd s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (by linarith only [ThetaCurvature.velocityGap_pos hs0])
  have h := hm (show (0:ℝ) ∈ Ici 0 by simp) ht ht
  simp only [mul_zero,Real.exp_zero,one_mul] at h
  have he : Real.exp (2*t)*Real.exp (-2*t)=1 := by
    rw [← Real.exp_add,show 2*t+-2*t=0 by ring,Real.exp_zero]
  have hp := mul_le_mul_of_nonneg_left h (Real.exp_pos (2*t)).le
  rw [← mul_assoc,he,one_mul] at hp
  simpa only [mul_comm] using hp

theorem coareaWeight_exp_integrable (b : ℝ) :
    IntegrableOn (fun t => coareaWeight t*Real.exp (b*t)) (Ioi 0) := by
  have hi := ((HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (b+1)).const_mul (2*k 0)).integrableOn
    (s := Ioi (0:ℝ))
  apply hi.mono'
    ((coareaWeight_continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hkt := thetaCuspFullSource_pos_all t
  have hk0 := thetaCuspFullSource_pos_all 0
  have hk := source_le_center ht0.le
  have hte : t ≤ Real.exp t := by linarith only [Real.add_one_le_exp t]
  change ‖coareaWeight t*Real.exp (b*t)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_pos (mul_pos (coareaWeight_pos ht0) (Real.exp_pos _))]
  calc
    _ = 2*(t*Real.exp (b*t))*k t^2 := by unfold coareaWeight; ring
    _ ≤ 2*(Real.exp t*Real.exp (b*t))*(k 0*k t) := by
      gcongr
      nlinarith only [mul_le_mul_of_nonneg_right hk hkt.le]
    _ = _ := by
      rw [← Real.exp_add,show t+b*t=(b+1)*t by ring]
      ring

theorem coareaWeight_integrable : IntegrableOn coareaWeight (Ioi 0) := by
  simpa only [zero_mul,Real.exp_zero,mul_one] using coareaWeight_exp_integrable 0

theorem coareaMass_pos : 0 < coareaMass := by
  apply (integral_pos_iff_support_of_nonneg_ae _ coareaWeight_integrable).mpr
  · have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioi 0) := by
      simp only [Measure.restrict_apply measurableSet_Ioi,inter_self,Real.volume_Ioi,ENNReal.zero_lt_top]
    exact lt_of_lt_of_le hm (measure_mono (fun t ht => (coareaWeight_pos ht).ne'))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (coareaWeight_pos ht).le

theorem coareaWeight_curvature_sq_integrable :
    IntegrableOn (fun t => coareaWeight t*c (t+1)^2) (Ioi 0) := by
  have hi := (coareaWeight_exp_integrable 4).const_mul (c 0^2*Real.exp 4)
  apply hi.mono'
    ((coareaWeight_continuous.mul
      ((continuous_iff_continuousAt.mpr fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt).comp
        (continuous_id.add continuous_const) |>.pow 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hc := curvature_exp_envelope (show 0 ≤ t+1 by linarith)
  have he : (c 0*Real.exp (2*(t+1)))^2=c 0^2*Real.exp 4*Real.exp (4*t) := by
    rw [mul_pow,pow_two (Real.exp _),← Real.exp_add,mul_assoc,← Real.exp_add]
    congr 1
    ring
  change ‖coareaWeight t*c (t+1)^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (coareaWeight_pos ht0).le (sq_nonneg _))]
  have hs := pow_le_pow_left₀ (thetaCuspLogCurvature_pos (t+1)).le hc 2
  rw [he] at hs
  nlinarith only [mul_le_mul_of_nonneg_left hs (coareaWeight_pos ht0).le]

theorem coareaEnvelope_integrable :
    IntegrableOn (fun t => coareaWeight t*(1+c (t+1)^2)) (Ioi 0) := by
  convert! coareaWeight_integrable.add coareaWeight_curvature_sq_integrable using 1
  funext t
  simp only [Pi.add_apply]
  ring

theorem quadraticProfile_measurable : Measurable quadraticProfile := by
  have hp : Continuous thetaCuspLogDecaySlope := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
  have hc : Continuous c := continuous_iff_continuousAt.mpr
    fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
  exact ((hc.measurable.add (hp.measurable.div measurable_id)).sub measurable_const).div_const 4

theorem coareaWeight_profile_integrable :
    IntegrableOn (fun t => coareaWeight t*quadraticProfile t) (Ioi 0) := by
  apply coareaEnvelope_integrable.mono'
    ((coareaWeight_continuous.measurable.mul quadraticProfile_measurable).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖coareaWeight t*quadraticProfile t‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (coareaWeight_pos ht)]
  apply mul_le_mul_of_nonneg_left _ (coareaWeight_pos ht).le
  have hc := quadraticProfile_bound ht
  nlinarith only [hc,sq_nonneg (c (t+1)-1/2)]

theorem coareaWeight_profile_sq_integrable :
    IntegrableOn (fun t => coareaWeight t*quadraticProfile t^2) (Ioi 0) := by
  apply coareaWeight_curvature_sq_integrable.mono'
    ((coareaWeight_continuous.measurable.mul (quadraticProfile_measurable.pow_const 2)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change ‖coareaWeight t*quadraticProfile t^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (coareaWeight_pos ht).le (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (coareaWeight_pos ht).le
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (quadraticProfile t))
    (quadraticProfile_bound ht) 2

theorem coareaWeight_centeredProfile_sq_integrable (m : ℝ) :
    IntegrableOn (fun t => coareaWeight t*(quadraticProfile t-m)^2) (Ioi 0) := by
  convert! (coareaWeight_profile_sq_integrable.sub
    (coareaWeight_profile_integrable.const_mul (2*m))).add
      (coareaWeight_integrable.const_mul (m^2)) using 1
  funext t
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem quadraticVariance_pos : 0 < quadraticVariance := by
  let m := coareaAverage quadraticProfile
  have hi := coareaWeight_centeredProfile_sq_integrable m
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi (0:ℝ)), 0 ≤ coareaWeight t*(quadraticProfile t-m)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (coareaWeight_pos ht).le (sq_nonneg _)
  have hpos : 0 < ∫ t in Ioi 0, coareaWeight t*(quadraticProfile t-m)^2 := by
    by_contra hn
    have hz : (∫ t in Ioi 0, coareaWeight t*(quadraticProfile t-m)^2)=0 :=
      le_antisymm (not_lt.mp hn) (integral_nonneg_of_ae hnn)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).mp hz
    have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi
      (coareaWeight_continuous.continuousOn.mul
        ((quadraticProfile_continuousOn.sub continuousOn_const).pow 2)) continuousOn_const
    have he (t : ℝ) (ht : 0 < t) : quadraticProfile t=m := by
      have h := heq ht
      have hs : (quadraticProfile t-m)^2=0 := (mul_eq_zero.mp h).resolve_left (coareaWeight_pos ht).ne'
      nlinarith only [hs]
    have hm := quadraticProfile_strictMono (show (1:ℝ) ∈ Ioi 0 by norm_num)
      (show (2:ℝ) ∈ Ioi 0 by norm_num) (by norm_num : (1:ℝ) < 2)
    rw [he 1 (by norm_num),he 2 (by norm_num)] at hm
    exact (lt_irrefl _) hm
  exact div_pos hpos coareaMass_pos

end RHTower.ThetaGaussianCoarea
