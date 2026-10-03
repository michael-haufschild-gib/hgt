import GaloisForLFunctions.RHTower.ThetaTailGaussianSubmodular
import GaloisForLFunctions.RHTower.ThetaTailConfluentCoordinatePort
import GaloisForLFunctions.HTGeometry.MonotoneLikelihoodRatio

/-! Strict positivity of actual Schur cross terms above every nonnegative anchor.
Gaussian coarea separates a strict source comparison from positive covariance.
The coordinate-port upper bound and higher principal minors remain separate. -/

noncomputable section
open MeasureTheory Set
namespace RHTower.ThetaGaussianCoarea

local notation "k" => thetaCuspFullSource
local notation "H" => thetaTailFirstMomentKernel

private theorem density_mul_amplitude (b x u : ℝ) :
    density b b u*anchoredAmplitude b x u=density b x u := by
  unfold density anchoredAmplitude
  rw [← Real.exp_add]
  congr 1
  ring

private theorem product_integrable {b x y : ℝ} (hb : 0 ≤ b) (hx : b < x) (hy : b < y) :
    IntegrableOn (fun u => density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u) (Ioi 0) := by
  apply (density_integrable hb hb).mono'
    ((((density_continuous b b).mul (anchoredAmplitude_continuous b x)).mul
      (anchoredAmplitude_continuous b y)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hp := mul_pos (mul_pos (density_pos b b u) (anchoredAmplitude_pos b x u)) (anchoredAmplitude_pos b y u)
  change ‖density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u‖ ≤ density b b u
  rw [Real.norm_eq_abs,abs_of_pos hp]
  calc
    _ ≤ density b b u*anchoredAmplitude b x u := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (anchoredAmplitude_le_one hb hy hu.le)
        (mul_pos (density_pos b b u) (anchoredAmplitude_pos b x u)).le
    _ ≤ density b b u := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (anchoredAmplitude_le_one hb hx hu.le)
        (density_pos b b u).le

private theorem covariance_nonneg {b x y : ℝ} (hb : 0 ≤ b) (hx : b < x) (hy : b < y) :
    (∫ u in Ioi 0, density b x u)*(∫ u in Ioi 0, density b y u) ≤
      (∫ u in Ioi 0, density b b u)*
        (∫ u in Ioi 0, density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hf : Integrable (fun u => density b b u*anchoredAmplitude b x u) μ := by
    change IntegrableOn (fun u => density b b u*anchoredAmplitude b x u) (Ioi 0)
    simpa only [density_mul_amplitude] using density_integrable hb (hb.trans hx.le)
  have hh : Integrable (density b b) μ := density_integrable hb hb
  have hgf : Integrable (fun u => anchoredAmplitude b y u*(density b b u*anchoredAmplitude b x u)) μ := by
    change IntegrableOn (fun u => anchoredAmplitude b y u*(density b b u*anchoredAmplitude b x u)) (Ioi 0)
    convert! product_integrable hb hx hy using 1
    funext u
    ring
  have hgh : Integrable (fun u => anchoredAmplitude b y u*density b b u) μ := by
    change IntegrableOn (fun u => anchoredAmplitude b y u*density b b u) (Ioi 0)
    have he : (fun u => anchoredAmplitude b y u*density b b u)=density b y := by
      funext u
      rw [mul_comm,density_mul_amplitude]
    rw [he]
    exact density_integrable hb (hb.trans hy.le)
  have hprod : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ, 0 < z.1 ∧ 0 < z.2 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ⟨hs,ht⟩
  have hkernel : ∀ᵐ z : ℝ×ℝ ∂μ.prod μ,
      0 ≤ (anchoredAmplitude b y z.2-anchoredAmplitude b y z.1)*
        (density b b z.1*(density b b z.2*anchoredAmplitude b x z.2)-
          density b b z.2*(density b b z.1*anchoredAmplitude b x z.1)) := by
    filter_upwards [hprod] with z hz
    have hm : 0 ≤ (anchoredAmplitude b y z.2-anchoredAmplitude b y z.1)*(anchoredAmplitude b x z.2-anchoredAmplitude b x z.1) := by
      rcases le_total z.1 z.2 with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos
          (sub_nonpos.mpr ((anchoredAmplitude_strictAnti hb hy).antitoneOn hz.1.le hz.2.le h))
          (sub_nonpos.mpr ((anchoredAmplitude_strictAnti hb hx).antitoneOn hz.1.le hz.2.le h))
      · exact mul_nonneg
          (sub_nonneg.mpr ((anchoredAmplitude_strictAnti hb hy).antitoneOn hz.2.le hz.1.le h))
          (sub_nonneg.mpr ((anchoredAmplitude_strictAnti hb hx).antitoneOn hz.2.le hz.1.le h))
    convert! mul_nonneg (mul_pos (density_pos b b z.1) (density_pos b b z.2)).le hm using 1
    ring
  have h := HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel hf hh hgf hgh hkernel
  have he (u : ℝ) : anchoredAmplitude b y u*density b b u=density b y u := by
    rw [mul_comm,density_mul_amplitude]
  simp only [density_mul_amplitude,he] at h
  simp only [density_mul_amplitude]
  simpa only [μ,mul_comm] using h

private theorem integral_product_lt {b x y : ℝ} (hb : 0 ≤ b) (hx : b < x) (hy : b < y) :
    (∫ u in Ioi 0, density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u) <
      ∫ u in Ioi 0, density x y u := by
  let f : ℝ → ℝ := fun u => density x y u-density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u
  have hi : IntegrableOn f (Ioi 0) := (density_integrable (hb.trans hx.le) (hb.trans hy.le)).sub (product_integrable hb hx hy)
  have hp (u : ℝ) (hu : u ∈ Ioi 0) : 0 < f u := sub_pos.mpr (density_anchored_product_lt hb hx hy hu)
  have hn : ∀ᵐ u ∂volume.restrict (Ioi 0), 0 ≤ f u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hp u hu).le
  have hs : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioi 0) := by
      simp only [Measure.restrict_apply measurableSet_Ioi,inter_self,Real.volume_Ioi,ENNReal.zero_lt_top]
    exact lt_of_lt_of_le hm (measure_mono fun u hu => (hp u hu).ne')
  have h := (integral_pos_iff_support_of_nonneg_ae hn hi).mpr hs
  rw [show f=(fun u => density x y u-density b b u*anchoredAmplitude b x u*anchoredAmplitude b y u) from rfl,
    integral_sub (density_integrable (hb.trans hx.le) (hb.trans hy.le)) (product_integrable hb hx hy)] at h
  linarith only [h]

/-- Every finite pair above a nonnegative anchor has a positive actual Schur cross minor. -/
theorem anchored_schur_cross_pos {b x y : ℝ} (hb : 0 ≤ b) (hx : b < x) (hy : b < y) :
    H b x*H b y < H b b*H x y := by
  have hbb : 0 < H b b := by
    rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
    exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos b
  have hm : 0 < ∫ u in Ioi 0, density b b u := by
    rw [integral_density hb hb]
    exact div_pos hbb (mul_pos (thetaCuspFullSource_pos_all b) (thetaCuspFullSource_pos_all b))
  have h := (covariance_nonneg hb hx hy).trans_lt
    (mul_lt_mul_of_pos_left (integral_product_lt hb hx hy) hm)
  rw [integral_density hb (hb.trans hx.le),integral_density hb (hb.trans hy.le),
    integral_density hb hb,integral_density (hb.trans hx.le) (hb.trans hy.le)] at h
  have hden : 0 < (k b*k x)*(k b*k y) := by
    exact mul_pos (mul_pos (thetaCuspFullSource_pos_all b) (thetaCuspFullSource_pos_all x))
      (mul_pos (thetaCuspFullSource_pos_all b) (thetaCuspFullSource_pos_all y))
  have hscaled := mul_lt_mul_of_pos_right h hden
  convert! hscaled using 1 <;>
    field_simp [(thetaCuspFullSource_pos_all b).ne',
      (thetaCuspFullSource_pos_all x).ne',(thetaCuspFullSource_pos_all y).ne']

/-- The larger old-node projection coefficient is positive above every nonnegative anchor. -/
theorem anchored_positive_node_coefficient_pos {b z y : ℝ}
    (hb : 0 ≤ b) (hz : b < z) (hy : b < y) :
    0 < (H b b*H z y-H b z*H b y)/ThetaSturm.determinant b z := by
  exact div_pos (sub_pos.mpr (anchored_schur_cross_pos hb hz hy))
    (ThetaTailTwoPoint.kernel_two_point_det_pos hz.ne)

/-- Every positive finite pair has a strictly positive actual center Schur cross minor. -/
theorem center_schur_cross_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    H 0 x*H 0 y < H 0 0*H x y :=
  anchored_schur_cross_pos (le_refl (0:ℝ)) hx hy

/-- The positive old-node coefficient of the literal center projection is strictly positive. -/
theorem positive_node_coefficient_pos {z y : ℝ} (hz : 0 < z) (hy : 0 < y) :
    0 < (H 0 0*H z y-H 0 z*H 0 y)/ThetaSturm.determinant 0 z :=
  anchored_positive_node_coefficient_pos (le_refl (0:ℝ)) hz hy

end RHTower.ThetaGaussianCoarea
