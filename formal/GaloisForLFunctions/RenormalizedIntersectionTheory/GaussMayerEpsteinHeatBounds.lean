import GaloisForLFunctions.LatticeSectionTheory.TheRectangularLatticeCount

/-! Uniform bounds for the two Gaussian tails defining the rectangular
Epstein field. The slow dual tail is controlled by one convergent scalar
theta Mellin integral; its height dependence is explicit. -/

open Complex Real Set MeasureTheory
open GaloisForLFunctions.ArithmeticOrientationGeometry
open GaloisForLFunctions.LatticeSectionTheory
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeatBounds

private def thetaTail (t : ℝ) : ℝ := thetaSum t-1

private theorem thetaTail_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ thetaTail t :=
  sub_nonneg.mpr (one_le_thetaSum ht)

private theorem theta_scaled_le {y t : ℝ} (hy : 1 ≤ y) (ht : 1 ≤ t) :
    thetaSum (t/y^2) ≤ y*thetaSum 1 := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hy2 : 0 < y^2 := sq_pos_of_pos hy0
  have hy21 : 1 ≤ y^2 := by nlinarith only [hy,sq_nonneg (y-1)]
  have harg : 1/y^2 ≤ t/y^2 := div_le_div_of_nonneg_right ht hy2.le
  have hmono := thetaSum_antitone (div_pos zero_lt_one hy2) harg
  have he : thetaSum (1/y^2)=y*thetaSum (y^2) := by
    rw [thetaSum_inv (div_pos zero_lt_one hy2),← Real.sqrt_eq_rpow,one_div,
      Real.sqrt_inv,Real.sqrt_sq hy0.le,inv_inv,inv_inv]
  rw [he] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (thetaSum_antitone zero_lt_one hy21) hy0.le)

private theorem rectTheta_tail_le {y t : ℝ} (hy : 1 ≤ y) (ht : 0 < t) :
    rectTheta y t-1 ≤ rectTheta 1 t-1 := by
  have hy2 : 1 ≤ y^2 := by nlinarith only [hy,sq_nonneg (y-1)]
  have harg : t ≤ y^2*t := by nlinarith only [hy2,ht]
  have h := mul_le_mul_of_nonneg_left (thetaSum_antitone ht harg) (thetaSum_pos ht).le
  simpa only [rectTheta,one_pow,one_mul,sub_le_sub_iff_right] using h

private theorem theta_weight_integrable {η : ℝ} (hη : η < 1) :
    IntegrableOn (fun t : ℝ => t^(-η/2)*thetaTail t) (Ioi 0) := by
  have hs : (1/2 : ℝ) < (((1-η/2 : ℝ) : ℂ)).re := by simp only [Complex.ofReal_re]; linarith
  have h := ((HurwitzZeta.hurwitzEvenFEPair 0).hasMellin hs).1
  have hr := h.re
  refine MeasureTheory.IntegrableOn.congr_fun hr ?_ measurableSet_Ioi
  intro t ht
  simp only [HurwitzZeta.hurwitzEvenFEPair,Function.comp_apply,
    smul_eq_mul,RCLike.re_to_complex]
  change (((t : ℂ)^(((1-η/2 : ℝ) : ℂ)-1))*
    ((HurwitzZeta.evenKernel 0 t : ℂ)-1)).re=_
  rw [show (((1-η/2 : ℝ) : ℂ)-1)=((-η/2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow ht.le,← thetaSum_eq_evenKernel ht]
  simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.one_re,
    Complex.ofReal_im,zero_mul,sub_zero,thetaTail]

/-- The scalar theta moment controlling the slow dual heat tail; finite for `η<1`. -/
def thetaMoment (η : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t^(-η/2)*thetaTail t

private theorem scaled_weight_identity {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (η : ℝ) :
    (y^2*t)^(-η/2)*thetaTail ((y^2*t)/y^2)=
      (y^2)^(-η/2)*(t^(-η/2)*thetaTail t) := by
  rw [mul_div_cancel_left₀ t (pow_ne_zero 2 hy.ne'),Real.mul_rpow (sq_nonneg y) ht.le]
  ring

private theorem theta_scaled_weight_integrable {η y : ℝ} (hη : η < 1) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t^(-η/2)*thetaTail (t/y^2)) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ =>
      (y^2*t)^(-η/2)*thetaTail ((y^2*t)/y^2)) (Ioi 0) := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((theta_weight_integrable hη).const_mul ((y^2)^(-η/2))) ?_ measurableSet_Ioi
    intro t ht
    exact (scaled_weight_identity hy ht η).symm
  have hi := (integrableOn_Ioi_comp_mul_left_iff
    (fun t : ℝ => t^(-η/2)*thetaTail (t/y^2)) 0 (sq_pos_of_pos hy)).mp h
  simpa only [mul_zero] using hi

private theorem theta_scaled_weight_integral {η y : ℝ} (hy : 0 < y) :
    (∫ t in Ioi (0 : ℝ), t^(-η/2)*thetaTail (t/y^2))=y^(2-η)*thetaMoment η := by
  have h := integral_comp_mul_left_Ioi
    (fun t : ℝ => t^(-η/2)*thetaTail (t/y^2)) 0 (sq_pos_of_pos hy)
  simp only [mul_zero,smul_eq_mul] at h
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => scaled_weight_identity hy ht η),
    integral_const_mul] at h
  have he : y^2*(y^2)^(-η/2)=y^(2-η) := by
    have hs : y^(2 : ℝ)=y^2 := Real.rpow_natCast y 2
    calc
      _ = y^(2 : ℝ)*y^((2 : ℝ)*(-η/2)) := by rw [Real.rpow_mul hy.le,hs]
      _ = y^((2 : ℝ)+2*(-η/2)) := (Real.rpow_add hy 2 (2*(-η/2))).symm
      _ = _ := by congr 1; ring
  calc
    _ = y^2*((y^2)^(-η/2)*thetaMoment η) := by
      rw [thetaMoment,h]
      field_simp [pow_ne_zero 2 hy.ne']
    _ = _ := by rw [← mul_assoc,he]

private theorem continuousOn_theta_weight (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => t^(-σ/2)*thetaTail (t/y^2)) (Ioi 0) := by
  have hpow : ContinuousOn (fun t : ℝ => t^(-σ/2)) (Ioi 0) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).continuousWithinAt
  have htheta : ContinuousOn (fun t : ℝ => thetaSum (t/y^2)) (Ioi 0) :=
    continuousOn_thetaSum.comp (continuous_id.div_const (y^2)).continuousOn
      (fun t ht => div_pos ht (sq_pos_of_pos hy))
  exact hpow.mul (htheta.sub continuousOn_const)

private theorem theta_weight_le {η σ y t : ℝ} (hση : η ≤ σ) (hy : 0 < y) (ht : 1 ≤ t) :
    t^(-σ/2)*thetaTail (t/y^2) ≤ t^(-η/2)*thetaTail (t/y^2) := by
  have hn := thetaTail_nonneg (div_pos (zero_lt_one.trans_le ht) (sq_pos_of_pos hy))
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le ht (by linarith only [hση])) hn

private theorem dual_slow_integrable {η σ y : ℝ} (hη : η < 1) (hση : η ≤ σ) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t^(-σ/2)*thetaTail (t/y^2)) (Ioi 1) := by
  have hi := (theta_scaled_weight_integrable hη hy).mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  have hm := ((continuousOn_theta_weight σ hy).mono
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  refine hi.mono' hm ?_
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  have hn : 0 ≤ t^(-σ/2)*thetaTail (t/y^2) := mul_nonneg
    (Real.rpow_nonneg (zero_lt_one.trans ht).le _) (thetaTail_nonneg
      (div_pos (zero_lt_one.trans ht) (sq_pos_of_pos hy)))
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact theta_weight_le hση hy ht.le

private theorem dual_slow_bound {η σ y : ℝ} (hη : η < 1) (hση : η ≤ σ) (hy : 0 < y) :
    y⁻¹*(∫ t in Ioi (1 : ℝ), t^(-σ/2)*thetaTail (t/y^2)) ≤
      y^(1-η)*thetaMoment η := by
  have hηI := theta_scaled_weight_integrable hη hy
  have hηI1 := hηI.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  have hsI := dual_slow_integrable hη hση hy
  have hfirst : (∫ t in Ioi (1 : ℝ), t^(-σ/2)*thetaTail (t/y^2)) ≤
      ∫ t in Ioi (1 : ℝ), t^(-η/2)*thetaTail (t/y^2) := by
    apply integral_mono_ae hsI hηI1
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with t ht
    exact theta_weight_le hση hy ht.le
  have hsecond : (∫ t in Ioi (1 : ℝ), t^(-η/2)*thetaTail (t/y^2)) ≤
      ∫ t in Ioi (0 : ℝ), t^(-η/2)*thetaTail (t/y^2) := by
    apply setIntegral_mono_set hηI
    · apply (ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (thetaTail_nonneg
        (div_pos ht (sq_pos_of_pos hy)))
    · exact Filter.Eventually.of_forall (fun t ht => zero_lt_one.trans ht)
  have he : y⁻¹*y^(2-η)=y^(1-η) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hy]
    congr 1
    ring
  calc
    _ ≤ y⁻¹*(∫ t in Ioi (0 : ℝ), t^(-η/2)*thetaTail (t/y^2)) :=
      mul_le_mul_of_nonneg_left (hfirst.trans hsecond) (inv_pos.mpr hy).le
    _ = _ := by rw [theta_scaled_weight_integral hy,← mul_assoc,he]

private theorem theta_tail_integrable : IntegrableOn thetaTail (Ioi 0) := by
  simpa only [neg_zero,zero_div,Real.rpow_zero,one_mul] using
    theta_weight_integrable (η := 0) (by norm_num)

private theorem dual_heat_split {y : ℝ} (hy : 0 < y) (t : ℝ) :
    rectTheta (1/y) t-1=thetaTail t*thetaSum (t/y^2)+thetaTail (t/y^2) := by
  have he : (1/y)^2*t=t/y^2 := by field_simp [hy.ne']
  rw [rectTheta,he,thetaTail,thetaTail]
  ring

/-- The real norm weight in the dual Gaussian tail of the Epstein continuation. -/
def dualHeatWeight (σ y t : ℝ) : ℝ :=
  y⁻¹*t^(-σ/2)*(rectTheta (1/y) t-1)

private theorem dual_heat_nonneg {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (σ : ℝ) :
    0 ≤ dualHeatWeight σ y t :=
  mul_nonneg (mul_nonneg (inv_pos.mpr hy).le (Real.rpow_nonneg ht.le _))
    (sub_nonneg.mpr (one_le_rectTheta (one_div_pos.mpr hy).ne' ht))

private theorem dual_heat_majorant {η σ y t : ℝ} (hη : 0 < η) (hση : η ≤ σ)
    (hy : 1 ≤ y) (ht : 1 ≤ t) :
    dualHeatWeight σ y t ≤ thetaSum 1*thetaTail t+
      y⁻¹*(t^(-η/2)*thetaTail (t/y^2)) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp : t^(-σ/2) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le ht
      (by linarith only [hη,hση] : -σ/2 ≤ 0)
    simpa only [Real.rpow_zero] using h
  have hb : y⁻¹*thetaSum (t/y^2) ≤ thetaSum 1 := by
    calc
      _ ≤ y⁻¹*(y*thetaSum 1) :=
        mul_le_mul_of_nonneg_left (theta_scaled_le hy ht) (inv_pos.mpr hy0).le
      _ = _ := by rw [inv_mul_cancel_left₀ hy0.ne']
  have hf : t^(-σ/2)*(y⁻¹*thetaSum (t/y^2)) ≤ thetaSum 1 := by
    have hn : 0 ≤ y⁻¹*thetaSum (t/y^2) := mul_nonneg (inv_pos.mpr hy0).le
      (thetaSum_pos (div_pos ht0 (sq_pos_of_pos hy0))).le
    exact (mul_le_of_le_one_left hn hp).trans hb
  have hfast : y⁻¹*t^(-σ/2)*(thetaTail t*thetaSum (t/y^2)) ≤ thetaSum 1*thetaTail t := by
    calc
      _ = (t^(-σ/2)*(y⁻¹*thetaSum (t/y^2)))*thetaTail t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hf (thetaTail_nonneg ht0)
  have hslow := mul_le_mul_of_nonneg_left (theta_weight_le hση hy0 ht) (inv_pos.mpr hy0).le
  rw [dualHeatWeight,dual_heat_split hy0,mul_add]
  exact add_le_add hfast (by simpa only [mul_assoc] using hslow)

private theorem continuousOn_dualHeatWeight (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (dualHeatWeight σ y) (Ioi 0) := by
  have hp : ContinuousOn (fun t : ℝ => t^(-σ/2)) (Ioi 0) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).continuousWithinAt
  exact (continuousOn_const.mul hp).mul
    ((continuousOn_rectTheta (one_div_pos.mpr hy).ne').sub continuousOn_const)

/-- The dual Gaussian tail is absolutely integrable, uniformly under a smaller positive exponent. -/
theorem dualHeatWeight_integrable {η σ y : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hση : η ≤ σ) (hy : 1 ≤ y) : IntegrableOn (dualHeatWeight σ y) (Ioi 1) := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have h0 := (theta_tail_integrable.mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul (thetaSum 1)
  have h1 := ((theta_scaled_weight_integrable hη1 hy0).mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul y⁻¹
  have hU : IntegrableOn (fun t : ℝ => thetaSum 1*thetaTail t+
      y⁻¹*(t^(-η/2)*thetaTail (t/y^2))) (Ioi 1) := h0.add h1
  have hm := ((continuousOn_dualHeatWeight σ hy0).mono
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  refine hU.mono' hm ?_
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (dual_heat_nonneg hy0 (zero_lt_one.trans ht) σ)]
  exact dual_heat_majorant hη0 hση hy ht.le

/-- The dual heat tail grows at most as `y^(1-η)` for positive spectral real part. -/
theorem dualHeatWeight_integral_le {η σ y : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hση : η ≤ σ) (hy : 1 ≤ y) :
    (∫ t in Ioi (1 : ℝ), dualHeatWeight σ y t) ≤
      thetaSum 1*thetaMoment 0+y^(1-η)*thetaMoment η := by
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have h0 := (theta_tail_integrable.mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul (thetaSum 1)
  have h1 := ((theta_scaled_weight_integrable hη1 hy0).mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul y⁻¹
  have hU : IntegrableOn (fun t : ℝ => thetaSum 1*thetaTail t+
      y⁻¹*(t^(-η/2)*thetaTail (t/y^2))) (Ioi 1) := h0.add h1
  have hb : (∫ t in Ioi (1 : ℝ), thetaTail t) ≤ thetaMoment 0 := by
    have h : (∫ t in Ioi (1 : ℝ), thetaTail t) ≤ ∫ t in Ioi (0 : ℝ), thetaTail t := by
      apply setIntegral_mono_set theta_tail_integrable
      · apply (ae_restrict_iff' measurableSet_Ioi).mpr
        filter_upwards with t ht
        exact thetaTail_nonneg ht
      · exact Filter.Eventually.of_forall (fun t ht => zero_lt_one.trans ht)
    simpa only [thetaMoment,neg_zero,zero_div,Real.rpow_zero,one_mul] using h
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), thetaSum 1*thetaTail t+
        y⁻¹*(t^(-η/2)*thetaTail (t/y^2)) := by
      apply integral_mono_ae (dualHeatWeight_integrable hη0 hη1 hση hy) hU
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t ht
      exact dual_heat_majorant hη0 hση hy ht.le
    _ = thetaSum 1*(∫ t in Ioi (1 : ℝ), thetaTail t)+
        y⁻¹*(∫ t in Ioi (1 : ℝ), t^(-η/2)*thetaTail (t/y^2)) := by
      rw [integral_add h0 h1,integral_const_mul,integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (thetaSum_pos zero_lt_one).le)
      (dual_slow_bound hη1 le_rfl hy0)

private theorem rectTheta_scalar_majorant {y t : ℝ} (hy : 1 ≤ y) (ht : 1 ≤ t) :
    rectTheta y t-1 ≤ (thetaSum 1+1)*thetaTail t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  calc
    _ ≤ rectTheta 1 t-1 := rectTheta_tail_le hy ht0
    _ = (thetaSum t+1)*thetaTail t := by simp only [rectTheta,one_pow,one_mul,thetaTail]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by linarith only [thetaSum_antitone zero_lt_one ht] : thetaSum t+1 ≤ thetaSum 1+1)
      (thetaTail_nonneg ht0)

/-- The real norm weight in the original Gaussian tail of the Epstein continuation. -/
def originalHeatWeight (σ y t : ℝ) : ℝ :=
  t^(σ/2-1)*(rectTheta y t-1)

private theorem original_heat_nonneg {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (σ : ℝ) :
    0 ≤ originalHeatWeight σ y t :=
  mul_nonneg (Real.rpow_nonneg ht.le _) (sub_nonneg.mpr (one_le_rectTheta hy.ne' ht))

private theorem original_heat_majorant {σ β y t : ℝ} (hσβ : σ ≤ β) (hy : 1 ≤ y) (ht : 1 ≤ t) :
    originalHeatWeight σ y t ≤ (thetaSum 1+1)*(t^(β/2-1)*thetaTail t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hp := Real.rpow_le_rpow_of_exponent_le ht (by linarith only [hσβ] : σ/2-1 ≤ β/2-1)
  unfold originalHeatWeight
  calc
    _ ≤ t^(β/2-1)*((thetaSum 1+1)*thetaTail t) :=
      mul_le_mul hp (rectTheta_scalar_majorant hy ht)
        (sub_nonneg.mpr (one_le_rectTheta hy0.ne' ht0)) (Real.rpow_nonneg ht0.le _)
    _ = _ := by ring

private theorem original_majorant_integrable {β : ℝ} (hβ : 1 < β) :
    IntegrableOn (fun t : ℝ => t^(β/2-1)*thetaTail t) (Ioi 0) := by
  have h := theta_weight_integrable (η := 2-β) (by linarith only [hβ])
  simpa only [show -(2-β)/2=β/2-1 by ring] using h

private theorem continuousOn_originalHeatWeight (σ : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (originalHeatWeight σ y) (Ioi 0) := by
  have hp : ContinuousOn (fun t : ℝ => t^(σ/2-1)) (Ioi 0) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl ht.ne')).continuousWithinAt
  exact hp.mul ((continuousOn_rectTheta hy.ne').sub continuousOn_const)

/-- The original Gaussian tail is absolutely integrable under any larger exponent above one. -/
theorem originalHeatWeight_integrable {σ β y : ℝ} (hβ : 1 < β) (hσβ : σ ≤ β) (hy : 1 ≤ y) :
    IntegrableOn (originalHeatWeight σ y) (Ioi 1) := by
  have hi := ((original_majorant_integrable hβ).mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul (thetaSum 1+1)
  have hm := ((continuousOn_originalHeatWeight σ (zero_lt_one.trans_le hy)).mono
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  refine hi.mono' hm ?_
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (original_heat_nonneg (zero_lt_one.trans_le hy)
    (zero_lt_one.trans ht) σ)]
  exact original_heat_majorant hσβ hy ht.le

/-- The original heat tail is bounded independently of the height `y≥1`. -/
theorem originalHeatWeight_integral_le {σ β y : ℝ} (hβ : 1 < β) (hσβ : σ ≤ β) (hy : 1 ≤ y) :
    (∫ t in Ioi (1 : ℝ), originalHeatWeight σ y t) ≤
      (thetaSum 1+1)*thetaMoment (2-β) := by
  have hbase := original_majorant_integrable hβ
  have hi := (hbase.mono_set (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))).const_mul (thetaSum 1+1)
  have hb : (∫ t in Ioi (1 : ℝ), t^(β/2-1)*thetaTail t) ≤ thetaMoment (2-β) := by
    have h : (∫ t in Ioi (1 : ℝ), t^(β/2-1)*thetaTail t) ≤
        ∫ t in Ioi (0 : ℝ), t^(β/2-1)*thetaTail t := by
      apply setIntegral_mono_set hbase
      · apply (ae_restrict_iff' measurableSet_Ioi).mpr
        filter_upwards with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (thetaTail_nonneg ht)
      · exact Filter.Eventually.of_forall (fun t ht => zero_lt_one.trans ht)
    simpa only [thetaMoment,show -(2-β)/2=β/2-1 by ring] using h
  calc
    _ ≤ ∫ t in Ioi (1 : ℝ), (thetaSum 1+1)*(t^(β/2-1)*thetaTail t) := by
      apply integral_mono_ae (originalHeatWeight_integrable hβ hσβ hy) hi
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t ht
      exact original_heat_majorant hσβ hy ht.le
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hb (by linarith only [thetaSum_pos zero_lt_one])

/-- Scalar theta moments are nonnegative. -/
theorem thetaMoment_nonneg (η : ℝ) : 0 ≤ thetaMoment η := by
  apply integral_nonneg_of_ae
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  exact mul_nonneg (Real.rpow_nonneg ht.le _) (thetaTail_nonneg ht)

#print axioms originalHeatWeight_integrable
#print axioms originalHeatWeight_integral_le
#print axioms thetaMoment_nonneg

#print axioms theta_scaled_le
#print axioms rectTheta_tail_le
#print axioms theta_weight_integrable
#print axioms theta_scaled_weight_integrable
#print axioms theta_scaled_weight_integral
#print axioms dual_slow_integrable
#print axioms dual_slow_bound
#print axioms dualHeatWeight_integrable
#print axioms dualHeatWeight_integral_le
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerEpsteinHeatBounds
