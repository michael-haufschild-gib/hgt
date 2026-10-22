import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMModularBallGrowth
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneStripIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal
namespace RHTower.D4BMModularCore
noncomputable section
set_option autoImplicit false

private def heightDensity (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1/y^2)
private def heightMeasure : Measure ℝ := volume.withDensity heightDensity

private theorem heightDensity_measurable : Measurable heightDensity := by
  unfold heightDensity
  fun_prop

private theorem volume_chart_set (s : Set ℍ) (hs : MeasurableSet s) :
    volume s = heightMeasure.prod volume (stripEquiv '' (UpperHalfPlane.coe '' s)) := by
  rw [heightMeasure, prod_withDensity_left heightDensity_measurable,
    ← Measure.volume_eq_prod, withDensity_apply _
      (stripEquiv.measurableEmbedding.measurableSet_image.mpr
        (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs))]
  rw [← measurePreserving_stripEquiv.setLIntegral_comp_emb
    stripEquiv.measurableEmbedding (fun p : ℝ × ℝ => heightDensity p.1)
    (UpperHalfPlane.coe '' s), UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_congr_fun
    (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs)
  rintro _ ⟨z,hz,rfl⟩
  simp only [stripEquiv_apply, coe_im, heightDensity]
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [NNReal.coe_pow, Real.nnnorm_of_nonneg z.im_pos.le, one_div, inv_pow]

private theorem ball_in_parabolic_region (R : ℝ) :
    stripEquiv '' (UpperHalfPlane.coe '' Metric.closedBall I R) ⊆
      regionBetween (fun y : ℝ => -2 * Real.exp (R/2) * Real.sqrt y)
        (fun y : ℝ => 2 * Real.exp (R/2) * Real.sqrt y) (Ici (Real.exp (-R))) := by
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  change Real.exp (-R) ≤ z.im ∧
    -2 * Real.exp (R/2) * Real.sqrt z.im < z.re ∧
    z.re < 2 * Real.exp (R/2) * Real.sqrt z.im
  have hd : dist z I ≤ R := hz
  have hl : Real.exp (-R) ≤ z.im := by
    have h := im_div_exp_dist_le I z
    simp only [I_im, dist_comm I z] at h
    calc
      _ = 1 / Real.exp R := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / Real.exp (dist z I) := by gcongr
      _ ≤ z.im := h
  have hc := cosh_dist' z I
  simp only [I_re, I_im, sub_zero, one_pow, mul_one] at hc
  have he : Real.cosh (dist z I) ≤ Real.exp R := by
    have hc := Real.cosh_add_sinh (dist z I)
    have hs := Real.sinh_nonneg_iff.mpr (dist_nonneg (x := z) (y := I))
    exact (by linarith : Real.cosh (dist z I) ≤ Real.exp (dist z I)).trans
      (Real.exp_le_exp.mpr hd)
  have hn : z.re^2 ≤ 2 * Real.exp R * z.im := by
    have h := (div_le_iff₀ (by positivity : 0 < 2*z.im)).mp (hc ▸ he)
    nlinarith [sq_nonneg z.im]
  have hp : (Real.exp (R/2))^2 = Real.exp R := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hy := Real.sq_sqrt z.im_pos.le
  have hpos := mul_pos (Real.exp_pos (R/2)) (Real.sqrt_pos.mpr z.im_pos)
  have hs : (Real.exp (R/2) * Real.sqrt z.im)^2 = Real.exp R * z.im := by
    rw [mul_pow,hp,hy]
  refine ⟨hl, ?_, ?_⟩ <;> nlinarith [sq_nonneg (z.re + 2*(Real.exp (R/2)*Real.sqrt z.im)),
    sq_nonneg (z.re - 2*(Real.exp (R/2)*Real.sqrt z.im))]

private theorem parabolic_region_volume (R : ℝ) :
    heightMeasure.prod volume
      (regionBetween (fun y : ℝ => -2 * Real.exp (R/2) * Real.sqrt y)
        (fun y : ℝ => 2 * Real.exp (R/2) * Real.sqrt y) (Ici (Real.exp (-R)))) =
      ENNReal.ofReal (8 * Real.exp R) := by
  rw [volume_regionBetween_eq_lintegral' (by fun_prop) (by fun_prop) measurableSet_Ici]
  rw [heightMeasure, setLIntegral_withDensity_eq_setLIntegral_mul _ heightDensity_measurable
    (by fun_prop) measurableSet_Ici]
  have hp (y : ℝ) (hy : y ∈ Ici (Real.exp (-R))) :
      heightDensity y * ENNReal.ofReal
        ((fun y : ℝ => 2 * Real.exp (R/2) * Real.sqrt y) y -
          (fun y : ℝ => -2 * Real.exp (R/2) * Real.sqrt y) y) =
      ENNReal.ofReal (4 * Real.exp (R/2) * y^(-(3/2:ℝ))) := by
    have hy0 : 0 < y := (Real.exp_pos _).trans_le hy
    have he : y^(-(3/2:ℝ)) = Real.sqrt y / y^2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hy0]
      congr 1
      ring
    rw [heightDensity, ← ENNReal.ofReal_mul (by positivity), he]
    congr 1
    ring
  simp only [Pi.mul_apply, Pi.sub_apply]
  rw [setLIntegral_congr_fun measurableSet_Ici hp]
  have hi : IntegrableOn (fun y : ℝ => 4 * Real.exp (R/2) * y^(-(3/2:ℝ)))
      (Ici (Real.exp (-R))) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1)
      (Real.exp_pos _)).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      have hy0 : 0 ≤ y := (Real.exp_pos _).le.trans hy
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hy0 _))]
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num : -(3/2:ℝ) < -1) (Real.exp_pos _)]
  have hpow : (Real.exp (-R))^(-(3/2:ℝ)+1) = Real.exp (R/2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hprod : Real.exp (R/2) * Real.exp (R/2) = Real.exp R := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hpow]
  congr 1
  norm_num
  nlinarith [hprod]

/-- Quantitative area control in the actual hyperbolic volume. -/
theorem hyperbolic_ball_volume_le (R : ℝ) :
    volume (Metric.closedBall I R) ≤ ENNReal.ofReal (8 * Real.exp R) := by
  rw [volume_chart_set _ measurableSet_closedBall, ← parabolic_region_volume R]
  exact measure_mono (ball_in_parabolic_region R)

/-- Real-valued form used in absolute source estimates. -/
theorem hyperbolic_ball_real_volume_le (R : ℝ) :
    volume.real (Metric.closedBall I R) ≤ 8 * Real.exp R := by
  have h := ENNReal.toReal_mono (by finiteness) (hyperbolic_ball_volume_le R)
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ 8 * Real.exp R)] using h

/-- Shell admission uses the actual ball mass and retains absolute values before summation. -/
theorem radial_weight_integrable_of_ball_bound (f : ℍ → ℂ) (hf : Continuous f)
    (C a p : ℝ) (ha : 0 ≤ a) (hp : a < p)
    (hb : ∀ R : ℝ, 0 ≤ R → (∫ z : ℍ in Metric.closedBall I R, ‖f z‖) ≤ C * Real.exp (a*R)) :
    Integrable (fun z : ℍ => Real.exp (-p * dist z I) * ‖f z‖) := by
  have hp0 : 0 < p := ha.trans_lt hp
  let S : ℕ → Set ℍ := fun n => {z | (n:ℝ) ≤ dist z I ∧ dist z I ≤ n+1}
  have hK (n : ℕ) : IsCompact (S n) := by
    apply (isCompact_closedBall I (n+1)).of_isClosed_subset
    · exact (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
        (isClosed_le (continuous_id.dist continuous_const) continuous_const)
    · exact fun z hz => hz.2
  let g : ℍ → ℝ := fun z => Real.exp (-p * dist z I) * ‖f z‖
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hi (n : ℕ) : IntegrableOn g (S n) := hg.continuousOn.integrableOn_compact (hK n)
  have hcover : ⋃ n : ℕ, S n = univ := by
    apply Set.eq_univ_of_forall
    intro z
    apply mem_iUnion.mpr
    exact ⟨⌊dist z I⌋₊, Nat.floor_le dist_nonneg, (Nat.lt_floor_add_one _).le⟩
  have hbound (n : ℕ) : (∫ z : ℍ in S n, ‖g z‖) ≤
      C * Real.exp a * Real.exp ((n:ℝ)*(a-p)) := by
    have hsub : S n ⊆ Metric.closedBall I (n+1) := fun z hz => hz.2
    have hfi : IntegrableOn (fun z => ‖f z‖) (Metric.closedBall I (n+1)) :=
      hf.norm.continuousOn.integrableOn_compact (isCompact_closedBall I _)
    calc
      _ ≤ ∫ z : ℍ in S n, Real.exp (-p*(n:ℝ)) * ‖f z‖ := by
        apply setIntegral_mono_on (hi n).norm ((hfi.mono_set hsub).const_mul _) (hK n).measurableSet
        intro z hz
        dsimp only [g]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz.1 (neg_nonpos.mpr hp0.le)))
          (norm_nonneg (f z))
      _ = Real.exp (-p*(n:ℝ)) * ∫ z : ℍ in S n, ‖f z‖ := integral_const_mul _ _
      _ ≤ Real.exp (-p*(n:ℝ)) * ∫ z : ℍ in Metric.closedBall I (n+1), ‖f z‖ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact setIntegral_mono_set hfi (Eventually.of_forall (fun z => norm_nonneg (f z)))
          (Eventually.of_forall hsub)
      _ ≤ Real.exp (-p*(n:ℝ)) * (C * Real.exp (a*((n:ℝ)+1))) :=
        mul_le_mul_of_nonneg_left (hb _ (by positivity)) (Real.exp_pos _).le
      _ = _ := by
        rw [show a*((n:ℝ)+1) = a+(n:ℝ)*a by ring, Real.exp_add]
        rw [show (n:ℝ)*(a-p) = -p*(n:ℝ)+(n:ℝ)*a by ring, Real.exp_add]
        ring
  have hs : Summable (fun n : ℕ => ∫ z : ℍ in S n, ‖g z‖) :=
    ((Real.summable_exp_nat_mul_iff.mpr (sub_neg.mpr hp)).mul_left (C*Real.exp a)).of_nonneg_of_le
      (fun n => integral_nonneg (fun z => norm_nonneg (g z))) hbound
  have h := integrableOn_iUnion_of_summable_integral_norm hi hs
  simpa only [hcover, integrableOn_univ] using h

private theorem integral_norm_balance (f : ℍ → ℂ) (hf : Continuous f) (R t : ℝ)
    (ht : 0 < t) :
    (∫ z : ℍ in Metric.closedBall I R, ‖f z‖) ≤
      ((∫ z : ℍ in Metric.closedBall I R, ‖f z‖^2)/t +
        t * volume.real (Metric.closedBall I R))/2 := by
  letI : IsFiniteMeasure ((volume : Measure ℍ).restrict (Metric.closedBall I R)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_closedBall I R).measure_lt_top⟩
  have h1 : IntegrableOn (fun z => ‖f z‖) (Metric.closedBall I R) :=
    hf.norm.continuousOn.integrableOn_compact (isCompact_closedBall I R)
  have h2 : IntegrableOn (fun z => ‖f z‖^2) (Metric.closedBall I R) :=
    (hf.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall I R)
  have hb : (∫ z : ℍ in Metric.closedBall I R, ‖f z‖) ≤
      ∫ z : ℍ in Metric.closedBall I R, (‖f z‖^2/t+t)/2 := by
    apply integral_mono h1 (((h2.div_const t).add (integrable_const t)).div_const 2)
    intro z
    change ‖f z‖ ≤ (‖f z‖^2/t+t)/2
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (mul_le_mul_iff_right₀ ht).mp
    have he : (‖f z‖^2/t)*t = ‖f z‖^2 := div_mul_cancel₀ _ ht.ne'
    nlinarith [sq_nonneg (‖f z‖-t)]
  convert hb using 1
  rw [integral_div, integral_add (h2.div_const t) (integrable_const t),
    integral_div, setIntegral_const]
  simp only [smul_eq_mul]
  ring

/-- The actual full-forcing response has absolute ball growth strictly below the physical kernel exponent. -/
theorem globalResponse_ball_norm_growth (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (∫ z : ℍ in Metric.closedBall I R, ‖globalResponse q branch z‖) ≤
        C * Real.exp ((5/2:ℝ)*R) := by
  let M := ∫ z : ℍ, ‖cellExtension (embedding (weakResponse q branch)) z‖^2
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  refine ⟨(7^4*M+8)/2, by positivity, ?_⟩
  intro R hR
  have h := integral_norm_balance (globalResponse q branch)
    (ChartSmooth.continuous (globalResponse_smooth q branch)) R
    (Real.exp (3*R/2)) (Real.exp_pos _)
  have h2 := globalResponse_ball_square_bound q branch R hR
  have hvol := hyperbolic_ball_real_volume_le R
  have he1 : (Real.exp R)^4 / Real.exp (3*R/2) = Real.exp ((5/2:ℝ)*R) := by
    rw [← Real.exp_nat_mul, ← Real.exp_sub]
    congr 1
    ring
  have he2 : Real.exp (3*R/2) * Real.exp R = Real.exp ((5/2:ℝ)*R) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ((∫ z : ℍ in Metric.closedBall I R, ‖globalResponse q branch z‖^2) /
        Real.exp (3*R/2) + Real.exp (3*R/2) * volume.real (Metric.closedBall I R))/2 := h
    _ ≤ (((7*Real.exp R)^4*M)/Real.exp (3*R/2) + Real.exp (3*R/2)*(8*Real.exp R))/2 := by
      gcongr
    _ = (7^4*M*((Real.exp R)^4/Real.exp (3*R/2)) +
        8*(Real.exp (3*R/2)*Real.exp R))/2 := by ring
    _ = _ := by rw [he1,he2]; ring

/-- Absolute exponential radial admission of the actual smooth response, with its native L2 input discharged. -/
theorem globalResponse_radial_weight_integrable (q : XiZeroCopy) (branch : Bool)
    (p : ℝ) (hp : (5/2:ℝ) < p) :
    Integrable (fun z : ℍ => Real.exp (-p*dist z I) * ‖globalResponse q branch z‖) := by
  obtain ⟨C,_,hC⟩ := globalResponse_ball_norm_growth q branch
  exact radial_weight_integrable_of_ball_bound _
    (ChartSmooth.continuous (globalResponse_smooth q branch)) C (5/2) p (by norm_num) hp hC

end
end RHTower.D4BMModularCore
