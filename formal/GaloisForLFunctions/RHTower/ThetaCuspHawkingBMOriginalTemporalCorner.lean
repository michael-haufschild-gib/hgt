import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCornerCurrentAdmission
import GaloisForLFunctions.HTGeometry.TriangularIntervalFubini
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The original causal triangle retains the horizon current's first temporal moment.

The unchanged horizon trace and forcing supply all moment admission and both endpoint
limits. Half-line integration by parts identifies the temporal corner with the existing
meromorphic candidate on the original convergence chamber. The original radial coordinate
fixes its log-two normalization. No numerical evidence or assumed horizon admission is used.

This closes the leading scalar-horizon comparison. Identification with the complete original
angular/metric boundary integral, and continuation of that assembled action to a QNM,
remain separate obligations; no full matching or RH conclusion is asserted.
-/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalTemporalCorner
open D4BMJointSource D4BMModularCore D4BMOriginalCausalAdmission
open D4BMOriginalHorizonTimeTrace D4BMOriginalCharacteristicTransform
open D4BMOriginalCollarCurrentBounds D4BMOriginalCornerCurrentAdmission
open D4BMOriginalCornerForcing D4BMOriginalHorizonGreenMatch D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace

private theorem reader_re (q : XiZeroCopy) :
    0 ≤ (D4BMOriginalCirclePeriod.readerExponent q).re := by
  have hr := (xi_divisor_support_re_mem_open_unit q.1).2
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

private theorem moment_of_bound (f : ℝ → ℂ) (w : ℂ) (G B : ℝ) (n : ℕ)
    (hw : G < w.re) (hm : AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))))
    (hb : ∀ p : ℝ, 0 < p → ‖f p‖ ≤ B*Real.exp (G*p)) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*f p) (Ioi 0) := by
  have hn : (-1:ℝ) < (n:ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) hn (by norm_num) (sub_pos.mpr hw)
  have hmajor : IntegrableOn (fun p : ℝ => B*(p^n*Real.exp (-(w.re-G)*p))) (Ioi 0) := by
    simpa only [IntegrableOn,Real.rpow_one,Real.rpow_natCast] using h.const_mul B
  apply hmajor.mono' (((show Continuous (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ)))
    by fun_prop).aestronglyMeasurable).mul hm)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have he : ‖Complex.exp (-w*(p:ℂ))‖ = Real.exp (-w.re*p) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  change ‖(p:ℂ)^n*Complex.exp (-w*(p:ℂ))*f p‖ ≤ _
  rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.le,he]
  calc
    _ ≤ (p^n*Real.exp (-w.re*p))*(B*Real.exp (G*p)) :=
      mul_le_mul_of_nonneg_left (hb p hp) (mul_nonneg (pow_nonneg hp.le n) (Real.exp_nonneg _))
    _ = _ := by
      rw [show -(w.re-G)*p = -w.re*p+G*p by ring,Real.exp_add]
      ring

private theorem horizon_derivative_moment_integrable (q : XiZeroCopy) (br : Bool)
    (amp w : ℂ) (n : ℕ) (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p)
      (Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := original_horizon_value_slope_growth q br amp
  apply moment_of_bound _ w _ B n hw (measurable_deriv _).aestronglyMeasurable
  intro p hp
  rw [(horizon_trace_hasDerivAt q br amp hp).deriv]
  exact (le_add_of_nonneg_left (norm_nonneg (horizonTrace q br amp p))).trans (hb p hp)

/-- The retained horizon density at the unchanged arithmetic, source and radial-reader coefficients.
The full angular/metric attachment is not assumed by this definition. -/
def leadingDensity (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (p : ℝ) : ℂ :=
  let μ := physicalAngularParameter q^2-1/4
  μ*readerTrace w (physicalRadialFrequency q)*Complex.exp (-w*(p:ℂ))*
    ((μ-2)*(deriv (horizonTrace q br amp) p+w*horizonTrace q br amp p)+
      w*physicalSelfSourceCoefficient q*forcingTrace (physicalRate q br) amp 1
        (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)

/-- Every time moment of this actual source/forcing horizon density is integrable on its chamber. -/
theorem leading_moment_integrable (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    IntegrableOn (fun p : ℝ => (p:ℂ)^n*leadingDensity q br amp w p) (Ioi 0) := by
  have hH := horizon_moment_integrable q br amp w n hw
  have hD := horizon_derivative_moment_integrable q br amp w n hw
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hF := forcing_moment_integrable (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w n
    (show (2*physicalRate q br).re < w.re from hs.trans (by linarith [reader_re q]))
  let μ := physicalAngularParameter q^2-1/4
  have h := (((hD.add (hH.const_mul w)).const_mul (μ-2)).add
    (hF.const_mul (w*physicalSelfSourceCoefficient q))).const_mul
      (μ*readerTrace w (physicalRadialFrequency q))
  apply h.congr
  exact ae_of_all _ (fun p => by dsimp [leadingDensity,μ]; ring)

/-- The original static-time triangular domain, with ingoing time `p=t+x`. -/
def temporalTriangle (A : ℝ → ℂ) (T : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..T, ∫ x in (-t)..0, A (t+x)

private theorem triangle_weighted (A : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) :
    temporalTriangle A T = ∫ p in (0:ℝ)..T, ((T-p:ℝ):ℂ)*A p := by
  have hinner (t : ℝ) : (∫ x in (-t)..0, A (t+x)) = ∫ p in (0:ℝ)..t, A p := by
    simpa only [add_neg_cancel,add_zero] using intervalIntegral.integral_comp_add_left A (a:=-t) (b:=0) t
  have h := GaloisForLFunctions.HTGeometry.intervalIntegral_triangle_swap hT hA
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℂ)) volume 0 T)
  simp only [intervalIntegral.integral_const,Complex.real_smul,mul_one] at h
  unfold temporalTriangle
  simp_rw [hinner]
  rw [← h]
  apply intervalIntegral.integral_congr
  intro p hp
  exact mul_comm _ _

private theorem interval_admission {A : ℝ → ℂ} (hA : IntegrableOn A (Ioi (0:ℝ)))
    {T : ℝ} (hT : 0 ≤ T) : IntervalIntegrable A volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (hA.mono_set (fun _ hp => hp.1))

private theorem first_tail_tendsto {A : ℝ → ℂ} (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi 0)) :
    Tendsto (fun T : ℝ => (T:ℂ)*∫ p in Ioi T, A p) atTop (𝓝 (0:ℂ)) := by
  apply squeeze_zero_norm' (a:=fun T : ℝ => ∫ p in Ioi T, ‖(p:ℂ)*A p‖)
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    have hAT := hA.mono_set (Ioi_subset_Ioi hT)
    have hMT := hM.mono_set (Ioi_subset_Ioi hT)
    rw [← integral_const_mul]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae (hAT.const_mul (T:ℂ)).norm hMT.norm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hT,
      abs_of_nonneg (hT.trans hp.le)]
    exact mul_le_mul_of_nonneg_right hp.le (norm_nonneg _)
  · exact tendsto_integral_Ioi_zero tendsto_id

private theorem triangle_defect {A : ℝ → ℂ} (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi 0)) {T : ℝ} (hT : 0 ≤ T) :
    temporalTriangle A T-(T:ℂ)*(∫ p in Ioi (0:ℝ), A p) =
      -(∫ p in (0:ℝ)..T, (p:ℂ)*A p)-(T:ℂ)*(∫ p in Ioi T, A p) := by
  have hAI := interval_admission hA hT
  have hMI := interval_admission hM hT
  rw [triangle_weighted A hT hAI]
  have he (p : ℝ) : ((T-p:ℝ):ℂ)*A p = (T:ℂ)*A p-(p:ℂ)*A p := by push_cast; ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (hAI.const_mul _) hMI,intervalIntegral.integral_const_mul]
  have hs := intervalIntegral.integral_interval_add_Ioi hA (hA.mono_set (Ioi_subset_Ioi hT))
  rw [← hs]
  ring

private theorem triangle_finitePart {A : ℝ → ℂ} (hA : IntegrableOn A (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*A p) (Ioi 0)) :
    Tendsto (fun T : ℝ => temporalTriangle A T-(T:ℂ)*(∫ p in Ioi (0:ℝ), A p)) atTop
      (𝓝 (-(∫ p in Ioi (0:ℝ), (p:ℂ)*A p))) := by
  have h := (intervalIntegral_tendsto_integral_Ioi 0 hM tendsto_id).neg.sub (first_tail_tendsto hA hM)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact (triangle_defect hA hM hT).symm

/-- The causal triangle of the retained physical horizon density has exactly its negative
first temporal moment as finite part. All admission is derived from the actual source. -/
theorem original_leading_triangle_finitePart (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    Tendsto (fun T : ℝ => temporalTriangle (leadingDensity q br amp w) T-
      (T:ℂ)*(∫ p in Ioi (0:ℝ), leadingDensity q br amp w p)) atTop
      (𝓝 (-(∫ p in Ioi (0:ℝ), (p:ℂ)*leadingDensity q br amp w p))) := by
  apply triangle_finitePart
  · simpa only [pow_zero,one_mul] using leading_moment_integrable q br amp w 0 hw
  · simpa only [pow_one] using leading_moment_integrable q br amp w 1 hw

private theorem horizon_zero (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    horizonTrace q br amp 0 = 0 := by
  have hz : reducedTrace q br amp (D4BMOriginalCirclePeriod.readerExponent q) 0 = 0 := by
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with L hL
    simpa only [collarValue,zero_add] using
      (collarValue_zero (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp hL).symm
  simp only [horizonTrace,hz,timeOnset_zero_of_nonpos _ (le_refl 0),mul_zero,add_zero]

private theorem scalar_zero (q : XiZeroCopy) (br : Bool) (amp : ℂ) {L : ℝ} (hL : 0 ≤ L) :
    originalScalar q br amp 0 (0+L) = 0 := by
  rw [original_scalar_on_collar,collarValue_zero _ _ _ hL,timeOnset_zero_of_nonpos _ (le_refl 0)]
  simp

private theorem scalar_time_continuous (q : XiZeroCopy) (br : Bool) (amp : ℂ) (L : ℝ) :
    Continuous (fun p : ℝ => originalScalar q br amp p (p+L)) := by
  have hV : Continuous (fun p : ℝ =>
      collarValue (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp L p) := by
    have h := (D4BMNativeResponse.radialResponse_continuous
      (-D4BMOriginalCirclePeriod.readerExponent q) (physicalRate q br) amp).comp
        (show Continuous (fun p : ℝ => ((p+(p+L))/2,(p-(p+L))/2)) by fun_prop)
    simpa only [collarValue,nullValue,Function.comp_def] using h
  have hO : Continuous (timeOnset (2*physicalRate q br)) :=
    continuous_iff_continuousAt.mpr (fun p => (timeOnset_hasDerivAt _ p).continuousAt)
  simp_rw [original_scalar_on_collar]
  exact (hV.add (hO.const_mul _)).const_mul _

/-- The actual horizon limit is uniform through the original onset endpoint. -/
theorem original_onset_horizon_uniform (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    TendstoUniformlyOn (fun L p : ℝ => originalScalar q br amp p (p+L))
      (horizonTrace q br amp) atTop (Icc (0:ℝ) 1) := by
  obtain ⟨B,hB,hb⟩ := original_collar_value_slope_error q br amp
  let G := (D4BMOriginalCirclePeriod.readerExponent q).re
  have hlim : Tendsto (fun L : ℝ => B*Real.exp (-L)*Real.exp G) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero,zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul B).mul_const (Real.exp G)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb,hlim.eventually (gt_mem_nhds hε),eventually_ge_atTop (0:ℝ)] with L h hsmall hL
  intro p hp
  rcases eq_or_lt_of_le hp.1 with hzero | hpos
  · subst p
    rw [scalar_zero q br amp hL,horizon_zero,dist_self]
    exact hε
  · rw [dist_eq_norm,norm_sub_rev]
    have hv := (le_add_of_nonneg_right
      (norm_nonneg (deriv (fun a => originalScalar q br amp a (a+L)) p-horizonSlope q br amp p))).trans (h p hpos)
    apply hv.trans_lt
    apply lt_of_le_of_lt _ hsmall
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Real.exp_nonneg _))
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (reader_re q) hp.2

/-- No horizon-onset constant is inserted: the actual horizon trace tends to zero. -/
theorem original_horizon_onset_zero (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    Tendsto (horizonTrace q br amp) (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hc := (original_onset_horizon_uniform q br amp).continuousOn
    (Eventually.of_forall (fun L => (scalar_time_continuous q br amp L).continuousOn)).frequently
  have h0 := hc.continuousWithinAt (show (0:ℝ) ∈ Icc 0 1 by simp)
  have hs : Icc (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with p hp hp1
    exact ⟨hp.le,hp1.le⟩
  simpa only [horizon_zero] using (h0.mono_of_mem_nhdsWithin hs).tendsto

private theorem horizon_moment_terminal (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    Tendsto (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      atTop (𝓝 (0:ℂ)) := by
  obtain ⟨B,hB,hb⟩ := original_horizon_value_slope_growth q br amp
  let G := (D4BMOriginalCirclePeriod.readerExponent q).re
  apply squeeze_zero_norm' (a:=fun p : ℝ => B*(p^n*Real.exp (-(w.re-G)*p)))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
    have hv := (le_add_of_nonneg_right (norm_nonneg (horizonSlope q br amp p))).trans (hb p hp)
    have he : ‖Complex.exp (-w*(p:ℂ))‖ = Real.exp (-w.re*p) := by
      rw [Complex.norm_exp]
      congr 1
      simp
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp.le,he]
    calc
      _ ≤ (p^n*Real.exp (-w.re*p))*(B*Real.exp (G*p)) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
      _ = _ := by
        rw [show -(w.re-G)*p = -w.re*p+G*p by ring,Real.exp_add]
        ring
  · simpa only [Real.rpow_natCast,mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n:ℝ) (w.re-G) (sub_pos.mpr hw)).const_mul B

private theorem horizon_moment_onset (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ) :
    Tendsto (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) := by
  have hc : Continuous (fun p : ℝ => (p:ℂ)^n*Complex.exp (-w*(p:ℂ))) := by fun_prop
  have h := (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
    (original_horizon_onset_zero q br amp)
  simpa only [mul_zero] using h

private theorem exp_derivative (w : ℂ) (p : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (-w*(x:ℂ)))
      (-w*Complex.exp (-w*(p:ℂ))) p := by
  apply (((Complex.ofRealCLM.hasDerivAt (x:=p)).const_mul (-w)).cexp).congr_deriv
  change Complex.exp (-w*(p:ℂ))*(-w*1) = -w*Complex.exp (-w*(p:ℂ))
  ring

/-- Integration by parts of the actual horizon trace retains no onset or terminal constant. -/
theorem horizon_derivative_laplace (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    (∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p) =
      w*horizonTransform q br amp w := by
  have hH : IntegrableOn (fun p : ℝ => Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using horizon_moment_integrable q br amp w 0 hw
  have hD : IntegrableOn (fun p : ℝ => Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using horizon_derivative_moment_integrable q br amp w 0 hw
  have h := integral_Ioi_mul_deriv_eq_deriv_mul
    (fun p (_ : p ∈ Ioi (0:ℝ)) => exp_derivative w p)
    (fun p (hp : p ∈ Ioi (0:ℝ)) => (horizon_trace_hasDerivAt q br amp hp).differentiableAt.hasDerivAt)
    hD
    (show IntegrableOn (fun p : ℝ => (-w*Complex.exp (-w*(p:ℂ)))*horizonTrace q br amp p) (Ioi 0) from
      by simpa only [IntegrableOn,mul_assoc] using hH.const_mul (-w))
    (show Tendsto (fun p : ℝ => Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) from by
        simpa only [pow_zero,one_mul] using horizon_moment_onset q br amp w 0)
    (show Tendsto (fun p : ℝ => Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      atTop (𝓝 (0:ℂ)) from by
        simpa only [pow_zero,one_mul] using horizon_moment_terminal q br amp w 0 hw)
  simpa only [mul_assoc,integral_const_mul,integral_neg,sub_zero,zero_sub,neg_mul,neg_neg,horizonTransform] using h

/-- The first time moment of the genuine horizon derivative includes the undifferentiated mass. -/
theorem horizon_derivative_firstMoment (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    (∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p) =
      w*(∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)-
        horizonTransform q br amp w := by
  have hH : IntegrableOn (fun p : ℝ => Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) (Ioi 0) := by
    simpa only [pow_zero,one_mul] using horizon_moment_integrable q br amp w 0 hw
  have hM : IntegrableOn (fun p : ℝ => (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) (Ioi 0) := by
    simpa only [pow_one] using horizon_moment_integrable q br amp w 1 hw
  have hD : IntegrableOn (fun p : ℝ => (p:ℂ)*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p) (Ioi 0) := by
    simpa only [pow_one] using horizon_derivative_moment_integrable q br amp w 1 hw
  let u' := fun p : ℝ => Complex.exp (-w*(p:ℂ))-w*((p:ℂ)*Complex.exp (-w*(p:ℂ)))
  have hu (p : ℝ) (_ : p ∈ Ioi (0:ℝ)) :
      HasDerivAt (fun x : ℝ => (x:ℂ)*Complex.exp (-w*(x:ℂ))) (u' p) p := by
    apply ((Complex.ofRealCLM.hasDerivAt (x:=p)).mul (exp_derivative w p)).congr_deriv
    change _ = Complex.exp (-w*(p:ℂ))-w*((p:ℂ)*Complex.exp (-w*(p:ℂ)))
    simp only [Complex.ofRealCLM_apply,Complex.ofReal_one]
    ring
  have hUv : IntegrableOn (fun p => u' p*horizonTrace q br amp p) (Ioi 0) := by
    apply (hH.sub (hM.const_mul w)).congr
    exact ae_of_all _ (fun p => by dsimp [u']; ring)
  have h := integral_Ioi_mul_deriv_eq_deriv_mul hu
    (fun p (hp : p ∈ Ioi (0:ℝ)) => (horizon_trace_hasDerivAt q br amp hp).differentiableAt.hasDerivAt)
    hD hUv
    (show Tendsto (fun p : ℝ => (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      (𝓝[>] (0:ℝ)) (𝓝 (0:ℂ)) from by
        simpa only [pow_one] using horizon_moment_onset q br amp w 1)
    (show Tendsto (fun p : ℝ => (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)
      atTop (𝓝 (0:ℂ)) from by
        simpa only [pow_one] using horizon_moment_terminal q br amp w 1 hw)
  have hi : (∫ p in Ioi (0:ℝ), u' p*horizonTrace q br amp p) =
      horizonTransform q br amp w-w*(∫ p in Ioi (0:ℝ), (p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) := by
    calc
      _ = ∫ p in Ioi (0:ℝ), Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p-
          w*((p:ℂ)*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => by dsimp [u']; ring)
      _ = _ := by rw [integral_sub hH (hM.const_mul w),integral_const_mul]; rfl
  rw [hi] at h
  linear_combination h

private theorem leading_moment_integral (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (n : ℕ)
    (hw : (D4BMOriginalCirclePeriod.readerExponent q).re < w.re) :
    (∫ p in Ioi (0:ℝ), (p:ℂ)^n*leadingDensity q br amp w p) =
      (physicalAngularParameter q^2-1/4)*readerTrace w (physicalRadialFrequency q)*
        ((physicalAngularParameter q^2-1/4-2)*
          ((∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p)+
            w*(∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p))+
          w*physicalSelfSourceCoefficient q*(∫ p in Ioi (0:ℝ), (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
            forcingTrace (physicalRate q br) amp 1
              (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p)) := by
  have hH := horizon_moment_integrable q br amp w n hw
  have hD := horizon_derivative_moment_integrable q br amp w n hw
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hF := forcing_moment_integrable (physicalRate q br) amp 1
    (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w n
    (show (2*physicalRate q br).re < w.re from hs.trans (by linarith [reader_re q]))
  let μ := physicalAngularParameter q^2-1/4
  have hDH : IntegrableOn (fun p : ℝ =>
      (p:ℂ)^n*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p+
        w*((p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p)) (Ioi 0) := by
    apply (hD.add (hH.const_mul w)).congr
    exact ae_of_all _ (fun _ => rfl)
  calc
    _ = μ*readerTrace w (physicalRadialFrequency q)*
        ∫ p in Ioi (0:ℝ), (μ-2)*
          ((p:ℂ)^n*Complex.exp (-w*(p:ℂ))*deriv (horizonTrace q br amp) p+
            w*((p:ℂ)^n*Complex.exp (-w*(p:ℂ))*horizonTrace q br amp p))+
          w*physicalSelfSourceCoefficient q*((p:ℂ)^n*Complex.exp (-w*(p:ℂ))*
            forcingTrace (physicalRate q br) amp 1
              (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) p) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun p => by dsimp [leadingDensity,μ]; ring)
    _ = _ := by
      rw [integral_add (hDH.const_mul (μ-2))
        (hF.const_mul (w*physicalSelfSourceCoefficient q)),integral_const_mul,
        integral_add hD (hH.const_mul w),integral_const_mul,integral_const_mul]

private theorem chamber_reader (q : XiZeroCopy) (w : ℂ) (hw : 3/2 < w.re) :
    (D4BMOriginalCirclePeriod.readerExponent q).re < w.re := by
  have hq := (xi_divisor_support_re_mem_open_unit q.1).1
  norm_num [D4BMOriginalCirclePeriod.readerExponent]
  linarith

/-- The actual first moment and the prescribed radial normalization equal the existing
meromorphic corner candidate on the original convergence chamber. -/
theorem original_corner_moment_eq_candidate (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    -(∫ p in Ioi (0:ℝ), (p:ℂ)*leadingDensity q br amp w p)-
      (Real.log 2:ℂ)*(∫ p in Ioi (0:ℝ), leadingDensity q br amp w p) =
        physicalCornerCandidate q br amp w := by
  have hwr := chamber_reader q w hw
  have h0 := leading_moment_integral q br amp w 0 hwr
  have h1 := leading_moment_integral q br amp w 1 hwr
  simp only [pow_zero,one_mul] at h0
  simp only [pow_one] at h1
  rw [h0,h1,horizon_derivative_laplace q br amp w hwr,horizon_derivative_firstMoment q br amp w hwr]
  have hs := currentRate_re_lt q br
  change (2*physicalRate q br).re < -2 at hs
  have hforce : (2*physicalRate q br).re < w.re := by linarith
  have hp : power (-w) 2 = Complex.exp (-w*(Real.log 2:ℂ)) := by
    rw [power,Complex.cpow_def_of_ne_zero (by norm_num),← Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [physicalCornerCandidate,continuedCornerAmplitude_eq_original q br amp w hw hwi,cornerAmplitude,
    (continuedCornerAmplitude_original_firstMoment q br amp w hw hwi).deriv,
    (continued_forcing_original_firstMoment (physicalRate q br) amp 1
      (reducedGreenGradient (physicalRadialFrequency q) (physicalRate q br) 1) w hforce).deriv,
    readerTrace,hp]
  unfold horizonTransform
  ring

/-- The actual causal horizon triangle, retaining the fixed log-two normalization, lands
on the meromorphic corner candidate. Complete metric/angular assembly remains separate. -/
theorem original_leading_triangle_eq_candidate (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    Tendsto (fun T : ℝ => temporalTriangle (leadingDensity q br amp w) T-
      (T:ℂ)*(∫ p in Ioi (0:ℝ), leadingDensity q br amp w p)-
      (Real.log 2:ℂ)*(∫ p in Ioi (0:ℝ), leadingDensity q br amp w p)) atTop
      (𝓝 (physicalCornerCandidate q br amp w)) := by
  have h := (original_leading_triangle_finitePart q br amp w (chamber_reader q w hw)).sub_const
    ((Real.log 2:ℂ)*(∫ p in Ioi (0:ℝ), leadingDensity q br amp w p))
  rwa [original_corner_moment_eq_candidate q br amp w hw hwi] at h

private theorem unit_at_horizon : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hform : radialUnit=fun x => (1-Real.exp (2*x))/(1+Real.exp (2*x)) := by
    funext x
    apply (eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x)))).mpr
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa only [Function.comp_def,Pi.div_apply,sub_zero,add_zero,div_one] using!
    (tendsto_const_nhds.sub he).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

/-- The original radial coordinate fixes the log-two shift; it is not a free counterterm. -/
theorem original_radial_log_shift :
    Tendsto (fun T : ℝ => T+Real.log (horizonCoordinate (-T))/2) atTop
      (𝓝 (Real.log 2)) := by
  have hlog (T : ℝ) : T+Real.log (horizonCoordinate (-T))/2 =
      Real.log (1+radialUnit (-T)) := by
    rw [horizonCoordinate_factor,Real.log_pow,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (radialUnit_add_one_pos (-T))),Real.log_exp]
    ring
  simp_rw [hlog]
  have h := (tendsto_const_nhds (x:=(1:ℝ))).add (unit_at_horizon.comp tendsto_neg_atTop_atBot)
  have htwo : Tendsto (fun T : ℝ => 1+radialUnit (-T)) atTop (𝓝 (2:ℝ)) := by
    simpa only [Function.comp_def,show (1:ℝ)+1=2 by norm_num] using h
  exact (Real.continuousAt_log (by norm_num : (2:ℝ) ≠ 0)).tendsto.comp htwo

private theorem radial_leading_finitePart (K : ℂ) :
    Tendsto (fun T : ℝ => (T:ℂ)*K+(K/2)*(Real.log (horizonCoordinate (-T)):ℂ)) atTop
      (𝓝 ((Real.log 2:ℂ)*K)) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp original_radial_log_shift).mul_const K
  have he (T : ℝ) : (T:ℂ)*K+(K/2)*(Real.log (horizonCoordinate (-T)):ℂ) =
      ((T+Real.log (horizonCoordinate (-T))/2:ℝ):ℂ)*K := by
    push_cast
    ring
  simp_rw [he]
  exact h

/-- The original temporal triangle and the time-first radial integral have exactly the
candidate's difference after their prescribed subtractions. This is the leading horizon
sector; complete angular/metric boundary assembly is not asserted. -/
theorem original_temporal_radial_leading_difference (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2 < w.re) (hwi : w.im ≠ 0) :
    let K := ∫ p in Ioi (0:ℝ), leadingDensity q br amp w p
    Tendsto (fun T : ℝ =>
      (temporalTriangle (leadingDensity q br amp w) T-(T:ℂ)*K)-
      ((T:ℂ)*K+(K/2)*(Real.log (horizonCoordinate (-T)):ℂ))) atTop
      (𝓝 (physicalCornerCandidate q br amp w)) := by
  dsimp only
  have h := (original_leading_triangle_finitePart q br amp w (chamber_reader q w hw)).sub
    (radial_leading_finitePart (∫ p in Ioi (0:ℝ), leadingDensity q br amp w p))
  rwa [original_corner_moment_eq_candidate q br amp w hw hwi] at h

end
end RHTower.D4BMOriginalTemporalCorner
