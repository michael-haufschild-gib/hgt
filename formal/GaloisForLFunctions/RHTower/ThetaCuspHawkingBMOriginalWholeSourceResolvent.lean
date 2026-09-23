import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceResolventEndpoints
import Mathlib.Topology.Order.ExtendFrom

/-! The complete original two-frequency source identity with derived endpoint admission. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem interval_congr_Ioo {f g : ℝ→ℂ} {a b : ℝ} (hab : a≤b)
    (hf : IntervalIntegrable f volume a b) (he : ∀ z∈Ioo a b, f z=g z) :
    IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hf).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact he z hz

private theorem interval_of_endpoint_limits {f : ℝ→ℂ} {a b : ℝ} {L R : ℂ}
    (hab : a<b) (hc : ContinuousOn f (Ioo a b))
    (hL : Tendsto f (𝓝[>] a) (𝓝 L)) (hR : Tendsto f (𝓝[<] b) (𝓝 R)) :
    IntervalIntegrable f volume a b := by
  have he := continuousOn_Icc_extendFrom_Ioo hc hL hR
  have hi : IntervalIntegrable (extendFrom (Ioo a b) f) volume a b :=
    (he.mono (by rw [uIcc_of_le hab.le])).intervalIntegrable
  exact interval_congr_Ioo hab.le hi (extendFrom_extends hc)

private def responsePowerCore (s chi amp J K w : ℂ) (z : ℝ) : ℂ :=
  continuedResponse s chi amp J K z w/power (w/2) z

private theorem responsePowerCore_cont (s chi amp J K w : ℂ)
    (hwi : w.im≠0) (hwr : -2<w.re) :
    ContinuousOn (responsePowerCore s chi amp J K w) (Ioo (0:ℝ) 1) := by
  intro z hz
  exact (((continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz).1.continuousAt).div
    (power_derivatives (w/2) hz.1).1.continuousAt (power_ne_zero _ hz.1)).continuousWithinAt

private theorem responsePowerCore_limit (s chi amp J K w : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    Tendsto (responsePowerCore s chi amp J K w) (𝓝[>] (0:ℝ))
      (𝓝 (outerMoment w chi s amp J K (onsetTransform (2*s) w) 0)) := by
  apply (response_ingoing hw s amp J K (onsetTransform (2*s) w)).congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
  rw [responsePowerCore,continuedResponse_eq_original s chi amp J K w hwi
    (by linarith [chamber_re_pos hw]) hs hz.1 hz.2]

private theorem horizon_density_integrable (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hs : (2*s).re<w.re)
    (hr : 0<(w+v).re) {b : ℝ} (hb : b∈Ioo (0:ℝ) 1) :
    IntervalIntegrable (fun z : ℝ => continuedResponse s chi amp J K z w*horizon v chi z/
      (2*(z:ℂ)*(Real.sqrt (1-z):ℂ))) volume 0 b := by
  let U := responsePowerCore s chi amp J K w
  let V := extendFrom (Ioo (0:ℝ) b) U
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hU : ContinuousOn U (Ioo (0:ℝ) b) :=
    (responsePowerCore_cont s chi amp J K w hwi hwr).mono
      (fun z hz => ⟨hz.1,hz.2.trans hb.2⟩)
  have hUb : ContinuousAt U b :=
    ((responsePowerCore_cont s chi amp J K w hwi hwr).continuousAt (isOpen_Ioo.mem_nhds hb))
  have hV : ContinuousOn V (Icc (0:ℝ) b) :=
    continuousOn_Icc_extendFrom_Ioo hU (responsePowerCore_limit s chi amp J K w hw hwi hs)
      (hUb.tendsto.mono_left nhdsWithin_le_nhds)
  let F := fun z : ℝ => V z*gaussFactor v chi false z/(2*(Real.sqrt (1-z):ℂ))
  have hF : ContinuousOn F (Icc (0:ℝ) b) := by
    intro z hz
    have hn : ‖(z:ℂ)‖ₑ<1 := by
      rw [← ofReal_norm,Complex.norm_real,Real.norm_of_nonneg hz.1]
      exact ENNReal.ofReal_lt_one.mpr (hz.2.trans_lt hb.2)
    have hG := (gaussFactor_derivatives_continued (w:=v) (chi:=chi) false hn).1.comp_ofReal.continuousAt
    exact ((hV z hz).mul hG.continuousWithinAt).div
      (show ContinuousWithinAt (fun t : ℝ => 2*(Real.sqrt (1-t):ℂ)) (Icc 0 b) z by fun_prop)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
        (Real.sqrt_pos.mpr (by linarith [hz.2,hb.2])).ne'))
  have hp : IntervalIntegrable (power ((w+v)/2-1)) volume 0 b :=
    intervalIntegral.intervalIntegrable_cpow' (by
      have hh : 0<((w+v)/2).re := by simpa using half_pos hr
      simp only [Complex.sub_re,Complex.one_re]
      linarith)
  have hi := hp.mul_continuousOn (hF.mono (by rw [uIcc_of_le hb.1.le]))
  apply interval_congr_Ioo hb.1.le hi
  intro z hz
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.1.ne'
  have hpow : power ((w+v)/2-1) z=power (w/2) z*power (v/2) z/(z:ℂ) := by
    dsimp only [power]
    rw [Complex.cpow_sub _ _ hz0,Complex.cpow_one,← Complex.cpow_add _ _ hz0]
    congr 1
    ring
  dsimp only [F,V]
  rw [extendFrom_extends hU z hz,hpow]
  dsimp only [U,responsePowerCore,horizon,dress]
  field_simp [power_ne_zero (w/2) hz.1,hz0]

private theorem normalizable_split (v chi : ℂ) (hv : v.im≠0) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    normalizable v chi z=
      horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*horizon v chi z+
        (connection v chi/(2*v))*horizon (-v) chi z := by
  have h := (original_homogeneous_horizon_representation v chi hv
    (fun z hz => (normalizable_derivatives_continued hz).1)
    (fun z hz => (normalizable_derivatives_continued hz).2)
    (fun z hz => normalizable_equation_continued hz) hz).1
  rwa [normalizable_opposite_coefficient v chi hv] at h

private theorem mixed_cont (s chi amp J K w v : ℂ) (hwi : w.im≠0) (hwr : -2<w.re) :
    ContinuousOn (mixedDensity s chi amp J K w v) (Ioo (0:ℝ) 1) := by
  intro z hz
  exact (((continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz).1.continuousAt.mul
    (normalizable_derivatives_continued (w:=v) (chi:=chi) hz).1.continuousAt).div
    (show ContinuousAt (fun t : ℝ => 2*(t:ℂ)*(Real.sqrt (1-t):ℂ)) z by fun_prop)
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hz.1.ne'))
      (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hz.2)).ne'))).continuousWithinAt

private theorem mixed_outer_zero (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hv : Chamber v chi) (hwi : w.im≠0) (hs : (2*s).re<w.re) :
    Tendsto (mixedDensity s chi amp J K w v) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have ht := ((response_boundary hw s amp J K (onsetTransform (2*s) w)).mul
    (normalizable_boundary_ratio hv)).div
    ((Complex.continuous_ofReal.tendsto (1:ℝ)).const_mul 2 |>.mono_left
      (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)) (by norm_num : (2:ℂ)*1≠0)
  simp only [zero_mul,zero_div] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with z hz
  rw [mixedDensity,continuedResponse_eq_original s chi amp J K w hwi
    (by linarith [chamber_re_pos hw]) hs hz.1 hz.2]
  dsimp only [Pi.div_apply,Pi.mul_apply]
  ring

/-- The original full response/reader product is absolutely integrable in
the mixed convergence wedge; no integral-admission hypothesis is supplied. -/
theorem mixedDensity_whole_integrable (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hv : Chamber v chi) (hwi : w.im≠0) (hvi : v.im≠0)
    (hs : (2*s).re<w.re) (hplus : 0<(w+v).re) (hminus : 0<(w-v).re) :
    IntervalIntegrable (mixedDensity s chi amp J K w v) volume 0 1 := by
  have hb : (1/2:ℝ)∈Ioo (0:ℝ) 1 := by constructor <;> norm_num
  have hI := horizon_density_integrable s chi amp J K w v hw hwi hs hplus hb
  have hO := horizon_density_integrable s chi amp J K w (-v) hw hwi hs
    (by simpa only [sub_eq_add_neg] using hminus) hb
  let A := horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)
  let B := connection v chi/(2*v)
  have hleft : IntervalIntegrable (mixedDensity s chi amp J K w v) volume 0 (1/2) := by
    apply interval_congr_Ioo (by norm_num : (0:ℝ)≤1/2) ((hI.const_mul A).add (hO.const_mul B))
    intro z hz
    rw [mixedDensity,normalizable_split v chi hvi ⟨hz.1,hz.2.trans hb.2⟩]
    dsimp only [A,B]
    ring
  have hcont := mixed_cont s chi amp J K w v hwi (by linarith [chamber_re_pos hw])
  have hright : IntervalIntegrable (mixedDensity s chi amp J K w v) volume (1/2) 1 :=
    interval_of_endpoint_limits hb.2
      (hcont.mono (fun z hz => ⟨hb.1.trans hz.1,hz.2⟩))
      ((hcont.continuousAt (isOpen_Ioo.mem_nhds hb)).tendsto.mono_left nhdsWithin_le_nhds)
      (mixed_outer_zero s chi amp J K w v hw hv hwi hs)
  exact hleft.trans hright

private theorem horizon_source_zero (s chi amp J K w v : ℂ) (hr : 0<(w+v).re) :
    Tendsto (fun z : ℝ => horizon v chi z*continuedSourceProfile s amp J K w z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let T := 1/(w-2*s)+onsetCorrection (2*s) w
  have hG := (gaussFactor_derivatives_continued (w:=v) (chi:=chi) (z:=0) false (by simp)).1.comp_ofReal.continuousAt
  have hR := (sourceRemainder_continuous s w amp J K T).continuousAt (x:=0)
  have he : 0<((w+v)/2).re := by simpa using half_pos hr
  have ht := (power_tendsto_zero he).mul (hG.mul hR).tendsto
  simp only [zero_mul] at ht
  apply (ht.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hp : power ((w+v)/2) z=power (v/2) z*power (w/2) z := by
    dsimp only [power]
    rw [← Complex.cpow_add _ _ hz0]
    congr 1
    ring
  rw [hp]
  dsimp only [horizon,dress,continuedSourceProfile,sourceProfile,Pi.mul_apply,T]
  ring

/-- The original source overlap is admitted over both physical endpoints
with independent source and reader frequencies. -/
theorem sourceDensity_whole_integrable (s chi amp J K w v : ℂ)
    (hv : Chamber v chi) (hvi : v.im≠0)
    (hplus : 0<(w+v).re) (hminus : 0<(w-v).re) :
    IntervalIntegrable (sourceDensity s chi amp J K w v) volume 0 1 := by
  have hc : ContinuousOn (sourceDensity s chi amp J K w v) (Ioo (0:ℝ) 1) := by
    intro z hz
    exact ((normalizable_derivatives_continued (w:=v) (chi:=chi) hz).1.continuousAt.mul
      (continuedSourceProfile_continuousAt s amp J K w hz.1)).continuousWithinAt
  let A := horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)
  let B := connection v chi/(2*v)
  have hL : Tendsto (sourceDensity s chi amp J K w v) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have ht := ((horizon_source_zero s chi amp J K w v hplus).const_mul A).add
      ((horizon_source_zero s chi amp J K w (-v) (by simpa only [sub_eq_add_neg] using hminus)).const_mul B)
    simp only [mul_zero,add_zero] at ht
    apply ht.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    rw [sourceDensity,normalizable_split v chi hvi hz]
    dsimp only [A,B]
    ring
  have hR : Tendsto (sourceDensity s chi amp J K w v) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    have ht := (normalizable_boundary hv).mul
      (continuedSourceProfile_continuousAt s amp J K w (by norm_num : (0:ℝ)<1)).tendsto
    simpa only [sourceDensity,zero_mul] using! ht.mono_left (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  exact interval_of_endpoint_limits (by norm_num) hc hL hR

/-- Full original two-frequency source resolvent: both endpoint brackets
vanish and both whole-domain integrals are separately admitted. -/
theorem whole_source_resolvent (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hv : Chamber v chi) (hwi : w.im≠0) (hvi : v.im≠0)
    (hs : (2*s).re<w.re) (hplus : 0<(w+v).re) (hminus : 0<(w-v).re) :
    IntervalIntegrable (mixedDensity s chi amp J K w v) volume 0 1 ∧
    IntervalIntegrable (sourceDensity s chi amp J K w v) volume 0 1 ∧
    (v^(2 : ℕ)-w^(2 : ℕ))*(∫ z in (0:ℝ)..1,mixedDensity s chi amp J K w v z)=
      ∫ z in (0:ℝ)..1,sourceDensity s chi amp J K w v z := by
  have hI := mixedDensity_whole_integrable s chi amp J K w v hw hv hwi hvi hs hplus hminus
  have hS := sourceDensity_whole_integrable s chi amp J K w v hv hvi hplus hminus
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num : (0:ℝ)<1)
    (fun z hz => mixedBracket_hasDerivAt s chi amp J K w v hwi
      (by linarith [chamber_re_pos hw]) (connection_ne_zero hw) hz)
    (((hI.const_mul (v^(2 : ℕ)-w^(2 : ℕ))).sub hS).div_const 2)
    (mixedBracket_horizon_limit s chi amp J K w v hw hwi hvi hs hplus hminus)
    (mixedBracket_outer_limit s chi amp J K w v hw hv hwi hs)
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub (hI.const_mul _) hS,
    intervalIntegral.integral_const_mul] at h
  refine ⟨hI,hS,?_⟩
  linear_combination 2*h

end
end RHTower.D4BMOriginalSourceResolvent
