import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalSourceResolvent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMIncomingSourceTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalNormalizableHorizonDomain
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceGreenBoundary

/-! Actual endpoint brackets for the two-frequency source resolvent. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalSourceResolvent
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem gauss_cont (v chi : ℂ) :
    ContinuousAt (fun z : ℝ => gaussFactor v chi false z) 0 ∧
    ContinuousAt (fun z : ℝ => gaussFirst v chi false z) 0 := by
  have h := gaussFactor_derivatives_continued (w:=v) (chi:=chi) (z:=0) false (by simp)
  exact ⟨h.1.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp),
    h.2.continuousAt.comp_of_eq Complex.continuous_ofReal.continuousAt (by simp)⟩

private theorem horizon_pair_factor (w v chi : ℂ) {z : ℝ} (hz : 0<z) :
    radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon v chi) (horizonFirst v chi) z =
      power ((w+v)/2) z * (power (1/2) (1-z)*
        ((v-w)/2*gaussFactor w chi false z*gaussFactor v chi false z+
          (z:ℂ)*(gaussFactor w chi false z*gaussFirst v chi false z-
            gaussFirst w chi false z*gaussFactor v chi false z))) := by
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hp : power (w/2) z*power (v/2) z=power ((w+v)/2) z := by
    rw [power,power,← Complex.cpow_add _ _ hz0]
    congr 1
    ring
  rw [← hp]
  dsimp only [radialBracket,integratingFactor,horizon,horizonFirst,dress,dressFirst,powerFirst]
  field_simp [hz0]
  ring

private theorem horizon_pair_zero (w v chi : ℂ) (hr : 0<(w+v).re) :
    Tendsto (radialBracket (horizon w chi) (horizonFirst w chi)
      (horizon v chi) (horizonFirst v chi)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : ContinuousAt (fun z : ℝ => power (1/2) (1-z)) 0 := by
    exact ((power_derivatives (1/2) (by norm_num : (0:ℝ)<1)).1.continuousAt).comp_of_eq
      (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hF := gauss_cont w chi
  have hG := gauss_cont v chi
  have hB := hp.mul ((((hF.1.const_mul ((v-w)/2)).mul hG.1).add
    (Complex.continuous_ofReal.continuousAt.mul ((hF.1.mul hG.2).sub (hF.2.mul hG.1)))))
  have he : 0<((w+v)/2).re := by simpa using half_pos hr
  have ht := (power_tendsto_zero he).mul hB.tendsto
  simp only [zero_mul] at ht
  apply (ht.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (horizon_pair_factor w v chi hz).symm

private theorem weighted_horizon_pair_zero (w v chi : ℂ) (hr : 0<(w+v).re) :
    Tendsto (fun z : ℝ => integratingFactor z*horizon w chi z*horizon v chi z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hp : ContinuousAt (fun z : ℝ => power (1/2) (1-z)) 0 := by
    exact ((power_derivatives (1/2) (by norm_num : (0:ℝ)<1)).1.continuousAt).comp_of_eq
      (continuousAt_const.sub continuousAt_id) (by norm_num)
  have hB := ((Complex.continuous_ofReal.continuousAt.mul hp).mul
    (gauss_cont w chi).1).mul (gauss_cont v chi).1
  have he : 0<((w+v)/2).re := by simpa using half_pos hr
  have ht := (power_tendsto_zero he).mul hB.tendsto
  simp only [zero_mul] at ht
  apply (ht.mono_left (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : (z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hpow : power (w/2) z*power (v/2) z=power ((w+v)/2) z := by
    rw [power,power,← Complex.cpow_add _ _ hz0]
    congr 1
    ring
  rw [← hpow]
  dsimp only [integratingFactor,horizon,dress,Pi.mul_apply]
  ring

private theorem normalizable_horizon_split (v chi : ℂ) (hv : v.im≠0)
    {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    normalizable v chi z =
      horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*horizon v chi z+
        (connection v chi/(2*v))*horizon (-v) chi z ∧
    normalizableFirst v chi z =
      horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)*horizonFirst v chi z+
        (connection v chi/(2*v))*horizonFirst (-v) chi z := by
  have h := original_homogeneous_horizon_representation v chi hv
    (fun z hz => (normalizable_derivatives_continued hz).1)
    (fun z hz => (normalizable_derivatives_continued hz).2)
    (fun z hz => normalizable_equation_continued hz) hz
  rwa [normalizable_opposite_coefficient v chi hv] at h

private theorem normalizable_horizon_brackets_zero (w v chi : ℂ) (hv : v.im≠0)
    (hplus : 0<(w+v).re) (hminus : 0<(w-v).re) :
    Tendsto (radialBracket (horizon w chi) (horizonFirst w chi)
      (normalizable v chi) (normalizableFirst v chi)) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun z : ℝ => integratingFactor z*horizon w chi z*normalizable v chi z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let A := horizonRegularCoefficient v chi (normalizable v chi) (normalizableFirst v chi)
  let B := connection v chi/(2*v)
  have hm : 0<(w+-v).re := by simpa only [sub_eq_add_neg] using hminus
  have hP := ((horizon_pair_zero w v chi hplus).const_mul A).add
    ((horizon_pair_zero w (-v) chi hm).const_mul B)
  have hQ := ((weighted_horizon_pair_zero w v chi hplus).const_mul A).add
    ((weighted_horizon_pair_zero w (-v) chi hm).const_mul B)
  simp only [mul_zero,add_zero] at hP hQ
  constructor
  · apply hP.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    obtain ⟨hn,hd⟩ := normalizable_horizon_split v chi hv hz
    dsimp only [radialBracket]
    rw [hn,hd]
    dsimp only [A,B]
    ring
  · apply hQ.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    rw [(normalizable_horizon_split v chi hv hz).1]
    dsimp only [A,B]
    ring

/-- In the genuine mixed-frequency convergence wedge, the actual forced
response and original reader have zero horizon bracket. -/
theorem mixedBracket_horizon_limit (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hwi : w.im≠0) (hv : v.im≠0)
    (hs : (2*s).re<w.re) (hplus : 0<(w+v).re) (hminus : 0<(w-v).re) :
    Tendsto (mixedBracket s chi amp J K w v) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hwr : -2<w.re := by linarith [chamber_re_pos hw]
  have hwr1 : -1<w.re := by linarith [chamber_re_pos hw]
  have hG := (gauss_cont w chi).1.tendsto.mono_left
    (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
  simp only [Complex.ofReal_zero,gaussFactor_zero] at hG
  have hA := (response_ingoing hw s amp J K (onsetTransform (2*s) w)).div hG (by norm_num : (1:ℂ)≠0)
  simp only [div_one] at hA
  have hquot : Tendsto (fun z => continuedResponse s chi amp J K z w/horizon w chi z)
      (𝓝[>] (0:ℝ)) (𝓝 (outerMoment w chi s amp J K (onsetTransform (2*s) w) 0)) := by
    apply hA.congr'
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with z hz
    rw [continuedResponse_eq_original s chi amp J K w hwi hwr1 hs hz.1 hz.2]
    dsimp only [horizon,dress,Pi.div_apply]
    rw [div_div]
  obtain ⟨hW,hP⟩ := normalizable_horizon_brackets_zero w v chi hv hplus hminus
  have ht := (hquot.mul hW).sub
    (hP.mul (incomingSourceTransport_tendsto_horizon s chi amp J K w hwi hwr))
  simp only [mul_zero,zero_mul,sub_zero] at ht
  apply ht.congr'
  have hGn : ∀ᶠ z : ℝ in 𝓝[>] (0:ℝ), gaussFactor w chi false (z:ℂ)≠0 :=
    hG.eventually (isOpen_compl_singleton.mem_nhds (by norm_num : (1:ℂ)≠0))
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1),hGn] with z hz hgz
  have hh : horizon w chi z≠0 :=
    mul_ne_zero (power_ne_zero _ hz.1) hgz
  have hder := continuedResponse_div_horizon_hasDerivAt s chi amp J K w hwi hwr
    (connection_ne_zero hw) hz hh
  have hder' := ((continuedResponse_hasDerivAt s chi amp J K w hwi hwr hz).1.div
    (horizon_derivatives_continued (w:=w) (chi:=chi) hz).1 hh)
  have he := hder.unique hder'
  dsimp only [mixedBracket,radialBracket]
  rw [he]
  field_simp [hh]
  ring

private theorem continuedFirst_original (s chi amp J K w : ℂ) (hwi : w.im≠0)
    (hwr : -1<w.re) (hs : (2*s).re<w.re) {z : ℝ} (hz : z∈Ioo (0:ℝ) 1) :
    continuedResponseFirst s chi amp J K z w =
      responseFirst w chi s amp J K (onsetTransform (2*s) w) z := by
  rw [continuedResponseFirst,
    continuedHorizonMoment_eq_original s chi amp J K w hwi hwr hs hz.1 hz.2,
    continuedOuterMoment_eq_original s chi amp J K w hs hz.2.le]
  rfl

/-- The outer endpoint also vanishes for the actual two-frequency bracket;
the reader frequency is independent of the source frequency. -/
theorem mixedBracket_outer_limit (s chi amp J K w v : ℂ)
    (hw : Chamber w chi) (hv : Chamber v chi) (hwi : w.im≠0)
    (hs : (2*s).re<w.re) :
    Tendsto (mixedBracket s chi amp J K w v) (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have hwr : -1<w.re := by linarith [chamber_re_pos hw]
  have hc := greenMoments_continuousOn hw s amp J K (onsetTransform (2*s) w)
  have hA := (hc.1 1 (by norm_num)).mono Ioo_subset_Icc_self
  have hB := (hc.2 1 (by norm_num)).mono Ioo_subset_Icc_self
  rw [ContinuousWithinAt,nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (0:ℝ)<1)] at hA hB
  have hB0 : outerMoment w chi s amp J K (onsetTransform (2*s) w) 1=0 := by
    simp only [outerMoment,intervalIntegral.integral_same]
  rw [hB0] at hB
  have hY := response_boundary hw s amp J K (onsetTransform (2*s) w)
  have hD := ((normalizableFirst_boundary hw).mul hA).add
    ((horizonFirst_boundary_weighted hw).mul hB)
  have hN := (normalizable_boundary hv).mono_left
    (show 𝓝[<] (1:ℝ)≤𝓝 1 from nhdsWithin_le_nhds)
  have hZ : Tendsto (fun z : ℝ => (z:ℂ)) (𝓝[<] (1:ℝ)) (𝓝 (1:ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hZ.mul ((hY.mul (normalizableFirst_boundary hv)).sub (hD.mul hN))
  simp only [zero_mul,mul_zero,sub_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ)<1)] with z hz
  dsimp only [mixedBracket,radialBracket]
  rw [continuedResponse_eq_original s chi amp J K w hwi hwr hs hz.1 hz.2,
    continuedFirst_original s chi amp J K w hwi hwr hs hz]
  dsimp only [integratingFactor,responseFirst]
  rw [power_half_eq_sqrt (sub_nonneg.mpr hz.2.le)]
  ring

end
end RHTower.D4BMOriginalSourceResolvent
