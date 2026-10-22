import GaloisForLFunctions.RHTower.Suzuki.SuzukiRaisedMetricShiftLimit
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ImaginaryCarrierCollapse
import GaloisForLFunctions.RHTower.Suzuki.SuzukiXiFirstDefectJetSource
import Mathlib.Analysis.Calculus.Deriv.Inverse

open Complex Filter Set
open scoped Topology InnerProduct NNReal
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower
noncomputable section
namespace RHTower

private theorem inverse_reflection (a : SuzukiPositiveAperture) (t : ℝ≥0)
    (f : SuzukiApertureIntervalL2 a.1) :
    suzukiRaisedMetricInverse a t (suzukiWeilIntervalReflection a f) =
      suzukiWeilIntervalReflection a (suzukiRaisedMetricInverse a t f) := by
  have hcomm (v : SuzukiApertureIntervalL2 a.1) :
      suzukiRaisedMetricTransfer a t (suzukiWeilIntervalReflection a v) =
        suzukiWeilIntervalReflection a (suzukiRaisedMetricTransfer a t v) := by
    simp only [suzukiRaisedMetricTransfer, add_apply, one_apply_eq_self,
      smul_apply, map_add, map_smul, suzukiWeilIntervalCovariance_reflection]
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp
    (suzukiRaisedMetricTransfer_isUnit a t)).1
  rw [suzukiRaisedMetricTransfer_inverse_apply, hcomm,
    suzukiRaisedMetricTransfer_inverse_apply]

/-- The raised covariance preserves the literal arithmetic reflection law. -/
theorem suzukiRaisedMetricCovariance_reflection
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (f : SuzukiApertureIntervalL2 a.1) :
    suzukiRaisedMetricCovariance a t (suzukiWeilIntervalReflection a f) =
      suzukiWeilIntervalReflection a (suzukiRaisedMetricCovariance a t f) := by
  change suzukiWeilIntervalCovariance a
    (suzukiRaisedMetricInverse a t (suzukiWeilIntervalReflection a f)) = _
  rw [inverse_reflection, suzukiWeilIntervalCovariance_reflection]
  rfl

theorem suzukiRaisedMetricCovariance_exponential_reflection
    (a : SuzukiPositiveAperture) (t : ℝ≥0) (s : ℝ) :
    suzukiRaisedMetricCovariance a t (suzukiTaExponentialL2 a (-s)) =
      suzukiWeilIntervalReflection a
        (suzukiRaisedMetricCovariance a t (suzukiTaExponentialL2 a s)) := by
  rw [← suzukiWeilIntervalReflection_exponential, suzukiRaisedMetricCovariance_reflection]

/-- Literal Fourier quotient of the actual raised-metric response. -/
def suzukiRaisedMetricLivsic (b : SuzukiRaisedMetricParameters) (z : ℂ) : ℂ :=
  ((z-I)/(z+I)) *
    (suzukiTaPhysicalFourier b.1 (suzukiRaisedMetricRawDeficiency b.1 b.2) z /
      suzukiTaPhysicalFourier b.1 (suzukiRaisedMetricRawDeficiency b.1 b.2) (-z))

/-- Zero increment recovers the original actual V2 carrier exactly. -/
theorem suzukiRaisedMetricLivsic_zero (a : SuzukiPositiveAperture) (z : ℂ) :
    suzukiRaisedMetricLivsic (a, 0) z = suzukiTaV2Livsic a z := by
  rw [suzukiRaisedMetricLivsic, suzukiRaisedMetricRawDeficiency_zero,
    suzukiTaV2Livsic_eq_rawDeficiency]
  unfold suzukiLivsicQuotient suzukiTaV2RawCharacteristicA suzukiTaV2RawCharacteristicE
  rw [suzukiTaPhysicalFourier_rawDeficiency_reflection]
  exact (mul_div_mul_comm _ _ _ _).symm

theorem suzukiRaisedMetricLivsic_imaginary
    (b : SuzukiRaisedMetricParameters) (s : ℝ) :
    suzukiRaisedMetricLivsic b (I*(s : ℂ)) =
      ((I*(s : ℂ)-I)/(I*(s : ℂ)+I)) *
        (suzukiRaisedMetricMixedPairing b (-s) / suzukiRaisedMetricMixedPairing b s) := by
  rw [suzukiRaisedMetricLivsic,
    show -(I*(s : ℂ)) = I*((-s : ℝ) : ℂ) by push_cast; ring,
    suzukiTaPhysicalFourier_imaginary_eq_polar_pairing,
    suzukiTaPhysicalFourier_imaginary_eq_polar_pairing, neg_neg]
  rfl

/-- The entire class of raised metric shifts collapses on the interior
imaginary segment, uniformly over the increment. -/
theorem tendsto_suzukiRaisedMetricLivsic_imaginary_zero (s : Ioo (1/2 : ℝ) 1) :
    Tendsto (fun b : SuzukiRaisedMetricParameters => suzukiRaisedMetricLivsic b (I*(s.1 : ℂ)))
      (comap (fun b : SuzukiRaisedMetricParameters => b.1.1) atTop) (𝓝 0) := by
  obtain ⟨hp, hm⟩ := tendsto_suzukiRaisedMetric_mixed_pairings s
  have hl : ((1/(1+s.1) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero one_ne_zero (by linarith [s.2.1])
  have hc (b : SuzukiRaisedMetricParameters) : (suzukiRaisedMetricMixedScale b s.1 : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    apply ne_of_gt
    apply mul_pos _ (Real.exp_pos _)
    exact add_pos_of_pos_of_nonneg (boundedPerturbedFormShift_pos _) b.2.2
  have hr := (hm.div hp hl).congr' (Eventually.of_forall fun b =>
    mul_div_mul_left (suzukiRaisedMetricMixedPairing b (-s.1))
      (suzukiRaisedMetricMixedPairing b s.1) (hc b))
  simpa only [suzukiRaisedMetricLivsic_imaginary, zero_div, mul_zero] using
    hr.const_mul ((I*(s.1 : ℂ)-I)/(I*(s.1 : ℂ)+I))

/-- The audited nonzero first defect gives a nonzero Xi value on the interior
imaginary segment; reusable independently of any metric-shift family. -/
theorem exists_xi_target_imaginary_ne_zero :
    ∃ s : Ioo (1/2 : ℝ) 1, xiHedenmalmLivsicTarget (I*(s.1 : ℂ)) ≠ 0 := by
  have hd : deriv xiHedenmalmLivsicTarget I ≠ 0 := by
    intro h
    have hp := xiHedenmalmLivsicFirstDefectJet_mem_Ioo.1
    rw [xiHedenmalmLivsicFirstDefectJet, h, mul_zero, Complex.zero_re] at hp
    norm_num at hp
  have hn := differentiableAt_xiHedenmalmLivsicTarget_I.hasDerivAt.eventually_ne (c := 0) hd
  have ht : Tendsto (fun s : ℝ => I*(s : ℂ)) (𝓝[<] (1 : ℝ)) (𝓝[≠] I) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous (fun s : ℝ => I*(s : ℂ)) :=
        continuous_const.mul Complex.continuous_ofReal
      have h := (hcont.tendsto (1 : ℝ)).mono_left
        (show 𝓝[<] (1 : ℝ) ≤ 𝓝 (1 : ℝ) from nhdsWithin_le_nhds)
      simpa only [Complex.ofReal_one, mul_one] using h
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s < 1 at hs
      change I*(s : ℂ) ≠ I
      intro heq
      have heq' : I*(s : ℂ) = I*(1 : ℂ) := by simpa using heq
      have hreal : s = 1 := Complex.ofReal_injective (mul_left_cancel₀ I_ne_zero heq')
      linarith
  have hlo : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 1/2 < s :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  obtain ⟨s, hnonzero, hslo, hshi⟩ :=
    ((ht.eventually hn).and (hlo.and self_mem_nhdsWithin)).exists
  exact ⟨⟨s, hslo, hshi⟩, hnonzero⟩

/-- No raised-shift schedule identifies Xi, even pointwise on this segment.
The actual source and shift equations are discharged by construction. -/
theorem not_exists_suzukiRaisedMetric_cofinal_xi_segment_limit :
    ¬ ∃ b : ℕ → SuzukiRaisedMetricParameters,
      Tendsto (fun n => (b n).1.1) atTop atTop ∧
      ∀ s : Ioo (1/2 : ℝ) 1,
        Tendsto (fun n => suzukiRaisedMetricLivsic (b n) (I*(s.1 : ℂ))) atTop
          (𝓝 (xiHedenmalmLivsicTarget (I*(s.1 : ℂ)))) := by
  rintro ⟨b, hb, hxi⟩
  obtain ⟨s, hs⟩ := exists_xi_target_imaginary_ne_zero
  have hzero := (tendsto_suzukiRaisedMetricLivsic_imaginary_zero s).comp
    (tendsto_comap_iff.2 hb)
  exact hs (tendsto_nhds_unique (hxi s) hzero)

/-- In particular, no cofinal raised-shift family converges locally uniformly
to the normalized Xi target in the upper half-plane. -/
theorem not_exists_suzukiRaisedMetric_cofinal_xi_limit :
    ¬ ∃ b : ℕ → SuzukiRaisedMetricParameters,
      Tendsto (fun n => (b n).1.1) atTop atTop ∧
      TendstoLocallyUniformlyOn (fun n => suzukiRaisedMetricLivsic (b n))
        xiHedenmalmLivsicTarget atTop {z : ℂ | 0 < z.im} := by
  rintro ⟨b, hb, hconv⟩
  apply not_exists_suzukiRaisedMetric_cofinal_xi_segment_limit
  refine ⟨b, hb, fun s => ?_⟩
  exact hconv.tendsto_at (by
    change 0 < (I*(s.1 : ℂ)).im
    simpa using (show 0 < s.1 by linarith [s.2.1]))

end RHTower
end
