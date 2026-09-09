import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteAngularSourceBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceOuterModeLimits
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialModeMatching
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceKernelBounds

/-! Absolute admission of the complete physical source in the original endpoint Green integrals. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The original horizon mode has its true exponential decay rate on the full negative ray. -/
theorem tortoiseHorizon_norm_le_exp {w chi : ℂ} (h : Chamber w chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < 0,
      ‖tortoiseMode false w chi t‖ ≤ C*Real.exp (w.re*t) := by
  have hc : ContinuousOn (fun u : ℝ => power w (1+u)) (Icc 0 1) := by
    intro u hu
    exact (((power_derivatives w (by linarith [hu.1] : 0 < 1+u)).1.continuousAt).comp_of_eq
      (continuous_const.add continuous_id).continuousAt rfl).continuousWithinAt
  obtain ⟨C,hC,hb⟩ := laplaceProfile_norm_le_exp w _ hc
  obtain ⟨D,hD,hg⟩ := horizonFactor_bound h
  refine ⟨C*D,mul_nonneg hC hD,fun t ht => ?_⟩
  have hz := horizonCoordinate_interior t ht
  change ‖horizon w chi (horizonCoordinate t)‖ ≤ _
  rw [horizon,dress,horizonPower_tortoise w t ht,norm_mul]
  exact (mul_le_mul (hb t ht) (hg _ ⟨hz.1.le,hz.2.le⟩) (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The original normalizable mode is bounded between any fixed interior point and the outer endpoint. -/
theorem tortoiseNormalizable_bounded_outer {w chi : ℂ} (h : Chamber w chi) (s : ℝ) (hs : s < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo s 0, ‖tortoiseMode true w chi t‖ ≤ C := by
  have hc : ContinuousOn (tortoiseMode true w chi) (Ioo s 0) :=
    fun t ht => (tortoiseMode_hasDerivAt h true t ht.2).1.continuousAt.continuousWithinAt
  have hl := ((tortoiseMode_hasDerivAt h true s hs).1.continuousAt.tendsto).mono_left
    (show 𝓝[>] s ≤ 𝓝 s from nhdsWithin_le_nhds)
  have he := continuousOn_Icc_extendFrom_Ioo hc hl (tortoiseNormalizable_boundary h)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn he
  refine ⟨max C 0,le_max_right _ _,fun t ht => ?_⟩
  have hb := (hC t ⟨ht.1.le,ht.2.le⟩).trans (le_max_left C 0)
  rwa [extendFrom_extends hc _ ht] at hb

/-- The complete physical horizon source pairing is absolutely integrable all the way to the original horizon. -/
theorem physicalHorizonSource_integrable (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) :
    Integrable (fun t => tortoiseMode false w (physicalRadialFrequency r) t*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t) radialMeasure := by
  have hc := physicalRadialFrequency_chamber r w (by linarith)
  obtain ⟨C,hC,hH⟩ := tortoiseHorizon_norm_le_exp hc
  obtain ⟨D,hD,hF⟩ := continuedAngularSourceProjection_bounded q branch (physicalAngularParameter r) a w hd hwi
  have hmc : ContinuousOn (tortoiseMode false w (physicalRadialFrequency r)) (Iio (0:ℝ)) :=
    fun t ht => (tortoiseMode_hasDerivAt hc false t ht).1.continuousAt.continuousWithinAt
  have hfc := continuedAngularSourceProjection_continuousOn q branch (physicalAngularParameter r) a w hwi (by linarith)
  have hi : Integrable (fun t : ℝ => Real.exp (w.re*t)) radialMeasure :=
    (integrableOn_exp_mul_Iic (by linarith : 0 < w.re) 0).mono_set Iio_subset_Iic_self
  apply (hi.const_mul (C*D)).mono' ((hmc.mul hfc).aestronglyMeasurable measurableSet_Iio)
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  simp only [Pi.mul_apply,norm_mul]
  exact (mul_le_mul (hH t ht) (hF t ht) (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- The complete physical normalizable source pairing is absolutely admitted up to the original outer endpoint. -/
theorem physicalNormalizableSource_intervalIntegrable (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (s : ℝ) (hs : s < 0) :
    IntervalIntegrable (fun t => tortoiseMode true w (physicalRadialFrequency r) t*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w t) volume s 0 := by
  have hc := physicalRadialFrequency_chamber r w (by linarith)
  obtain ⟨C,hC,hN⟩ := tortoiseNormalizable_bounded_outer hc s hs
  obtain ⟨D,hD,hF⟩ := continuedAngularSourceProjection_bounded q branch (physicalAngularParameter r) a w hd hwi
  have hmc : ContinuousOn (tortoiseMode true w (physicalRadialFrequency r)) (Ioo s 0) :=
    fun t ht => (tortoiseMode_hasDerivAt hc true t ht.2).1.continuousAt.continuousWithinAt
  have hfc := (continuedAngularSourceProjection_continuousOn q branch (physicalAngularParameter r) a w hwi
    (by linarith)).mono (show Ioo s 0 ⊆ Iio (0:ℝ) from fun _ ht => ht.2)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).mpr
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  apply (integrable_const (C*D) : Integrable (fun _ : ℝ => C*D) (volume.restrict (Ioo s 0))).mono'
    ((hmc.mul hfc).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul (hN t ht) (hF t ht.2) (norm_nonneg _) hC

end
end RHTower.D4BMJointSource
