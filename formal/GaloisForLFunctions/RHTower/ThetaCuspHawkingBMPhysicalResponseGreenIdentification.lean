import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalResponseEndpointCurrents
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalGreenSourceAdmission

/-! Identification of the actual complete physical response with the original endpoint Green integral. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Original endpoint Green integral for the literal complete angular source and original physical modes. -/
def completePhysicalGreenProfile (q r : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) : ℂ :=
  (tortoiseMode true w (physicalRadialFrequency r) t*
      (∫ x in Iic t, tortoiseMode false w (physicalRadialFrequency r) x*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x)+
    tortoiseMode false w (physicalRadialFrequency r) t*
      (∫ x in t..0, tortoiseMode true w (physicalRadialFrequency r) x*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x))/
    connection w (physicalRadialFrequency r)

/-- The actual horizon current is the absolutely convergent complete-source horizon integral. -/
theorem physicalCuspModeCurrent_horizon_integral (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    physicalCuspModeCurrent q r branch w a hw hd hwi hwr false t =
      ∫ x in Iic t, tortoiseMode false w (physicalRadialFrequency r) x*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x := by
  have hi0 : IntegrableOn (fun x => tortoiseMode false w (physicalRadialFrequency r) x*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) (Iio (0:ℝ)) :=
    physicalHorizonSource_integrable q r branch w a hd hwi
  have hi := hi0.mono_set
    (show Iic t ⊆ Iio (0:ℝ) from fun _ hx => hx.trans_lt ht)
  have hlim := intervalIntegral_tendsto_integral_Iic t hi tendsto_id
  have hj : Tendsto (fun s => ∫ x in s..t, tortoiseMode false w (physicalRadialFrequency r) x*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) atBot
      (𝓝 (physicalCuspModeCurrent q r branch w a hw hd hwi hwr false t)) := by
    have hz := (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      physicalCuspModeCurrent q r branch w a hw hd hwi hwr false t) atBot (𝓝 _)).sub
        (physicalCuspModeCurrent_horizon_zero q r branch w a hw hd hwi hwr)
    simp only [sub_zero] at hz
    apply hz.congr'
    filter_upwards [eventually_le_atBot t] with s hs
    exact (physicalCuspModeCurrent_integral q r branch w a hw hd hwi hwr false s t hs ht).symm
  exact tendsto_nhds_unique hj hlim

/-- The original zero endpoint gives the actual normalizable current as its complete outer source integral. -/
theorem physicalCuspModeCurrent_outer_integral (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    physicalCuspModeCurrent q r branch w a hw hd hwi hwr true t =
      -(∫ x in t..0, tortoiseMode true w (physicalRadialFrequency r) x*
        continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) := by
  have hi := physicalNormalizableSource_intervalIntegrable q r branch w a hd hwi t ht
  have hc := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hlim := hc 0 right_mem_uIcc
  rw [uIcc_of_le ht.le,ContinuousWithinAt,nhdsWithin_Icc_eq_nhdsLE ht] at hlim
  have hlim' := hlim.mono_left (nhdsWithin_mono (0:ℝ) Iio_subset_Iic_self)
  have hj : Tendsto (fun s => ∫ x in t..s, tortoiseMode true w (physicalRadialFrequency r) x*
      continuedAngularSourceProjection q branch (physicalAngularParameter r) a w x) (𝓝[<] (0:ℝ))
      (𝓝 (-physicalCuspModeCurrent q r branch w a hw hd hwi hwr true t)) := by
    have hz := (physicalCuspModeCurrent_boundary_zero q r branch w a hw hd hwi hwr).sub_const
      (physicalCuspModeCurrent q r branch w a hw hd hwi hwr true t)
    simp only [zero_sub] at hz
    apply hz.congr'
    filter_upwards [Ioc_mem_nhdsLT ht,self_mem_nhdsWithin] with s hs hs0
    exact (physicalCuspModeCurrent_integral q r branch w a hw hd hwi hwr true t s hs.1.le hs0).symm
  have he := tendsto_nhds_unique hlim' hj
  linear_combination he

/-- The actual original causal response equals the endpoint Green integral of its complete physical source.
All mode matching, source admission, derivative bounds and endpoint currents are derived internally. -/
theorem physicalCuspProfile_eq_completePhysicalGreenProfile (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2)
    (t : ℝ) (ht : t < 0) :
    physicalCuspProfile q r branch w a hw hd hwi hwr t = completePhysicalGreenProfile q r branch w a t := by
  have hc := connection_ne_zero (physicalRadialFrequency_chamber r w (by linarith))
  unfold completePhysicalGreenProfile
  apply (eq_div_iff hc).mpr
  rw [mul_comm,physicalCuspProfile_modeCurrents q r branch w a hw hd hwi hwr t ht,
    physicalCuspModeCurrent_horizon_integral q r branch w a hw hd hwi hwr t ht,
    physicalCuspModeCurrent_outer_integral q r branch w a hw hd hwi hwr t ht]
  ring

/-- Endpoint Green identification holds for the original Hilbert response, not only its selected representative. -/
theorem physicalCuspResponse_ae_completePhysicalGreenProfile (q r : XiZeroCopy) (branch : Bool) (w a : ℂ)
    (hw : 0 < w.re) (hd : 3/2 < w.re) (hwi : w.im ≠ 0) (hwr : |w.re| < 2) :
    physicalCuspResponse q r branch w a hw hd hwi hwr =ᵐ[radialMeasure]
      completePhysicalGreenProfile q r branch w a := by
  filter_upwards [physicalCuspProfile_ae q r branch w a hw hd hwi hwr,
    ae_restrict_mem measurableSet_Iio] with t hp ht
  exact hp.symm.trans (physicalCuspProfile_eq_completePhysicalGreenProfile q r branch w a hw hd hwi hwr t ht)

end
end RHTower.D4BMJointSource
