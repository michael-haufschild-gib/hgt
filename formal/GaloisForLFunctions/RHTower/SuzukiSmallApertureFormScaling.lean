import GaloisForLFunctions.RHTower.SuzukiSmallApertureGroundAsymptotic
import GaloisForLFunctions.RHTower.SuzukiHlogInwardFormCore
import GaloisForLFunctions.RHTower.SuzukiLimitingLogOperator

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

private abbrev smallValue (a : SuzukiPrimeFreeSmallAperture) : ℝ :=
  GaloisForLFunctions.RHTower.SuzukiPrimeFreeSmallAperture.val a

private theorem smallValue_pos (a : SuzukiPrimeFreeSmallAperture) : 0 < smallValue a :=
  GaloisForLFunctions.RHTower.SuzukiPrimeFreeSmallAperture.pos a

private abbrev smallPositiveAperture (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiPositiveAperture := ⟨smallValue a, smallValue_pos a⟩

/-- Multiplicative loss of the logarithmic weight under a positive dilation. -/
def suzukiHlogScaleBound (r : ℝ) : ℝ := 1 + Real.posLog r

theorem suzukiHlogScaleBound_pos {r : ℝ} (_hr : 0 < r) :
    0 < suzukiHlogScaleBound r := by
  unfold suzukiHlogScaleBound
  linarith [Real.posLog_nonneg (x := r)]

theorem suzukiLogWeight_mul_le_scaleBound
    {r : ℝ} (_hr : 0 < r) (x : ℝ) :
    suzukiLogWeight (r * x) ≤ suzukiHlogScaleBound r * suzukiLogWeight x := by
  rw [suzukiLogWeight_eq_one_add_posLog, suzukiLogWeight_eq_one_add_posLog]
  have hmul := Real.posLog_mul (x := r) (y := x)
  have hr0 := Real.posLog_nonneg (x := r)
  have hx0 := Real.posLog_nonneg (x := x)
  unfold suzukiHlogScaleBound
  nlinarith [mul_nonneg hr0 hx0]

def suzukiHlogScaleRatio (r : ℝ) (x : ℝ) : ℂ :=
  (Real.sqrt (suzukiLogWeight x / suzukiLogWeight (r⁻¹ * x)) : ℝ)

theorem measurable_suzukiHlogScaleRatio (r : ℝ) :
    Measurable (suzukiHlogScaleRatio r) := by
  unfold suzukiHlogScaleRatio
  exact Complex.measurable_ofReal.comp
    (Real.continuous_sqrt.measurable.comp (measurable_suzukiLogWeight.div
      (measurable_suzukiLogWeight.comp (measurable_const.mul measurable_id))))

theorem norm_suzukiHlogScaleRatio_le {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ‖suzukiHlogScaleRatio r x‖ ≤ Real.sqrt (suzukiHlogScaleBound r) := by
  have hw := suzukiLogWeight_mul_le_scaleBound hr (r⁻¹ * x)
  have harg : r * (r⁻¹ * x) = x := by field_simp [hr.ne']
  rw [harg] at hw
  have hden := suzukiLogWeight_pos (r⁻¹ * x)
  have hdiv : suzukiLogWeight x / suzukiLogWeight (r⁻¹ * x) ≤
      suzukiHlogScaleBound r := by
    rw [div_le_iff₀ hden]
    exact hw
  rw [suzukiHlogScaleRatio, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt hdiv

def suzukiHlogScaleRatioMul (r : ℝ) (hr : 0 < r) : SoninL2 →L[ℂ] SoninL2 :=
  lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
    (measurable_suzukiHlogScaleRatio r)
    (Real.sqrt_nonneg (suzukiHlogScaleBound r))
    (norm_suzukiHlogScaleRatio_le hr)

/-- Normalized frequency dilation by `r⁻¹` on weighted logarithmic `L²`. -/
def suzukiHlogFourierScaleCLM (r : ℝ) (hr : 0 < r) :
    SuzukiHlogFourierL2 →L[ℂ] SuzukiHlogFourierL2 :=
  suzukiHlogDensityUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    suzukiHlogScaleRatioMul r hr ∘L
      dilationCLM r⁻¹ (inv_pos.mpr hr) ∘L
        suzukiHlogDensityUnitary.toLinearIsometry.toContinuousLinearMap

theorem suzukiHlogFourierScaleCLM_ae (r : ℝ) (hr : 0 < r)
    (f : SuzukiHlogFourierL2) :
    (suzukiHlogFourierScaleCLM r hr f : ℝ → ℂ) =ᵐ[suzukiHlogMeasure]
      fun x => (Real.sqrt r⁻¹ : ℂ) * f (r⁻¹ * x) := by
  apply (withDensity_realDensity_ae_eq measurable_suzukiLogWeight
    suzukiLogWeight_pos).mpr
  have hdiv := densityDiv_ae suzukiLogWeight measurable_suzukiLogWeight
    suzukiLogWeight_pos
    (suzukiHlogScaleRatioMul r hr
      (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)))
  have hmul := lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (measurable_suzukiHlogScaleRatio r)
    (Real.sqrt_nonneg (suzukiHlogScaleBound r))
    (norm_suzukiHlogScaleRatio_le hr)
    (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f))
  have hdil := dilation_ae r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)
  have hden := (densityMul_ae suzukiLogWeight measurable_suzukiLogWeight
    suzukiLogWeight_pos f).comp_tendsto
      (realMul_quasiMeasurePreserving r⁻¹ (inv_ne_zero hr.ne')).tendsto_ae
  filter_upwards [hdiv, hmul, hdil, hden] with x hdivx hmulx hdilx hdenx
  have hdivx' : (suzukiHlogFourierScaleCLM r hr f : ℝ → ℂ) x =
      (sqrtWeight suzukiLogWeight x)⁻¹ *
        (suzukiHlogScaleRatioMul r hr
          (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)) :
            SoninL2) x := by
    change ((suzukiHlogDensityUnitary.symm
      (suzukiHlogScaleRatioMul r hr
        (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f))) :
          SuzukiHlogFourierL2) : ℝ → ℂ) x = _
    rw [show suzukiHlogDensityUnitary.symm
        (suzukiHlogScaleRatioMul r hr
          (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f))) =
      densityDiv suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos
        (suzukiHlogScaleRatioMul r hr
          (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f))) by rfl]
    exact hdivx
  have hmulx' :
      (suzukiHlogScaleRatioMul r hr
        (dilationCLM r⁻¹ (inv_pos.mpr hr) (suzukiHlogDensityUnitary f)) :
          SoninL2) x =
        suzukiHlogScaleRatio r x *
          (dilationCLM r⁻¹ (inv_pos.mpr hr)
            (suzukiHlogDensityUnitary f) : SoninL2) x := by
    simpa only [suzukiHlogScaleRatioMul] using hmulx
  have hdilx' :
      (dilationCLM r⁻¹ (inv_pos.mpr hr)
        (suzukiHlogDensityUnitary f) : SoninL2) x =
        (Real.sqrt r⁻¹ : ℂ) * (suzukiHlogDensityUnitary f : SoninL2) (r⁻¹ * x) := by
    simpa only [dilationCLM_apply] using hdilx
  have hdenx' :
      (suzukiHlogDensityUnitary f : SoninL2) (r⁻¹ * x) =
        sqrtWeight suzukiLogWeight (r⁻¹ * x) * (f : ℝ → ℂ) (r⁻¹ * x) := by
    rw [show suzukiHlogDensityUnitary f =
      densityMul suzukiLogWeight measurable_suzukiLogWeight suzukiLogWeight_pos f by rfl]
    exact hdenx
  rw [hdivx', hmulx', hdilx']
  simp only [suzukiHlogScaleRatio, Function.comp_apply] at hdenx ⊢
  rw [hdenx']
  have hxpos := suzukiLogWeight_pos x
  have hrxpos := suzukiLogWeight_pos (r⁻¹ * x)
  unfold sqrtWeight
  rw [Real.sqrt_div (suzukiLogWeight_nonneg x)]
  push_cast
  field_simp [Real.sqrt_ne_zero'.mpr hxpos, Real.sqrt_ne_zero'.mpr hrxpos]
  have hxr : x / r = r⁻¹ * x := by field_simp [hr.ne']
  have hden0 : ((Real.sqrt (suzukiLogWeight (x / r)) : ℝ) : ℂ) ≠ 0 := by
    rw [hxr]
    exact_mod_cast Real.sqrt_ne_zero'.mpr hrxpos
  rw [div_eq_iff hden0]
  ring

theorem suzukiHlogFourierScaleCLM_inv_apply (r : ℝ) (hr : 0 < r)
    (f : SuzukiHlogFourierL2) :
    suzukiHlogFourierScaleCLM r⁻¹ (inv_pos.mpr hr)
      (suzukiHlogFourierScaleCLM r hr f) = f := by
  apply MeasureTheory.Lp.ext
  apply (withDensity_realDensity_ae_eq measurable_suzukiLogWeight
    suzukiLogWeight_pos).mpr
  have hout := (suzukiHlogFourierScaleCLM_ae r⁻¹ (inv_pos.mpr hr)
    (suzukiHlogFourierScaleCLM r hr f)).filter_mono
      (ae_mono volume_le_suzukiHlogMeasure)
  have hin0 := (suzukiHlogFourierScaleCLM_ae r hr f).filter_mono
    (ae_mono volume_le_suzukiHlogMeasure)
  have hin := hin0.comp_tendsto
    (realMul_quasiMeasurePreserving (r⁻¹)⁻¹
      (inv_ne_zero (inv_ne_zero hr.ne'))).tendsto_ae
  filter_upwards [hout, hin] with x houtx hinx
  rw [houtx]
  simp only [Function.comp_apply] at hinx
  rw [hinx]
  have hsqrt : (Real.sqrt (r⁻¹)⁻¹ : ℂ) * (Real.sqrt r⁻¹ : ℂ) = 1 := by
    norm_cast
    rw [inv_inv]
    exact sqrt_mul_sqrt_inv r hr
  rw [← mul_assoc, hsqrt, one_mul]
  field_simp [hr.ne']

def suzukiHlogFourierScaleEquiv (r : ℝ) (hr : 0 < r) :
    SuzukiHlogFourierL2 ≃L[ℂ] SuzukiHlogFourierL2 where
  toLinearEquiv :=
    { toFun := suzukiHlogFourierScaleCLM r hr
      invFun := suzukiHlogFourierScaleCLM r⁻¹ (inv_pos.mpr hr)
      left_inv := suzukiHlogFourierScaleCLM_inv_apply r hr
      right_inv := by
        intro f
        simpa using suzukiHlogFourierScaleCLM_inv_apply r⁻¹ (inv_pos.mpr hr) f
      map_add' := (suzukiHlogFourierScaleCLM r hr).map_add
      map_smul' := (suzukiHlogFourierScaleCLM r hr).map_smul }
  continuous_toFun := (suzukiHlogFourierScaleCLM r hr).continuous
  continuous_invFun := (suzukiHlogFourierScaleCLM r⁻¹ (inv_pos.mpr hr)).continuous

theorem suzukiHlogWeightedToL2_fourierScale (r : ℝ) (hr : 0 < r)
    (f : SuzukiHlogFourierL2) :
    suzukiHlogWeightedToL2 (suzukiHlogFourierScaleCLM r hr f) =
      dilation r⁻¹ (inv_pos.mpr hr) (suzukiHlogWeightedToL2 f) := by
  apply MeasureTheory.Lp.ext
  have hleft := (suzukiHlogWeightedToL2_coeFn
    (suzukiHlogFourierScaleCLM r hr f)).trans
      ((suzukiHlogFourierScaleCLM_ae r hr f).filter_mono
        (ae_mono volume_le_suzukiHlogMeasure))
  have hright := dilation_ae r⁻¹ (inv_pos.mpr hr) (suzukiHlogWeightedToL2 f)
  have hf := (suzukiHlogWeightedToL2_coeFn f).comp_tendsto
    (realMul_quasiMeasurePreserving r⁻¹ (inv_ne_zero hr.ne')).tendsto_ae
  filter_upwards [hleft, hright, hf] with x hl hrx hfx
  rw [hl, hrx]
  simp only [Function.comp_apply] at hfx
  rw [hfx]

theorem suzukiHlogFourierToTime_fourierScale (r : ℝ) (hr : 0 < r)
    (f : SuzukiHlogFourierL2) :
    suzukiHlogFourierToTime (suzukiHlogFourierScaleCLM r hr f) =
      dilation r hr (suzukiHlogFourierToTime f) := by
  apply fourierUnitary.injective
  rw [fourierUnitary_suzukiHlogFourierToTime,
    suzukiHlogWeightedToL2_fourierScale,
    fourierUnitary_dilation,
    fourierUnitary_suzukiHlogFourierToTime]

/-- Normalized dilation from the complete unit-aperture logarithmic form domain to aperture `a`. -/
def suzukiHlogUnitToSmallFormCLM (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiHlogFormDomain suzukiLimitingUnitAperture →L[ℂ]
      SuzukiHlogFormDomain (smallPositiveAperture a) :=
  ((suzukiHlogFourierScaleCLM (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a))).domRestrict
    (suzukiHlogSupportDefect suzukiLimitingUnitAperture).ker).codRestrict
      (suzukiHlogSupportDefect (smallPositiveAperture a)).ker fun f => by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval (smallValue a))
      (measurableSet_centralInterval (smallValue a)))
        (suzukiHlogFourierToTime
          (suzukiHlogFourierScaleCLM (smallValue a)⁻¹
            (inv_pos.mpr (smallValue_pos a)) f.1)) = 0
    rw [suzukiHlogFourierToTime_fourierScale, sub_apply, one_apply_eq_self,
      sub_eq_zero, indicatorCutoff_dilation]
    apply congrArg (dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)))
    have hfix := indicatorCutoff_suzukiHlogFormEmbedding
      suzukiLimitingUnitAperture f
    change indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1 at hfix
    simpa [smallPositiveAperture, (smallValue_pos a).ne'] using hfix.symm

/-- Inverse normalized dilation from aperture `a` to the unit aperture. -/
def suzukiHlogSmallToUnitFormCLM (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiHlogFormDomain (smallPositiveAperture a) →L[ℂ]
      SuzukiHlogFormDomain suzukiLimitingUnitAperture :=
  ((suzukiHlogFourierScaleCLM (smallValue a) (smallValue_pos a)).domRestrict
    (suzukiHlogSupportDefect (smallPositiveAperture a)).ker).codRestrict
      (suzukiHlogSupportDefect suzukiLimitingUnitAperture).ker fun f => by
    rw [LinearMap.mem_ker]
    change (1 - indicatorCutoff (centralInterval 1)
      (measurableSet_centralInterval 1))
        (suzukiHlogFourierToTime
          (suzukiHlogFourierScaleCLM (smallValue a) (smallValue_pos a) f.1)) = 0
    rw [suzukiHlogFourierToTime_fourierScale, sub_apply, one_apply_eq_self,
      sub_eq_zero, indicatorCutoff_dilation]
    apply congrArg (dilation (smallValue a) (smallValue_pos a))
    have hfix := indicatorCutoff_suzukiHlogFormEmbedding (smallPositiveAperture a) f
    change indicatorCutoff (centralInterval (smallValue a))
      (measurableSet_centralInterval (smallValue a))
      (suzukiHlogFourierToTime f.1) = suzukiHlogFourierToTime f.1 at hfix
    simpa using hfix.symm

theorem suzukiHlogSmallToUnit_unitToSmall
    (a : SuzukiPrimeFreeSmallAperture)
    (f : SuzukiHlogFormDomain suzukiLimitingUnitAperture) :
    suzukiHlogSmallToUnitFormCLM a (suzukiHlogUnitToSmallFormCLM a f) = f := by
  apply Subtype.ext
  change suzukiHlogFourierScaleCLM (smallValue a) (smallValue_pos a)
      (suzukiHlogFourierScaleCLM (smallValue a)⁻¹
        (inv_pos.mpr (smallValue_pos a)) f.1) = f.1
  simpa using suzukiHlogFourierScaleCLM_inv_apply (smallValue a)⁻¹
    (inv_pos.mpr (smallValue_pos a)) f.1

theorem suzukiHlogUnitToSmall_smallToUnit
    (a : SuzukiPrimeFreeSmallAperture)
    (f : SuzukiHlogFormDomain (smallPositiveAperture a)) :
    suzukiHlogUnitToSmallFormCLM a (suzukiHlogSmallToUnitFormCLM a f) = f := by
  apply Subtype.ext
  change suzukiHlogFourierScaleCLM (smallValue a)⁻¹
      (inv_pos.mpr (smallValue_pos a))
      (suzukiHlogFourierScaleCLM (smallValue a) (smallValue_pos a) f.1) = f.1
  exact suzukiHlogFourierScaleCLM_inv_apply (smallValue a) (smallValue_pos a) f.1

def suzukiHlogUnitSmallFormEquiv (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiHlogFormDomain suzukiLimitingUnitAperture ≃L[ℂ]
      SuzukiHlogFormDomain (smallPositiveAperture a) where
  toLinearEquiv :=
    { toFun := suzukiHlogUnitToSmallFormCLM a
      invFun := suzukiHlogSmallToUnitFormCLM a
      left_inv := suzukiHlogSmallToUnit_unitToSmall a
      right_inv := suzukiHlogUnitToSmall_smallToUnit a
      map_add' := (suzukiHlogUnitToSmallFormCLM a).map_add
      map_smul' := (suzukiHlogUnitToSmallFormCLM a).map_smul }
  continuous_toFun := (suzukiHlogUnitToSmallFormCLM a).continuous
  continuous_invFun := (suzukiHlogSmallToUnitFormCLM a).continuous

/-- Complete CCM form domains at apertures `1` and `a` are exactly related by normalized dilation. -/
def ccmArchimedeanUnitSmallFormEquiv (a : SuzukiPrimeFreeSmallAperture) :
    CCMArchimedeanFormDomain suzukiLimitingUnitAperture ≃L[ℂ]
      CCMArchimedeanFormDomain (smallPositiveAperture a) :=
  (ccmArchimedeanLogFormDomainEquiv suzukiLimitingUnitAperture).symm.trans
    ((suzukiHlogUnitSmallFormEquiv a).trans
      (ccmArchimedeanLogFormDomainEquiv (smallPositiveAperture a)))

theorem ccmArchimedeanUnitSmallFormEquiv_time
    (a : SuzukiPrimeFreeSmallAperture)
    (f : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    ccmArchimedeanFormEmbedding (smallPositiveAperture a)
        (ccmArchimedeanUnitSmallFormEquiv a f) =
      dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a))
        (ccmArchimedeanFormEmbedding suzukiLimitingUnitAperture f) := by
  change ccmArchimedeanFourierToTime
      (ccmLogToArchimedean
        (suzukiHlogUnitToSmallFormCLM a
          (ccmArchimedeanFormToLog suzukiLimitingUnitAperture f))) = _
  rw [ccmArchimedeanFourierToTime_logToArchimedean]
  change suzukiHlogFourierToTime
      (suzukiHlogFourierScaleCLM (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a))
        (ccmArchimedeanFormToLog suzukiLimitingUnitAperture f).1) = _
  rw [suzukiHlogFourierToTime_fourierScale]
  congr 1
  exact suzukiHlogFourierToTime_archimedeanToLog f.1

/-- Normalized physical dilation from unit aperture to `a`. -/
def suzukiPhysicalUnitToSmallIsometry (a : SuzukiPrimeFreeSmallAperture) :
    suzukiApertureHilbert suzukiLimitingUnitAperture →ₗᵢ[ℂ]
      suzukiApertureHilbert (smallPositiveAperture a) where
  toFun f := ⟨dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)) f.1, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    refine ⟨dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)) f.1, ?_⟩
    change indicatorCutoff (centralInterval (smallValue a))
      (measurableSet_centralInterval (smallValue a))
        (dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)) f.1) =
      dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)) f.1
    rw [indicatorCutoff_dilation]
    have hfix := indicatorCutoff_suzukiApertureHilbert suzukiLimitingUnitAperture f
    change indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1) f.1 = f.1
      at hfix
    rw [show (smallValue a)⁻¹ * smallValue a = 1 by
      exact inv_mul_cancel₀ (smallValue_pos a).ne']
    rw [hfix]⟩
  map_add' f g := Subtype.ext (map_add _ f.1 g.1)
  map_smul' c f := Subtype.ext (map_smul _ c f.1)
  norm_map' f := (dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a))).norm_map f.1

/-- Inverse normalized physical dilation from aperture `a` to the unit aperture. -/
def suzukiPhysicalSmallToUnitIsometry (a : SuzukiPrimeFreeSmallAperture) :
    suzukiApertureHilbert (smallPositiveAperture a) →ₗᵢ[ℂ]
      suzukiApertureHilbert suzukiLimitingUnitAperture where
  toFun f := ⟨dilation (smallValue a) (smallValue_pos a) f.1, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    refine ⟨dilation (smallValue a) (smallValue_pos a) f.1, ?_⟩
    change indicatorCutoff (centralInterval 1) (measurableSet_centralInterval 1)
        (dilation (smallValue a) (smallValue_pos a) f.1) =
      dilation (smallValue a) (smallValue_pos a) f.1
    rw [indicatorCutoff_dilation]
    have hfix := indicatorCutoff_suzukiApertureHilbert (smallPositiveAperture a) f
    change indicatorCutoff (centralInterval (smallValue a))
      (measurableSet_centralInterval (smallValue a)) f.1 = f.1 at hfix
    simpa using congrArg (dilation (smallValue a) (smallValue_pos a)) hfix⟩
  map_add' f g := Subtype.ext (map_add _ f.1 g.1)
  map_smul' c f := Subtype.ext (map_smul _ c f.1)
  norm_map' f := (dilation (smallValue a) (smallValue_pos a)).norm_map f.1

theorem suzukiPhysicalSmallToUnit_unitToSmall
    (a : SuzukiPrimeFreeSmallAperture)
    (f : suzukiApertureHilbert suzukiLimitingUnitAperture) :
    suzukiPhysicalSmallToUnitIsometry a (suzukiPhysicalUnitToSmallIsometry a f) = f := by
  apply Subtype.ext
  change dilation (smallValue a) (smallValue_pos a)
      (dilation (smallValue a)⁻¹ (inv_pos.mpr (smallValue_pos a)) f.1) = f.1
  exact dilation_dilation_inv (smallValue a) (smallValue_pos a) f.1

theorem suzukiPhysicalUnitToSmall_smallToUnit
    (a : SuzukiPrimeFreeSmallAperture)
    (f : suzukiApertureHilbert (smallPositiveAperture a)) :
    suzukiPhysicalUnitToSmallIsometry a (suzukiPhysicalSmallToUnitIsometry a f) = f := by
  apply Subtype.ext
  exact dilation_inv_dilation (smallValue a) (smallValue_pos a) f.1

def suzukiPhysicalUnitSmallEquiv (a : SuzukiPrimeFreeSmallAperture) :
    suzukiApertureHilbert suzukiLimitingUnitAperture ≃ₗᵢ[ℂ]
      suzukiApertureHilbert (smallPositiveAperture a) where
  toFun := suzukiPhysicalUnitToSmallIsometry a
  invFun := suzukiPhysicalSmallToUnitIsometry a
  left_inv := suzukiPhysicalSmallToUnit_unitToSmall a
  right_inv := suzukiPhysicalUnitToSmall_smallToUnit a
  map_add' := (suzukiPhysicalUnitToSmallIsometry a).map_add
  map_smul' := (suzukiPhysicalUnitToSmallIsometry a).map_smul
  norm_map' := (suzukiPhysicalUnitToSmallIsometry a).norm_map

/-- Literal interval-coordinate normalized aperture unitary. -/
def suzukiIntervalUnitSmallEquiv (a : SuzukiPrimeFreeSmallAperture) :
    SuzukiApertureIntervalL2 1 ≃ₗᵢ[ℂ] SuzukiApertureIntervalL2 (smallValue a) :=
  (suzukiApertureL2Equiv suzukiLimitingUnitAperture).trans
    ((suzukiPhysicalUnitSmallEquiv a).trans
      (suzukiApertureL2Equiv (smallPositiveAperture a)).symm)

theorem ccmArchimedeanUnitSmallFormEquiv_embedding
    (a : SuzukiPrimeFreeSmallAperture)
    (f : CCMArchimedeanFormDomain suzukiLimitingUnitAperture) :
    suzukiPhysicalUnitSmallEquiv a
        (ccmArchimedeanFormToAperture suzukiLimitingUnitAperture f) =
      ccmArchimedeanFormToAperture (smallPositiveAperture a)
        (ccmArchimedeanUnitSmallFormEquiv a f) := by
  apply Subtype.ext
  exact (ccmArchimedeanUnitSmallFormEquiv_time a f).symm

end RHTower
