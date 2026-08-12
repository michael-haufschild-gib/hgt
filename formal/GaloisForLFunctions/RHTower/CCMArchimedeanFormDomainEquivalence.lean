import GaloisForLFunctions.RHTower.CCMArchimedeanLogWeightEquivalence

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology

noncomputable section

namespace RHTower

private def ccmLogToArchimedeanReal :
    SuzukiHlogFourierL2 →L[ℝ] CCMArchimedeanFourierL2 :=
  MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    ccmArchimedeanLogComparisonENNReal_ne_top
    ccmArchimedeanFormMeasure_le_logComparison_smul

theorem ccmLogToArchimedeanReal_coeFn (f : SuzukiHlogFourierL2) :
    ccmLogToArchimedeanReal f =ᵐ[ccmArchimedeanFormMeasure] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    ccmArchimedeanLogComparisonENNReal_ne_top
    ccmArchimedeanFormMeasure_le_logComparison_smul f

private def ccmLogToArchimedeanLinear :
    SuzukiHlogFourierL2 →ₗ[ℂ] CCMArchimedeanFourierL2 where
  toFun := ccmLogToArchimedeanReal
  map_add' := ccmLogToArchimedeanReal.map_add
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have hac : ccmArchimedeanFormMeasure ≪ suzukiHlogMeasure :=
      Measure.absolutelyContinuous_of_le_smul
        ccmArchimedeanFormMeasure_le_logComparison_smul
    have hsmul_in := hac.ae_eq (MeasureTheory.Lp.coeFn_smul c f)
    filter_upwards [ccmLogToArchimedeanReal_coeFn (c • f),
      ccmLogToArchimedeanReal_coeFn f, hsmul_in,
      MeasureTheory.Lp.coeFn_smul c (ccmLogToArchimedeanReal f)] with
        xi hcf hff hin hout
    change (ccmLogToArchimedeanReal (c • f) : ℝ → ℂ) xi =
      (c • ccmLogToArchimedeanReal f : CCMArchimedeanFourierL2) xi
    rw [hcf, hout, hin]
    change c * f xi = c * (ccmLogToArchimedeanReal f : ℝ → ℂ) xi
    rw [hff]

def ccmLogToArchimedean :
    SuzukiHlogFourierL2 →L[ℂ] CCMArchimedeanFourierL2 :=
  LinearMap.mkContinuous ccmLogToArchimedeanLinear ‖ccmLogToArchimedeanReal‖ fun f => by
    change ‖ccmLogToArchimedeanReal f‖ ≤ ‖ccmLogToArchimedeanReal‖ * ‖f‖
    exact ccmLogToArchimedeanReal.le_opNorm f

theorem ccmLogToArchimedean_coeFn (f : SuzukiHlogFourierL2) :
    ccmLogToArchimedean f =ᵐ[ccmArchimedeanFormMeasure] f :=
  ccmLogToArchimedeanReal_coeFn f

private def ccmArchimedeanToLogReal :
    CCMArchimedeanFourierL2 →L[ℝ] SuzukiHlogFourierL2 :=
  MeasureTheory.Lp.LpToLpOfMeasureLeSMul
    ccmArchimedeanLogComparisonENNReal_ne_top
    suzukiHlogMeasure_le_ccmArchimedeanComparison_smul

theorem ccmArchimedeanToLogReal_coeFn (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanToLogReal f =ᵐ[suzukiHlogMeasure] f :=
  MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul
    ccmArchimedeanLogComparisonENNReal_ne_top
    suzukiHlogMeasure_le_ccmArchimedeanComparison_smul f

private def ccmArchimedeanToLogLinear :
    CCMArchimedeanFourierL2 →ₗ[ℂ] SuzukiHlogFourierL2 where
  toFun := ccmArchimedeanToLogReal
  map_add' := ccmArchimedeanToLogReal.map_add
  map_smul' c f := by
    apply MeasureTheory.Lp.ext
    have hac : suzukiHlogMeasure ≪ ccmArchimedeanFormMeasure :=
      Measure.absolutelyContinuous_of_le_smul
        suzukiHlogMeasure_le_ccmArchimedeanComparison_smul
    have hsmul_in := hac.ae_eq (MeasureTheory.Lp.coeFn_smul c f)
    filter_upwards [ccmArchimedeanToLogReal_coeFn (c • f),
      ccmArchimedeanToLogReal_coeFn f, hsmul_in,
      MeasureTheory.Lp.coeFn_smul c (ccmArchimedeanToLogReal f)] with
        xi hcf hff hin hout
    change (ccmArchimedeanToLogReal (c • f) : ℝ → ℂ) xi =
      (c • ccmArchimedeanToLogReal f : SuzukiHlogFourierL2) xi
    rw [hcf, hout, hin]
    change c * f xi = c * (ccmArchimedeanToLogReal f : ℝ → ℂ) xi
    rw [hff]

def ccmArchimedeanToLog :
    CCMArchimedeanFourierL2 →L[ℂ] SuzukiHlogFourierL2 :=
  LinearMap.mkContinuous ccmArchimedeanToLogLinear ‖ccmArchimedeanToLogReal‖ fun f => by
    change ‖ccmArchimedeanToLogReal f‖ ≤ ‖ccmArchimedeanToLogReal‖ * ‖f‖
    exact ccmArchimedeanToLogReal.le_opNorm f

theorem ccmArchimedeanToLog_coeFn (f : CCMArchimedeanFourierL2) :
    ccmArchimedeanToLog f =ᵐ[suzukiHlogMeasure] f :=
  ccmArchimedeanToLogReal_coeFn f

theorem ccmArchimedeanToLog_logToArchimedean (f : SuzukiHlogFourierL2) :
    ccmArchimedeanToLog (ccmLogToArchimedean f) = f := by
  apply MeasureTheory.Lp.ext
  have hac : suzukiHlogMeasure ≪ ccmArchimedeanFormMeasure :=
    Measure.absolutelyContinuous_of_le_smul
      suzukiHlogMeasure_le_ccmArchimedeanComparison_smul
  have hforward := hac.ae_eq (ccmLogToArchimedean_coeFn f)
  filter_upwards [ccmArchimedeanToLog_coeFn (ccmLogToArchimedean f), hforward]
    with xi hback hforward
  rw [hback, hforward]

theorem ccmLogToArchimedean_archimedeanToLog (f : CCMArchimedeanFourierL2) :
    ccmLogToArchimedean (ccmArchimedeanToLog f) = f := by
  apply MeasureTheory.Lp.ext
  have hac : ccmArchimedeanFormMeasure ≪ suzukiHlogMeasure :=
    Measure.absolutelyContinuous_of_le_smul
      ccmArchimedeanFormMeasure_le_logComparison_smul
  have hback := hac.ae_eq (ccmArchimedeanToLog_coeFn f)
  filter_upwards [ccmLogToArchimedean_coeFn (ccmArchimedeanToLog f), hback]
    with xi hforward hback
  rw [hforward, hback]

def ccmArchimedeanLogFourierEquiv :
    SuzukiHlogFourierL2 ≃L[ℂ] CCMArchimedeanFourierL2 where
  toLinearEquiv :=
    { toFun := ccmLogToArchimedean
      invFun := ccmArchimedeanToLog
      left_inv := ccmArchimedeanToLog_logToArchimedean
      right_inv := ccmLogToArchimedean_archimedeanToLog
      map_add' := ccmLogToArchimedean.map_add
      map_smul' := ccmLogToArchimedean.map_smul }
  continuous_toFun := ccmLogToArchimedean.continuous
  continuous_invFun := ccmArchimedeanToLog.continuous

theorem ccmArchimedeanWeightedToL2_logToArchimedean
    (f : SuzukiHlogFourierL2) :
    ccmArchimedeanWeightedToL2 (ccmLogToArchimedean f) =
      suzukiHlogWeightedToL2 f := by
  apply MeasureTheory.Lp.ext
  have hforward := (ccmLogToArchimedean_coeFn f).filter_mono
    (ae_mono volume_le_ccmArchimedeanFormMeasure)
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn (ccmLogToArchimedean f),
    hforward, suzukiHlogWeightedToL2_coeFn f] with xi hex hforward hlog
  rw [hex, hforward, hlog]

theorem ccmArchimedeanFourierToTime_logToArchimedean
    (f : SuzukiHlogFourierL2) :
    ccmArchimedeanFourierToTime (ccmLogToArchimedean f) =
      suzukiHlogFourierToTime f := by
  apply fourierUnitary.injective
  rw [fourierUnitary_ccmArchimedeanFourierToTime,
    fourierUnitary_suzukiHlogFourierToTime,
    ccmArchimedeanWeightedToL2_logToArchimedean]

theorem suzukiHlogFourierToTime_archimedeanToLog
    (f : CCMArchimedeanFourierL2) :
    suzukiHlogFourierToTime (ccmArchimedeanToLog f) =
      ccmArchimedeanFourierToTime f := by
  calc
    suzukiHlogFourierToTime (ccmArchimedeanToLog f) =
        ccmArchimedeanFourierToTime
          (ccmLogToArchimedean (ccmArchimedeanToLog f)) :=
      (ccmArchimedeanFourierToTime_logToArchimedean
        (ccmArchimedeanToLog f)).symm
    _ = ccmArchimedeanFourierToTime f := by
      rw [ccmLogToArchimedean_archimedeanToLog]

theorem ccmArchimedeanSupportDefect_logToArchimedean
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFourierL2) :
    ccmArchimedeanSupportDefect a (ccmLogToArchimedean f) =
      suzukiHlogSupportDefect a f := by
  change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (ccmArchimedeanFourierToTime (ccmLogToArchimedean f)) =
    (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (suzukiHlogFourierToTime f)
  rw [ccmArchimedeanFourierToTime_logToArchimedean]

theorem suzukiHlogSupportDefect_archimedeanToLog
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFourierL2) :
    suzukiHlogSupportDefect a (ccmArchimedeanToLog f) =
      ccmArchimedeanSupportDefect a f := by
  change (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1))
        (suzukiHlogFourierToTime (ccmArchimedeanToLog f)) =
    (1 - indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1)) (ccmArchimedeanFourierToTime f)
  rw [suzukiHlogFourierToTime_archimedeanToLog]

def ccmLogFormToArchimedean (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a →L[ℂ] CCMArchimedeanFormDomain a :=
  (ccmLogToArchimedean.domRestrict (suzukiHlogSupportDefect a).ker).codRestrict
    (ccmArchimedeanSupportDefect a).ker fun f => by
      rw [LinearMap.mem_ker]
      change ccmArchimedeanSupportDefect a (ccmLogToArchimedean f.1) = 0
      rw [ccmArchimedeanSupportDefect_logToArchimedean]
      exact LinearMap.mem_ker.mp f.property

def ccmArchimedeanFormToLog (a : SuzukiPositiveAperture) :
    CCMArchimedeanFormDomain a →L[ℂ] SuzukiHlogFormDomain a :=
  (ccmArchimedeanToLog.domRestrict (ccmArchimedeanSupportDefect a).ker).codRestrict
    (suzukiHlogSupportDefect a).ker fun f => by
      rw [LinearMap.mem_ker]
      change suzukiHlogSupportDefect a (ccmArchimedeanToLog f.1) = 0
      rw [suzukiHlogSupportDefect_archimedeanToLog]
      exact LinearMap.mem_ker.mp f.property

theorem ccmArchimedeanFormToLog_logFormToArchimedean
    (a : SuzukiPositiveAperture) (f : SuzukiHlogFormDomain a) :
    ccmArchimedeanFormToLog a (ccmLogFormToArchimedean a f) = f := by
  apply Subtype.ext
  exact ccmArchimedeanToLog_logToArchimedean f.1

theorem ccmLogFormToArchimedean_archimedeanFormToLog
    (a : SuzukiPositiveAperture) (f : CCMArchimedeanFormDomain a) :
    ccmLogFormToArchimedean a (ccmArchimedeanFormToLog a f) = f := by
  apply Subtype.ext
  exact ccmLogToArchimedean_archimedeanToLog f.1

def ccmArchimedeanLogFormDomainEquiv (a : SuzukiPositiveAperture) :
    SuzukiHlogFormDomain a ≃L[ℂ] CCMArchimedeanFormDomain a where
  toLinearEquiv :=
    { toFun := ccmLogFormToArchimedean a
      invFun := ccmArchimedeanFormToLog a
      left_inv := ccmArchimedeanFormToLog_logFormToArchimedean a
      right_inv := ccmLogFormToArchimedean_archimedeanFormToLog a
      map_add' := (ccmLogFormToArchimedean a).map_add
      map_smul' := (ccmLogFormToArchimedean a).map_smul }
  continuous_toFun := (ccmLogFormToArchimedean a).continuous
  continuous_invFun := (ccmArchimedeanFormToLog a).continuous

end RHTower
