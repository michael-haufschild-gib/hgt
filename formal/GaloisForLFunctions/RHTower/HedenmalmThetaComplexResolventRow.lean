import GaloisForLFunctions.RHTower.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.HedenmalmShiftedCokernel

/-!
# All-complex theta resolvent row

The exact translated cokernel conormal gives the mean row of every invertible complex theta
source pencil.  This avoids a separate singular-endpoint integration argument: subtracting the
mean places the resolvent solution in the translated centered range, whose orthogonal complement
is the explicit exponential conormal.
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative
  HedenmalmFredholmRange

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

local instance factTwoNeTopThetaComplexResolventRow : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Complex source resolvent at an arbitrary invertible pencil point. -/
def thetaComplexResolvent (z : ℂ) : ThetaH →L[ℂ] ThetaH :=
  Ring.inverse (thetaSourcePencil z)

/-- Source character paired against a quantile-space vector. -/
def thetaComplexResolventMoment (z : ℂ) (f : ThetaH) : ℂ :=
  ∫ t, sourceChar z (thetaSource.quantileFun t) * f t ∂unitIntervalMeasure

/-- The full compact source inverse kills the constant boundary vector. -/
theorem thetaKernelOperator_pinnedOne : thetaKernelOperator pinnedOne = 0 := by
  have hGinj : Function.Injective thetaMetricOperator :=
    metricOperator_injective thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le
  apply hGinj
  have h := congrArg (fun T : ThetaH →L[ℂ] ThetaH => T pinnedOne)
    thetaMetricOperator_mul_thetaKernelOperator
  simpa only [ContinuousLinearMap.mul_apply, pinnedVolterraCLM_pinnedOne,
    map_zero, ContinuousLinearMap.smul_apply, smul_zero] using h

/-- The translated cokernel conormal is the exponential source character in quantile space. -/
theorem thetaCokernelVector_ae_sourceChar (z : ℂ) :
    (fun t => thetaCokernelVector z t) =ᵐ[unitIntervalMeasure]
      fun t => (Real.sqrt thetaSource.mass : ℂ) *
        sourceChar (-(starRingEnd ℂ) z) (thetaSource.quantileFun t) := by
  let w := thetaCokernelSourceVector z
  have hunit := quantileUnitary_ae thetaSource w
  have hwWeighted := thetaCokernelSourceVector_ae z
  have hwLeb : (fun x => w x) =ᵐ[(volume : Measure ℝ)]
      cokernelVector thetaSource z :=
    (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq
      (measurable_sourceWeight thetaSource) (sourceWeight_pos thetaSource)).mp hwWeighted
  have hwLaw : (fun x => w x) =ᵐ[thetaSource.law]
      cokernelVector thetaSource z := (thetaSource.law_ae_eq).mpr hwLeb
  have hwQuantile := hwLaw.comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hunit, hwQuantile] with t hu hw
  change (quantileUnitary thetaSource w : ThetaH) t = _
  rw [hu]
  change w (thetaSource.quantileFun t) =
    cokernelVector thetaSource z (thetaSource.quantileFun t) at hw
  rw [hw, cokernelVector_eq_k_mul_sourceChar]
  have hk : (thetaSource.k (thetaSource.quantileFun t) : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.pos_k _).ne'
  field_simp

/-- Pairing with the translated conormal is exactly the all-complex source-character moment. -/
theorem inner_thetaCokernelVector_eq_complexMoment (z : ℂ) (f : ThetaH) :
    inner ℂ (thetaCokernelVector z) f =
      (Real.sqrt thetaSource.mass : ℂ) * thetaComplexResolventMoment z f := by
  rw [inner_lp_eq]
  rw [thetaComplexResolventMoment, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [thetaCokernelVector_ae_sourceChar z] with t ht
  have hchar : (starRingEnd ℂ)
      (sourceChar (-(starRingEnd ℂ) z) (thetaSource.quantileFun t)) =
      sourceChar z (thetaSource.quantileFun t) := by
    rw [sourceChar, sourceChar, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  rw [ht, map_mul, Complex.conj_ofReal, hchar]
  ring

/-- Character moment of the constant vector is the normalized completed theta transform. -/
theorem thetaComplexResolventMoment_pinnedOne (z : ℂ) :
    thetaComplexResolventMoment z pinnedOne = rootA thetaSource z 1 := by
  rw [thetaComplexResolventMoment]
  calc
    (∫ t, sourceChar z (thetaSource.quantileFun t) * pinnedOne t
        ∂unitIntervalMeasure) =
        ∫ t, sourceChar z (thetaSource.quantileFun t) ∂unitIntervalMeasure := by
          apply integral_congr_ae
          filter_upwards [pinnedOne_coeFn] with t ht
          rw [ht, mul_one]
    _ = rootA thetaSource z 1 := by
      have hres : unitIntervalMeasure =
          (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1) := by
        rw [unitIntervalMeasure, restrict_Ioo_eq_restrict_Icc]
      rw [hres,
        rootA, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        setIntegral_congr_set (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)]

/-- Invertibility of the source pencil excludes vanishing of its scalar source transform. -/
theorem rootA_one_ne_zero_of_sourcePencil_isUnit {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) :
    rootA thetaSource z 1 ≠ 0 := by
  have hXi : XiC z ≠ 0 := by
    intro hzero
    exact (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).2 hzero hz
  rw [rootA_one, xiC_thetaSource_all]
  exact div_ne_zero hXi (by exact_mod_cast thetaSource.mass_ne_zero)

/-- Exact all-complex mean row of the inverse source pencil. -/
theorem pinnedMean_thetaComplexResolvent_eq {z : ℂ}
    (hz : IsUnit (thetaSourcePencil z)) (f : ThetaH) :
    pinnedMean (thetaComplexResolvent z f) =
      thetaComplexResolventMoment z f / rootA thetaSource z 1 := by
  let g : ThetaH := thetaComplexResolvent z f
  let m : ℂ := pinnedMean g
  let k : thetaCentered := ⟨g - m • pinnedOne, by
    rw [mem_thetaCentered_iff]
    calc
      pinnedMean (g - m • pinnedOne) =
          thetaPinnedMeanCLM (g - m • pinnedOne) :=
        (thetaPinnedMeanCLM_apply _).symm
      _ = 0 := by
        rw [map_sub, map_smul, thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply,
          pinnedMean_pinnedOne]
        simpa only [m, smul_eq_mul, mul_one, sub_self]⟩
  have hpencil : thetaSourcePencil z * thetaComplexResolvent z = 1 :=
    Ring.mul_inverse_cancel _ hz
  have hresolvent : g + z • thetaKernelOperator g = f := by
    have h := congrArg (fun T : ThetaH →L[ℂ] ThetaH => T f) hpencil
    simpa only [thetaSourcePencil, thetaComplexResolvent, g,
      ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply] using h
  have hcenteredInverse : thetaCenteredSourceInverse k = thetaKernelOperator g := by
    rw [thetaCenteredSourceInverse, ContinuousLinearMap.comp_apply]
    change thetaCompactSourceInverse (g - m • pinnedOne) = thetaKernelOperator g
    rw [map_sub, map_smul, ← thetaKernelOperator_eq_thetaCompactSourceInverse,
      thetaKernelOperator_pinnedOne, smul_zero, sub_zero]
  have hrange : thetaShiftedRangeMap z k = f - m • pinnedOne := by
    rw [thetaShiftedRangeMap_apply, hcenteredInverse]
    change (g - m • pinnedOne) + z • thetaKernelOperator g = f - m • pinnedOne
    rw [← hresolvent]
    module
  have hmem : f - m • pinnedOne ∈ (ℂ ∙ thetaCokernelVector z)ᗮ := by
    rw [← thetaShiftedRangeMap_range_eq_orthogonal z]
    exact ⟨k, hrange⟩
  have horth : inner ℂ (thetaCokernelVector z) (f - m • pinnedOne) = 0 := by
    exact (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem)
  rw [inner_sub_right, inner_smul_right,
    inner_thetaCokernelVector_eq_complexMoment,
    inner_thetaCokernelVector_eq_complexMoment,
    thetaComplexResolventMoment_pinnedOne] at horth
  have hsqrt : (Real.sqrt thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr thetaSource.mass_pos).ne'
  have hscalar : thetaComplexResolventMoment z f -
      m * rootA thetaSource z 1 = 0 := by
    have hfactored : (Real.sqrt thetaSource.mass : ℂ) *
        (thetaComplexResolventMoment z f - m * rootA thetaSource z 1) = 0 := by
      calc
        (Real.sqrt thetaSource.mass : ℂ) *
            (thetaComplexResolventMoment z f - m * rootA thetaSource z 1) =
            (Real.sqrt thetaSource.mass : ℂ) * thetaComplexResolventMoment z f -
              m * ((Real.sqrt thetaSource.mass : ℂ) * rootA thetaSource z 1) := by ring
        _ = 0 := horth
    exact (mul_eq_zero.mp hfactored).resolve_left hsqrt
  apply (eq_div_iff (rootA_one_ne_zero_of_sourcePencil_isUnit hz)).2
  change m * rootA thetaSource z 1 = thetaComplexResolventMoment z f
  exact (sub_eq_zero.mp hscalar).symm

end

end RHTower.HedenmalmThetaSource
