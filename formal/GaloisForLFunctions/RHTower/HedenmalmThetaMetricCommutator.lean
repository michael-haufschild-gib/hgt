import GaloisForLFunctions.RHTower.HedenmalmThetaCompactFluxEnergy

/-!
# Singular theta metric commutator

The canonical metric `G = M_{1/q}` exactly cancels quantile speed in compact theta source inverse
`B = i M_q V`.  Its entire failure of metric skew-adjointness is rank-two pinned boundary form:

`G B - B† G = i C`.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

open HedenmalmQuantile HedenmalmThetaSource

/-- Singular metric cancels quantile speed of theta source inverse exactly. -/
theorem thetaMetricOperator_mul_thetaKernelOperator :
    thetaMetricOperator * thetaKernelOperator =
      Complex.I • pinnedVolterraCLM := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply]
  apply Lp.ext
  have hV := pinnedVolterra_coeFn f
  change (fun t => (pinnedVolterraCLM f) t) =ᵐ[unitIntervalMeasure]
    pinnedVolterraFun f at hV
  filter_upwards
      [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le (thetaKernelOperator f),
       pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f,
       hV, Lp.coeFn_smul Complex.I (pinnedVolterraCLM f)]
    with t hG hB hVt hsmul
  rw [hG, hB, hsmul, hVt,
    pinnedKernelField_apply_eq_pinnedVolterraFun,
    metricSymbol_eq_inv_quantileSpeed]
  have hq : ((quantileSpeed thetaSource t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (quantileSpeed_pos thetaSource t).ne'
  push_cast
  field_simp

/-- Canonical theta metric is self-adjoint. -/
theorem adjoint_thetaMetricOperator :
    thetaMetricOperator.adjoint = thetaMetricOperator := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  exact metricOperator_inner thetaSource thetaMetricBound_nonneg
    norm_metricSymbol_thetaSource_le

/-- Adjoint half of exact metric cancellation. -/
theorem thetaKernelOperator_adjoint_mul_thetaMetricOperator :
    thetaKernelOperator.adjoint * thetaMetricOperator =
      (-Complex.I) • pinnedVolterraCLM.adjoint := by
  have h := congrArg ContinuousLinearMap.adjoint
    thetaMetricOperator_mul_thetaKernelOperator
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint.map_smulₛₗ, RCLike.conj_I, neg_smul,
    adjoint_thetaMetricOperator] using h

/-- Exact singular-metric Green identity: metric skewness is rank two. -/
theorem thetaMetric_commutator_thetaKernelOperator :
    thetaMetricOperator * thetaKernelOperator -
        thetaKernelOperator.adjoint * thetaMetricOperator =
      Complex.I • pinnedBoundaryCLM := by
  rw [thetaMetricOperator_mul_thetaKernelOperator,
    thetaKernelOperator_adjoint_mul_thetaMetricOperator]
  rw [← adjoint_add_pinnedVolterraCLM_eq_pinnedBoundaryCLM]
  module

end


end RHTower
