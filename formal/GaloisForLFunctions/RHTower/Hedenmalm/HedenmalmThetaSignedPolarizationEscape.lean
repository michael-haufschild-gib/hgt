import GaloisForLFunctions.HTGeometry.HilbertSchmidtBlockEigenvector
import GaloisForLFunctions.HTGeometry.MetricAdjointCorrectionEscape
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMetricCommutator
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaSourceSignedOrdinaryDeterminantCompletion

/-!
# Theta signed-source polarization escape

Canonical theta metric has exact nonzero rank-two Green defect.  Consequently no source correction
tending to zero can make theta source inverse adjoint in this fixed metric, and no repairing metrics
converging to canonical theta metric can do so.

This obstruction applies directly to trace-zero finite source kernels whose honest ordinary
determinants converge compact-open to normalized Xi.  After pulling these finite matrix operators
back to quantile space, they converge in operator norm to signed theta source inverse.  They cannot
eventually be theta-metric-adjoint; any exact repairing polarizations must escape canonical metric
in operator norm.
-/

open Complex
open Filter Metric

namespace RHTower

open HedenmalmQuantile HedenmalmThetaSource HedenmalmHilbertSchmidt
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal pinned boundary operator is nonzero, witnessed by its positive mode. -/
theorem pinnedBoundaryCLM_ne_zero : pinnedBoundaryCLM ≠ 0 := by
  intro hzero
  have hquad := congrArg
    (fun A : H →L[ℂ] H => inner ℂ (A pinnedPositiveMode) pinnedPositiveMode) hzero
  rw [inner_pinnedBoundaryCLM_pinnedPositiveMode] at hquad
  norm_num at hquad

/-- Canonical theta metric-adjoint defect is genuinely nonzero. -/
theorem thetaMetric_commutator_thetaKernelOperator_ne_zero :
    thetaMetricOperator * thetaKernelOperator -
        ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator ≠ 0 := by
  rw [thetaMetric_commutator_thetaKernelOperator]
  exact smul_ne_zero Complex.I_ne_zero pinnedBoundaryCLM_ne_zero

/-- Source-specific quantitative escape law.  Exact metric-adjoint repair must pay for complete
rank-two pinned boundary defect through metric drift or correction mass. -/
theorem pinnedBoundaryCLM_norm_le_metricAdjointCorrection_escape
    (Q E : H →L[ℂ] H)
    (hrepair : Q * (thetaKernelOperator + E) =
      ContinuousLinearMap.adjoint (thetaKernelOperator + E) * Q) :
    ‖pinnedBoundaryCLM‖ ≤
      2 * ‖thetaMetricOperator - Q‖ * ‖thetaKernelOperator‖ + 2 * ‖Q‖ * ‖E‖ := by
  have hbound := norm_metricAdjointCorrection_defect_le
    thetaKernelOperator thetaMetricOperator Q E hrepair
  rw [thetaMetric_commutator_thetaKernelOperator, norm_smul, norm_I, one_mul] at hbound
  exact hbound

/-- Fixed theta metric imposes explicit correction-norm floor. -/
theorem pinnedBoundaryCLM_norm_le_metricAdjointCorrection
    (E : H →L[ℂ] H)
    (hrepair : thetaMetricOperator * (thetaKernelOperator + E) =
      ContinuousLinearMap.adjoint (thetaKernelOperator + E) * thetaMetricOperator) :
    ‖pinnedBoundaryCLM‖ ≤ 2 * ‖thetaMetricOperator‖ * ‖E‖ := by
  have hbound := norm_metricAdjointCorrection_defect_le
    thetaKernelOperator thetaMetricOperator thetaMetricOperator E hrepair
  rw [thetaMetric_commutator_thetaKernelOperator, norm_smul, norm_I,
    one_mul, sub_self, norm_zero] at hbound
  simpa using hbound

/-- Every exact fixed-metric correction has nonzero operator norm. -/
theorem thetaMetricAdjointCorrection_norm_ne_zero
    (E : H →L[ℂ] H)
    (hrepair : thetaMetricOperator * (thetaKernelOperator + E) =
      ContinuousLinearMap.adjoint (thetaKernelOperator + E) * thetaMetricOperator) :
    ‖E‖ ≠ 0 := by
  intro hEnorm
  have hbound := pinnedBoundaryCLM_norm_le_metricAdjointCorrection E hrepair
  rw [hEnorm, mul_zero] at hbound
  have hCnorm : ‖pinnedBoundaryCLM‖ ≠ 0 := norm_ne_zero_iff.mpr pinnedBoundaryCLM_ne_zero
  exact hCnorm (le_antisymm hbound (norm_nonneg _))

/-- No operator-norm-vanishing correction sequence repairs theta source in fixed theta metric. -/
theorem no_thetaMetricAdjointCorrection_vanishing_sequence :
    ¬ ∃ E : ℕ → H →L[ℂ] H,
      Tendsto E atTop (nhds 0) ∧
      ∀ n, thetaMetricOperator * (thetaKernelOperator + E n) =
        ContinuousLinearMap.adjoint (thetaKernelOperator + E n) * thetaMetricOperator := by
  rintro ⟨E, hE, hrepair⟩
  have hmetric := metricAdjointCorrection_limit_rigidity
    thetaKernelOperator thetaMetricOperator (fun _ => thetaMetricOperator) E
    tendsto_const_nhds hE (Filter.Eventually.of_forall hrepair)
  exact thetaMetric_commutator_thetaKernelOperator_ne_zero (sub_eq_zero.mpr hmetric)

/-- Simultaneously vanishing corrections and theta-metric-convergent polarizations are impossible. -/
theorem no_thetaMetricAdjointCorrection_convergent_polarization :
    ¬ ∃ Q E : ℕ → H →L[ℂ] H,
      Tendsto Q atTop (nhds thetaMetricOperator) ∧
      Tendsto E atTop (nhds 0) ∧
      ∀ n, Q n * (thetaKernelOperator + E n) =
        ContinuousLinearMap.adjoint (thetaKernelOperator + E n) * Q n := by
  rintro ⟨Q, E, hQ, hE, hrepair⟩
  have hmetric := metricAdjointCorrection_limit_rigidity
    thetaKernelOperator thetaMetricOperator Q E hQ hE (Filter.Eventually.of_forall hrepair)
  exact thetaMetric_commutator_thetaKernelOperator_ne_zero (sub_eq_zero.mpr hmetric)

/-- Actual `k`-th trace-zero finite source kernel represented on theta coordinate space. -/
noncomputable def thetaSourceSignedMatrixOperator (k : ℕ) :
    lp (fun _ : thetaIndex => ℂ) 2 →L[ℂ] lp (fun _ : thetaIndex => ℂ) 2 :=
  HilbertSchmidt.toOperator (isHS_thetaSourceSignedKernel k)

/-- Hilbert--Schmidt convergence of signed kernels implies operator-norm convergence of their
represented finite operators. -/
theorem thetaSourceSignedMatrixOperator_tendsto :
    Tendsto thetaSourceSignedMatrixOperator atTop
      (nhds (HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix)) := by
  have hnorm : Tendsto
      (fun k => ‖thetaSourceSignedMatrixOperator k -
        HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix‖) atTop (nhds 0) := by
    exact squeeze_zero (fun k => norm_nonneg _)
      (fun k => HilbertSchmidt.norm_toOperator_sub_le
        (isHS_thetaSourceSignedKernel k) isHS_neg_thetaKernelMatrix)
      thetaSourceSignedKernel_tendsto_source
  have hdiff : Tendsto
      (fun k => thetaSourceSignedMatrixOperator k -
        HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hconst : Tendsto
      (fun _ : ℕ => HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix) atTop
      (nhds (HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix)) := tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hdiff.add hconst

/-- Pull actual finite coordinate operator back to quantile source space. -/
noncomputable def thetaSourceSignedPulledOperator (k : ℕ) : H →L[ℂ] H :=
  thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((thetaSourceSignedMatrixOperator k).comp
      thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Coordinate limit is exactly signed fixed theta source inverse. -/
theorem thetaSourceSignedPullback_limit_identification :
    thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix).comp
          thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap) =
      -thetaKernelOperator := by
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg thetaCoord.symm (thetaCoord_intertwines_neg_sourceInverse f)
  simpa [ContinuousLinearMap.comp_apply] using h.symm

/-- Actual finite signed source operators converge in operator norm to signed fixed source
inverse after canonical coordinate pullback. -/
theorem thetaSourceSignedPulledOperator_tendsto :
    Tendsto thetaSourceSignedPulledOperator atTop (nhds (-thetaKernelOperator)) := by
  let U := thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap
  let V := thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hright : Tendsto
      (fun k => (thetaSourceSignedMatrixOperator k).comp U) atTop
      (nhds ((HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix).comp U)) := by
    exact ((ContinuousLinearMap.isBoundedLinearMap_comp_right U).continuous.tendsto
      (HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix)).comp
        thetaSourceSignedMatrixOperator_tendsto
  have hleft : Tendsto
      (fun k => V.comp ((thetaSourceSignedMatrixOperator k).comp U)) atTop
      (nhds (V.comp ((HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix).comp U))) := by
    exact ((ContinuousLinearMap.isBoundedLinearMap_comp_left V).continuous.tendsto
      ((HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix).comp U)).comp hright
  change Tendsto
    (fun k => V.comp ((thetaSourceSignedMatrixOperator k).comp U)) atTop
      (nhds (-thetaKernelOperator))
  rw [show V.comp ((HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix).comp U) =
      -thetaKernelOperator by exact thetaSourceSignedPullback_limit_identification] at hleft
  exact hleft

/-- Actual trace-zero finite source corrections cannot eventually become adjoint in fixed theta
metric.  Xi-compatible determinant convergence does not evade rank-two Green defect. -/
theorem thetaSourceSignedPulledOperator_not_eventually_thetaMetricAdjoint :
    ¬ ∀ᶠ k in atTop,
      thetaMetricOperator * thetaSourceSignedPulledOperator k =
        ContinuousLinearMap.adjoint (thetaSourceSignedPulledOperator k) * thetaMetricOperator := by
  intro hrepair
  have hlimit := metricAdjoint_limit_rigidity (-thetaKernelOperator) thetaMetricOperator
    thetaSourceSignedPulledOperator (fun _ => thetaMetricOperator)
    thetaSourceSignedPulledOperator_tendsto tendsto_const_nhds hrepair
  apply thetaMetric_commutator_thetaKernelOperator_ne_zero
  have hmetric : thetaMetricOperator * thetaKernelOperator =
      ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator := by
    simpa only [mul_neg, map_neg, neg_mul, neg_inj] using hlimit
  exact sub_eq_zero.mpr hmetric

/-- Exact metric-adjoint realizations of actual signed finite source operators must use
polarizations escaping canonical theta metric in operator norm. -/
theorem thetaSourceSignedPulledOperator_polarization_escape :
    ∀ Q : ℕ → H →L[ℂ] H,
      (∀ᶠ k in atTop,
        Q k * thetaSourceSignedPulledOperator k =
          ContinuousLinearMap.adjoint (thetaSourceSignedPulledOperator k) * Q k) →
      ¬ Tendsto Q atTop (nhds thetaMetricOperator) := by
  intro Q hrepair hQ
  have hlimit := metricAdjoint_limit_rigidity (-thetaKernelOperator) thetaMetricOperator
    thetaSourceSignedPulledOperator Q thetaSourceSignedPulledOperator_tendsto hQ hrepair
  apply thetaMetric_commutator_thetaKernelOperator_ne_zero
  have hmetric : thetaMetricOperator * thetaKernelOperator =
      ContinuousLinearMap.adjoint thetaKernelOperator * thetaMetricOperator := by
    simpa only [mul_neg, map_neg, neg_mul, neg_inj] using hlimit
  exact sub_eq_zero.mpr hmetric

/-- Closed frontier certificate: honest finite signed source determinants converge compact-open to
normalized Xi, while any eventual metric-adjoint realization of those same source operators must
escape canonical theta polarization in operator norm. -/
theorem thetaSourceSignedCompletion_and_polarization_escape :
    TendstoLocallyUniformly thetaSourceSignedOrdinaryDet
        (fun z => XiC z / XiC 0) atTop ∧
      ∀ Q : ℕ → H →L[ℂ] H,
        (∀ᶠ k in atTop,
          Q k * thetaSourceSignedPulledOperator k =
            ContinuousLinearMap.adjoint (thetaSourceSignedPulledOperator k) * Q k) →
        ¬ Tendsto Q atTop (nhds thetaMetricOperator) := by
  exact ⟨thetaSourceSignedOrdinaryDet_tendstoLocallyUniformly_XiC,
    thetaSourceSignedPulledOperator_polarization_escape⟩

end

end RHTower
