import GaloisForLFunctions.RHTower.HedenmalmThetaSignedPolarizationEscape
import GaloisForLFunctions.RHTower.PositiveOperatorKernel

/-!
# Exact Green balance for actual finite signed theta stages

The actual signed finite operators converge to the negative fixed theta source. Their canonical
metric defect therefore splits exactly into the negative rank-two pinned Green current plus the
metric commutator of the finite correction. The correction commutator tends to zero, but cannot
cancel the fixed boundary current eventually.
-/

open Complex Filter Metric

namespace RHTower.HedenmalmThetaSource

open HedenmalmQuantile HedenmalmHilbertSchmidt

noncomputable section

/-- Difference between the actual finite stage and its limiting signed theta source. -/
def thetaSourceSignedStageCorrection (k : ℕ) : H →L[ℂ] H :=
  thetaSourceSignedPulledOperator k + thetaKernelOperator

/-- Canonical-metric defect of one actual finite theta stage. -/
def thetaSourceSignedStageMetricDefect (k : ℕ) : H →L[ℂ] H :=
  thetaMetricOperator * thetaSourceSignedPulledOperator k -
    ContinuousLinearMap.adjoint (thetaSourceSignedPulledOperator k) * thetaMetricOperator

/-- Green remainder carried by the actual finite correction. -/
def thetaSourceSignedStageGreenRemainder (k : ℕ) : H →L[ℂ] H :=
  thetaMetricOperator * thetaSourceSignedStageCorrection k -
    ContinuousLinearMap.adjoint (thetaSourceSignedStageCorrection k) * thetaMetricOperator

/-- Actual finite corrections vanish in operator norm. -/
theorem thetaSourceSignedStageCorrection_tendsto_zero :
    Tendsto thetaSourceSignedStageCorrection atTop (nhds 0) := by
  have h := thetaSourceSignedPulledOperator_tendsto.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => thetaKernelOperator) atTop
      (nhds thetaKernelOperator))
  change Tendsto (fun k => thetaSourceSignedPulledOperator k + thetaKernelOperator)
    atTop (nhds 0)
  simpa using h

/-- Exact source/Stokes decomposition at every actual finite stage. -/
theorem thetaSourceSignedStageMetricDefect_add_pinnedGreen
    (k : ℕ) :
    thetaSourceSignedStageMetricDefect k + Complex.I • pinnedBoundaryCLM =
      thetaSourceSignedStageGreenRemainder k := by
  rw [thetaSourceSignedStageMetricDefect, thetaSourceSignedStageGreenRemainder,
    thetaSourceSignedStageCorrection, ← thetaMetric_commutator_thetaKernelOperator]
  simp only [mul_add, map_add, add_mul]
  noncomm_ring

/-- Finite correction Green remainder vanishes in operator norm. -/
theorem thetaSourceSignedStageGreenRemainder_tendsto_zero :
    Tendsto thetaSourceSignedStageGreenRemainder atTop (nhds 0) := by
  have hE := thetaSourceSignedStageCorrection_tendsto_zero
  have hleft : Tendsto
      (fun k => thetaMetricOperator * thetaSourceSignedStageCorrection k)
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hE : Tendsto
        (fun k => thetaMetricOperator * thetaSourceSignedStageCorrection k)
        atTop (nhds (thetaMetricOperator * 0)))
  have hadj : Tendsto
      (fun k => ContinuousLinearMap.adjoint (thetaSourceSignedStageCorrection k))
      atTop (nhds 0) := by
    have hcontinuous :=
      (ContinuousLinearMap.adjoint :
        (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] H →L[ℂ] H).continuous
    change Tendsto
      ((ContinuousLinearMap.adjoint :
        (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] H →L[ℂ] H) ∘ thetaSourceSignedStageCorrection)
      atTop (nhds 0)
    simpa using hcontinuous.continuousAt.tendsto.comp hE
  have hright : Tendsto
      (fun k => ContinuousLinearMap.adjoint (thetaSourceSignedStageCorrection k) *
        thetaMetricOperator) atTop (nhds 0) := by
    simpa using
      (hadj.mul tendsto_const_nhds : Tendsto
        (fun k => ContinuousLinearMap.adjoint (thetaSourceSignedStageCorrection k) *
          thetaMetricOperator) atTop (nhds (0 * thetaMetricOperator)))
  change Tendsto
    (fun k => thetaMetricOperator * thetaSourceSignedStageCorrection k -
      ContinuousLinearMap.adjoint (thetaSourceSignedStageCorrection k) * thetaMetricOperator)
    atTop (nhds 0)
  simpa using hleft.sub hright

/-- Complete source-defined boundary form seen by one actual finite stage. It is the fixed
rank-two pinned form plus the correction commutator forced by coefficient-faithful approximation. -/
def thetaSourceSignedStageGreenBoundary (k : ℕ) : H →L[ℂ] H :=
  pinnedBoundaryCLM + Complex.I • thetaSourceSignedStageGreenRemainder k

/-- Actual-stage metric defect is exactly `-i` times its complete Green boundary form. -/
theorem thetaSourceSignedStageMetricDefect_eq_negI_smul_greenBoundary (k : ℕ) :
    thetaSourceSignedStageMetricDefect k =
      (-Complex.I) • thetaSourceSignedStageGreenBoundary k := by
  have h := thetaSourceSignedStageMetricDefect_add_pinnedGreen k
  have hd : thetaSourceSignedStageMetricDefect k =
      thetaSourceSignedStageGreenRemainder k - Complex.I • pinnedBoundaryCLM := by
    calc
      thetaSourceSignedStageMetricDefect k =
          (thetaSourceSignedStageMetricDefect k + Complex.I • pinnedBoundaryCLM) -
            Complex.I • pinnedBoundaryCLM := by module
      _ = thetaSourceSignedStageGreenRemainder k -
            Complex.I • pinnedBoundaryCLM := by rw [h]
  rw [hd, thetaSourceSignedStageGreenBoundary, smul_add, smul_smul]
  have hII : (-Complex.I) * Complex.I = (1 : ℂ) := by
    rw [neg_mul, Complex.I_mul_I]
    norm_num
  rw [hII, one_smul]
  module

/-- Complete actual-stage Green forms converge in operator norm to the rank-two pinned form. -/
theorem thetaSourceSignedStageGreenBoundary_tendsto_pinned :
    Tendsto thetaSourceSignedStageGreenBoundary atTop (nhds pinnedBoundaryCLM) := by
  have hsmul : Tendsto
      (fun k => Complex.I • thetaSourceSignedStageGreenRemainder k)
      atTop (nhds 0) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Complex.I) atTop (nhds Complex.I)).smul
        thetaSourceSignedStageGreenRemainder_tendsto_zero)
  change Tendsto
    (fun k => pinnedBoundaryCLM + Complex.I • thetaSourceSignedStageGreenRemainder k)
    atTop (nhds pinnedBoundaryCLM)
  simpa using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => pinnedBoundaryCLM) atTop
      (nhds pinnedBoundaryCLM)).add hsmul)

/-- Canonical theta metric is a positive operator. This is the pointwise positivity of the
reciprocal quantile speed, expressed as an operator statement. -/
theorem thetaMetricOperator_isPositive :
    thetaMetricOperator.IsPositive := by
  constructor
  · intro f g
    exact metricOperator_inner thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le f g
  · intro f
    show 0 ≤ (inner ℂ (thetaMetricOperator f) f : ℂ).re
    rw [MeasureTheory.L2.inner_def]
    change 0 ≤ RCLike.re (∫ a, inner ℂ ((thetaMetricOperator f : H) a) (f a)
      ∂unitIntervalMeasure)
    rw [← integral_re (MeasureTheory.L2.integrable_inner (thetaMetricOperator f) f)]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [metricOperator_coeFn thetaSource thetaMetricBound_nonneg
      norm_metricSymbol_thetaSource_le f] with t ht
    change 0 ≤ RCLike.re (inner ℂ
      (((metricOperator thetaSource thetaMetricBound_nonneg
        norm_metricSymbol_thetaSource_le) f : H) t) (f t))
    rw [ht, RCLike.inner_apply']
    rw [map_mul (starRingEnd ℂ), starRingEnd_metricSymbol]
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    rw [metricSymbol]
    exact_mod_cast
      mul_nonneg (metricSymbol_pos thetaSource t).le (Complex.normSq_nonneg _)

/-- Canonical theta metric energy is strictly nonzero on every nonzero source vector. -/
theorem inner_thetaMetricOperator_ne_zero {f : H} (hf : f ≠ 0) :
    (inner ℂ (thetaMetricOperator f) f : ℂ) ≠ 0 := by
  intro hzero
  have hzero' : (inner ℂ f (thetaMetricOperator f) : ℂ) = 0 := by
    calc
      (inner ℂ f (thetaMetricOperator f) : ℂ) =
          inner ℂ (thetaMetricOperator f) f := by
        simpa [thetaMetricOperator] using
          (metricOperator_inner thetaSource thetaMetricBound_nonneg
            norm_metricSymbol_thetaSource_le f f).symm
      _ = 0 := hzero
  have happly : thetaMetricOperator f = 0 :=
    thetaMetricOperator_isPositive.apply_eq_zero_of_inner_eq_zero hzero'
  have hfzero := metricOperator_injective thetaSource thetaMetricBound_nonneg
    norm_metricSymbol_thetaSource_le (show thetaMetricOperator f = thetaMetricOperator 0 by
      simpa using happly)
  exact hf hfzero

/-- Exact modal Stokes law for every eigenmode of every actual finite theta stage. No divisor or
zero location enters: imaginary spectral displacement is precisely complete Green charge in the
canonical source metric. -/
theorem inner_thetaSourceSignedStageGreenBoundary_eigen
    (k : ℕ) {mu : ℂ} {f : H}
    (heigen : thetaSourceSignedPulledOperator k f = mu • f) :
    (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ) =
      (((-2 * mu.im : ℝ) : ℂ) *
        inner ℂ (thetaMetricOperator f) f) := by
  have hoperator := thetaSourceSignedStageMetricDefect_eq_negI_smul_greenBoundary k
  have hquad := congrArg
    (fun T : H →L[ℂ] H => (inner ℂ (T f) f : ℂ)) hoperator
  rw [thetaSourceSignedStageMetricDefect, sub_apply,
    mul_apply_eq_comp, mul_apply_eq_comp,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    smul_apply, inner_smul_left, heigen,
    map_smul, inner_smul_left, inner_smul_right] at hquad
  have hconjNegI : (starRingEnd ℂ) (-Complex.I) = Complex.I := by simp
  rw [hconjNegI] at hquad
  have hmu : (starRingEnd ℂ) mu - mu = (((-2 * mu.im : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp [Complex.sub_re]
    · simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.ofReal_im, Complex.I_re]
      ring
  have hquad' :
      (((starRingEnd ℂ) mu - mu) * inner ℂ (thetaMetricOperator f) f) =
        Complex.I * inner ℂ (thetaSourceSignedStageGreenBoundary k f) f := by
    linear_combination hquad
  rw [hmu] at hquad'
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I * inner ℂ (thetaSourceSignedStageGreenBoundary k f) f =
        (((-2 * mu.im : ℝ) : ℂ) * Complex.I) *
          inner ℂ (thetaMetricOperator f) f := hquad'.symm
    _ = Complex.I *
        (((-2 * mu.im : ℝ) : ℂ) * inner ℂ (thetaMetricOperator f) f) := by ring

/-- Exact alternative on an actual-stage eigenmode: complete Green neutrality is either horizontal
spectrum or degeneration of canonical metric energy. -/
theorem inner_thetaSourceSignedStageGreenBoundary_eigen_eq_zero_iff
    (k : ℕ) {mu : ℂ} {f : H}
    (heigen : thetaSourceSignedPulledOperator k f = mu • f) :
    (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ) = 0 ↔
      mu.im = 0 ∨ (inner ℂ (thetaMetricOperator f) f : ℂ) = 0 := by
  rw [inner_thetaSourceSignedStageGreenBoundary_eigen k heigen, mul_eq_zero]
  simp

/-- For every nonzero actual-stage eigenmode, complete Green neutrality is exactly horizontal
spectrum. The statement is source-only: it uses no Xi zero or divisor location. -/
theorem inner_thetaSourceSignedStageGreenBoundary_eigen_eq_zero_iff_im_eq_zero
    (k : ℕ) {mu : ℂ} {f : H} (hf : f ≠ 0)
    (heigen : thetaSourceSignedPulledOperator k f = mu • f) :
    (inner ℂ (thetaSourceSignedStageGreenBoundary k f) f : ℂ) = 0 ↔ mu.im = 0 := by
  rw [inner_thetaSourceSignedStageGreenBoundary_eigen_eq_zero_iff k heigen]
  simp [inner_thetaMetricOperator_ne_zero hf]

/-- Positive-metric adjointness of an actual stage is exactly cancellation of the pinned
rank-two current by the correction Green remainder. Thus no boundary information is hidden in
operator notation. -/
theorem thetaSourceSignedStage_metricAdjoint_iff_greenCancellation (k : ℕ) :
    thetaMetricOperator * thetaSourceSignedPulledOperator k =
        ContinuousLinearMap.adjoint (thetaSourceSignedPulledOperator k) * thetaMetricOperator ↔
      thetaSourceSignedStageGreenRemainder k = Complex.I • pinnedBoundaryCLM := by
  constructor
  · intro hadjoint
    have hdefect : thetaSourceSignedStageMetricDefect k = 0 := by
      rw [thetaSourceSignedStageMetricDefect]
      exact sub_eq_zero.mpr hadjoint
    rw [← thetaSourceSignedStageMetricDefect_add_pinnedGreen k, hdefect, zero_add]
  · intro hcancel
    have hbalance := thetaSourceSignedStageMetricDefect_add_pinnedGreen k
    rw [hcancel] at hbalance
    have hdefect : thetaSourceSignedStageMetricDefect k = 0 := by
      exact add_eq_right.mp hbalance
    rw [thetaSourceSignedStageMetricDefect] at hdefect
    exact sub_eq_zero.mp hdefect

/-- Vanishing correction remainder cannot eventually cancel nonzero rank-two pinned current. -/
theorem thetaSourceSignedStageGreenRemainder_not_eventually_pinnedGreen :
    ¬ ∀ᶠ k in atTop,
      thetaSourceSignedStageGreenRemainder k = Complex.I • pinnedBoundaryCLM := by
  intro heq
  have heq' : thetaSourceSignedStageGreenRemainder =ᶠ[atTop]
      (fun _ : ℕ => Complex.I • pinnedBoundaryCLM) := heq
  have hconst : Tendsto (fun _ : ℕ => Complex.I • pinnedBoundaryCLM)
      atTop (nhds (Complex.I • pinnedBoundaryCLM)) := tendsto_const_nhds
  have hsame : Tendsto thetaSourceSignedStageGreenRemainder atTop
      (nhds (Complex.I • pinnedBoundaryCLM)) := hconst.congr' heq'.symm
  have hzero : (Complex.I • pinnedBoundaryCLM : H →L[ℂ] H) = 0 :=
    tendsto_nhds_unique hsame thetaSourceSignedStageGreenRemainder_tendsto_zero
  exact pinnedBoundaryCLM_ne_zero (smul_eq_zero.mp hzero |>.resolve_left Complex.I_ne_zero)

end

end RHTower.HedenmalmThetaSource
