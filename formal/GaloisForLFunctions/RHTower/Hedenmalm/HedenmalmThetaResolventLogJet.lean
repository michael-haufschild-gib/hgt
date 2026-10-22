import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmQuantileSliceMoment
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaResolventMetricPlancherel
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Phase-linear logarithmic jet of the theta source resolvent

The quantile coordinate is a square-integrable state.  Its all-complex source-character moment is
the first spectral jet of `XiC`, and the pinned inverse-pencil row is therefore `-i XiC'/XiC`.
On the fixed exterior line `h=1` this is exactly the continued prime--archimedean source trace.

Unlike determinant-weighted Gram synthesis, this row remains phase-linear and retains every pole
with its multiplicity.
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile GaloisForLFunctions.HTGeometry

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- The theta quantile coordinate belongs to `L²(0,1)`. -/
theorem memLp_two_thetaQuantileCoordinate :
    MemLp (fun t => (thetaSource.quantileFun t : ℂ)) 2 unitIntervalMeasure := by
  have hmeas : AEStronglyMeasurable
      (fun t => (thetaSource.quantileFun t : ℂ)) unitIntervalMeasure :=
    (Complex.continuous_ofReal.measurable.comp
      thetaSource.measurable_quantileFun).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ?_
  rw [unitIntervalMeasure_eq]
  refine integrableOn_sq_quantileFun_thetaSource.congr ?_
  filter_upwards with t
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Canonical phase-sensitive test vector: the quantile coordinate itself. -/
def thetaQuantileCoordinate : ThetaH :=
  memLp_two_thetaQuantileCoordinate.toLp
    (fun t => (thetaSource.quantileFun t : ℂ))

theorem thetaQuantileCoordinate_ae :
    (fun t => thetaQuantileCoordinate t) =ᵐ[unitIntervalMeasure]
      fun t => (thetaSource.quantileFun t : ℂ) :=
  memLp_two_thetaQuantileCoordinate.coeFn_toLp

/-- The first Xi jet is the oriented first source-character moment. -/
theorem deriv_XiC_eq_integral_I_mul_sourceChar (z : ℂ) :
    deriv XiC z =
      ∫ x : ℝ,
        Complex.I * (x : ℂ) * sourceChar z x * (thetaSource.k x : ℂ) := by
  have hderivFL : deriv thetaCuspFourierLaplace z =
      ∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand z x :=
    (hasDerivAt_thetaCuspFourierLaplace_all z).deriv
  have hfun : thetaCuspFourierLaplace = XiC :=
    funext thetaCuspFourierLaplace_eq_XiC_all
  rw [hfun] at hderivFL
  have hneg := integral_neg_eq_self
    (thetaCuspFourierLaplaceDerivativeIntegrand z) (volume : Measure ℝ)
  have hpoint : (fun x : ℝ => thetaCuspFourierLaplaceDerivativeIntegrand z (-x)) =
      fun x : ℝ =>
        Complex.I * (x : ℂ) * sourceChar z x * (thetaSource.k x : ℂ) := by
    funext x
    simp only [thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand, sourceChar, thetaSource_k,
      Complex.ofReal_neg, thetaCuspFullSource_neg]
    have hphase : -Complex.I * z * (-(x : ℂ)) =
        Complex.I * z * (x : ℂ) := by ring
    rw [hphase]
    ring
  rw [hpoint] at hneg
  exact hderivFL.trans hneg.symm

/-- Source-character moment of the quantile coordinate is the normalized first Xi jet. -/
theorem thetaComplexResolventMoment_thetaQuantileCoordinate (z : ℂ) :
    thetaComplexResolventMoment z thetaQuantileCoordinate =
      -Complex.I * deriv XiC z / (thetaSource.mass : ℂ) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => sourceChar z x * (x : ℂ)) (volume : Measure ℝ) :=
    (continuous_sourceChar z).aestronglyMeasurable.mul
      Complex.continuous_ofReal.aestronglyMeasurable
  have hchange := integral_comp_quantile thetaSource
    (fun x : ℝ => sourceChar z x * (x : ℂ)) hmeas
  have hderiv := deriv_XiC_eq_integral_I_mul_sourceChar z
  have hderiv' : deriv XiC z = Complex.I *
      ∫ x : ℝ, sourceChar z x * (x : ℂ) * (thetaSource.k x : ℂ) := by
    rw [hderiv, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [thetaComplexResolventMoment]
  calc
    (∫ t,
        sourceChar z (thetaSource.quantileFun t) * thetaQuantileCoordinate t
          ∂unitIntervalMeasure) =
        ∫ t,
          sourceChar z (thetaSource.quantileFun t) *
            (thetaSource.quantileFun t : ℂ) ∂unitIntervalMeasure := by
      apply integral_congr_ae
      filter_upwards [thetaQuantileCoordinate_ae] with t ht
      rw [ht]
    _ = ∫ t in Ioo (0 : ℝ) 1,
          sourceChar z (thetaSource.quantileFun t) *
            (thetaSource.quantileFun t : ℂ) := by
      rw [unitIntervalMeasure_eq]
    _ = ∫ x : ℝ,
        thetaSource.normalized x • (sourceChar z x * (x : ℂ)) := hchange
    _ = (1 / (thetaSource.mass : ℂ)) *
        ∫ x : ℝ, sourceChar z x * (x : ℂ) * (thetaSource.k x : ℂ) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.real_smul]
      change ((thetaSource.k x / thetaSource.mass : ℝ) : ℂ) *
          (sourceChar z x * (x : ℂ)) = _
      push_cast
      field_simp [thetaSource.mass_ne_zero]
    _ = -Complex.I * deriv XiC z / (thetaSource.mass : ℂ) := by
      rw [hderiv']
      field_simp [thetaSource.mass_ne_zero]
      rw [Complex.I_sq]
      ring

/-- **Phase-linear resolvent jet.**  At every invertible pencil point the pinned quantile-coordinate
row is exactly `-i` times the Xi logarithmic derivative. -/
theorem pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv
    {z : ℂ} (hz : IsUnit (thetaSourcePencil z)) :
    pinnedMean (thetaComplexResolvent z thetaQuantileCoordinate) =
      -Complex.I * logDeriv XiC z := by
  have hXi : XiC z ≠ 0 := by
    intro hzero
    exact (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).2 hzero hz
  rw [pinnedMean_thetaComplexResolvent_eq hz,
    thetaComplexResolventMoment_thetaQuantileCoordinate,
    rootA_one, xiC_thetaSource_all, logDeriv_apply]
  field_simp [thetaSource.mass_ne_zero, hXi]

/-- Fixed exterior line version, with no zero-free premise. -/
theorem pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_safeLine
    (tau : ℝ) :
    pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter 1 tau)
          thetaQuantileCoordinate) =
      -Complex.I * logDeriv XiC (thetaEsscherResolventParameter 1 tau) := by
  exact pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_logDeriv
    (isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs
      (by norm_num) tau)

/-- On the safe Euler line, the same unsquared resolvent row is the continued prime--Gamma source
trace.  This is the exact phase-preserving interface required by Route T. -/
theorem pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_eq_primeArchTrace
    (tau : ℝ) :
    pinnedMean
        (thetaComplexResolvent (thetaEsscherResolventParameter 1 tau)
          thetaQuantileCoordinate) =
      -Complex.I *
        continuedPrimeArchSourceRelativeTrace
          (thetaEsscherResolventParameter 1 tau) := by
  let z : ℂ := thetaEsscherResolventParameter 1 tau
  have hspos : 0 < (1 / 2 + z * Complex.I).re := by
    dsimp only [z, thetaEsscherResolventParameter]
    norm_num [Complex.mul_re]
  have hs1 : 1 / 2 + z * Complex.I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    dsimp only [z, thetaEsscherResolventParameter] at hre
    simp [Complex.mul_re] at hre
  have hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      dsimp only [z, thetaEsscherResolventParameter]
      norm_num [Complex.mul_re])
  have hpencil : IsUnit (thetaSourcePencil z) :=
    isUnit_thetaSourcePencil_thetaEsscherResolventParameter_of_half_le_abs
      (by norm_num) tau
  have hXi : XiC z ≠ 0 := by
    intro hzero
    exact (thetaSourcePencil_not_isUnit_iff_XiC_eq_zero z).2 hzero hpencil
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta]
    exact (logDeriv_XiC_eq_relativeResolventTrace hXi).symm
  rw [pinnedMean_thetaComplexResolvent_thetaQuantileCoordinate_safeLine, ← hsource]

end

end RHTower.HedenmalmThetaSource
