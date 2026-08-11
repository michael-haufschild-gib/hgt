import GaloisForLFunctions.RHTower.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.HedenmalmQuantileNormalForm
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.RealCharacterDenseL2

/-!
# Weighted Esscher cyclicity of the theta quantile source

Every real Esscher weight defines a finite tilted theta law.  Fourier characters are cyclic in
its `L²` space; multiplication by the positive square-root density and the probability-integral
transform transport this to a cyclic family

`exp (h Q(t)) exp (i tau Q(t))`

in quantile space.  Thus even one fixed real Esscher line already has dense complex span.
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry HedenmalmQuantile

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Positive density defining the real `h`-Esscher square-weight. -/
def thetaEsscherSquareWeight (h x : ℝ) : ℝ :=
  Real.exp (2 * h * x)

theorem measurable_thetaEsscherSquareWeight (h : ℝ) :
    Measurable (thetaEsscherSquareWeight h) := by
  unfold thetaEsscherSquareWeight
  fun_prop

theorem thetaEsscherSquareWeight_pos (h x : ℝ) :
    0 < thetaEsscherSquareWeight h x := by
  exact Real.exp_pos _

/-- Theta source law tilted by the square of the `h`-Esscher multiplier. -/
def thetaEsscherLaw (h : ℝ) : Measure ℝ :=
  thetaSource.law.withDensity (realDensity (thetaEsscherSquareWeight h))

theorem integrable_thetaEsscherSquareWeight_law (h : ℝ) :
    Integrable (thetaEsscherSquareWeight h) thetaSource.law := by
  rw [thetaSource.integrable_law_iff]
  have hint := (integrable_exp_mul_thetaCuspFullSource (2 * h)).div_const thetaSource.mass
  convert hint using 1
  funext x
  simp only [thetaEsscherSquareWeight, smul_eq_mul]
  rw [show thetaSource.normalized x = thetaSource.k x / thetaSource.mass from rfl,
    thetaSource_k]
  ring

noncomputable instance instIsFiniteMeasureThetaEsscherLaw (h : ℝ) :
    IsFiniteMeasure (thetaEsscherLaw h) := by
  rw [thetaEsscherLaw]
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_thetaEsscherSquareWeight_law h).hasFiniteIntegral

/-- Unitary transport from the tilted theta law to quantile space. -/
def thetaEsscherUnitary (h : ℝ) :
    Lp ℂ 2 (thetaEsscherLaw h) ≃ₗᵢ[ℂ] ThetaH :=
  (weightedDensityUnitary (μ := thetaSource.law)
      (thetaEsscherSquareWeight h)
      (measurable_thetaEsscherSquareWeight h)
      (thetaEsscherSquareWeight_pos h)).trans
    (lawToUnitInterval thetaSource)

/-- Fourier characters of one fixed Esscher line, transported to quantile space. -/
def thetaEsscherFourierFamily (h tau : ℝ) : ThetaH :=
  thetaEsscherUnitary h (realProbCharacterLp (thetaEsscherLaw h) tau)

theorem sqrtWeight_thetaEsscherSquareWeight (h x : ℝ) :
    sqrtWeight (thetaEsscherSquareWeight h) x = (Real.exp (h * x) : ℂ) := by
  rw [sqrtWeight, thetaEsscherSquareWeight]
  have hexp : Real.exp (2 * h * x) = Real.exp (h * x) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Literal quantile representative of the transported Esscher--Fourier family. -/
theorem thetaEsscherFourierFamily_ae (h tau : ℝ) :
    (fun t => thetaEsscherFourierFamily h tau t) =ᵐ[unitIntervalMeasure]
      fun t => (Real.exp (h * thetaSource.quantileFun t) : ℂ) *
        realProbCharacter tau (thetaSource.quantileFun t) := by
  let e : Lp ℂ 2 (thetaEsscherLaw h) :=
    realProbCharacterLp (thetaEsscherLaw h) tau
  let m : Lp ℂ 2 thetaSource.law :=
    weightedDensityUnitary (μ := thetaSource.law)
      (thetaEsscherSquareWeight h)
      (measurable_thetaEsscherSquareWeight h)
      (thetaEsscherSquareWeight_pos h) e
  have hunit := lawToUnitInterval_ae thetaSource m
  have hmul := densityMul_ae (μ := thetaSource.law)
    (thetaEsscherSquareWeight h)
    (measurable_thetaEsscherSquareWeight h)
    (thetaEsscherSquareWeight_pos h) e
  have hcharWeighted := realProbCharacterLp_ae (thetaEsscherLaw h) tau
  have hcharLaw : (fun x => e x) =ᵐ[thetaSource.law] realProbCharacter tau :=
    (withDensity_realDensity_ae_eq
      (measurable_thetaEsscherSquareWeight h)
      (thetaEsscherSquareWeight_pos h)).mp (by
        simpa only [e, thetaEsscherLaw] using hcharWeighted)
  have hmulQuantile := hmul.comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  have hcharQuantile := hcharLaw.comp_tendsto
    (measurePreserving_quantile_unitInterval thetaSource).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hunit, hmulQuantile, hcharQuantile] with t hu hm hc
  change lawToUnitInterval thetaSource m t = _
  rw [hu]
  change (densityMul (μ := thetaSource.law)
    (thetaEsscherSquareWeight h)
    (measurable_thetaEsscherSquareWeight h)
    (thetaEsscherSquareWeight_pos h) e ∘ thetaSource.quantileFun) t = _
  rw [hm]
  change sqrtWeight (thetaEsscherSquareWeight h) (thetaSource.quantileFun t) *
    e (thetaSource.quantileFun t) = _
  change e (thetaSource.quantileFun t) =
    realProbCharacter tau (thetaSource.quantileFun t) at hc
  rw [hc, sqrtWeight_thetaEsscherSquareWeight]

/-- **Unconditional fixed-line Esscher cyclicity.**  For every real tilt, the complex span of its
Fourier modulation family is dense in the full theta quantile Hilbert space. -/
theorem isCyclicFamily_thetaEsscherFourierFamily (h : ℝ) :
    IsCyclicFamily (𝕜 := ℂ) (thetaEsscherFourierFamily h) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let LU : Lp ℂ 2 (thetaEsscherLaw h) →L[ℂ] ℂ :=
    L.comp (thetaEsscherUnitary h).toLinearIsometry.toContinuousLinearMap
  have hLU (tau : ℝ) : LU (realProbCharacterLp (thetaEsscherLaw h) tau) = 0 := by
    exact hL tau
  have hLUzero := continuousLinearFunctional_eq_zero_of_isCyclicFamily
    (isCyclicFamily_realProbCharacterLp (thetaEsscherLaw h)) LU hLU
  apply ContinuousLinearMap.ext
  intro y
  have hy := congrArg
    (fun M : Lp ℂ 2 (thetaEsscherLaw h) →L[ℂ] ℂ =>
      M ((thetaEsscherUnitary h).symm y)) hLUzero
  change L (thetaEsscherUnitary h ((thetaEsscherUnitary h).symm y)) = 0 at hy
  simpa using hy

/-- Exact Gram kernel of one Esscher line.  It is a translated completed theta transform. -/
theorem inner_thetaEsscherFourierFamily (h tau sigma : ℝ) :
    inner ℂ (thetaEsscherFourierFamily h tau)
        (thetaEsscherFourierFamily h sigma) =
      XiC (((sigma - tau : ℝ) : ℂ) - (2 * h : ℝ) * Complex.I) /
        (thetaSource.mass : ℂ) := by
  let z : ℂ := ((sigma - tau : ℝ) : ℂ) - (2 * h : ℝ) * Complex.I
  rw [inner_lp_eq]
  have hpoint :
      (fun t => (starRingEnd ℂ) (thetaEsscherFourierFamily h tau t) *
        thetaEsscherFourierFamily h sigma t) =ᵐ[unitIntervalMeasure]
      fun t => sourceChar z (thetaSource.quantileFun t) := by
    filter_upwards [thetaEsscherFourierFamily_ae h tau,
      thetaEsscherFourierFamily_ae h sigma] with t ht hs
    rw [ht, hs, map_mul, Complex.conj_ofReal]
    rw [Complex.ofReal_exp, realProbCharacter, realProbCharacter, sourceChar,
      ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    dsimp only [z]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [integral_congr_ae hpoint]
  have hres : unitIntervalMeasure =
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1) := by
    rw [unitIntervalMeasure, restrict_Ioo_eq_restrict_Icc]
  rw [hres, integral_sourceChar_comp_quantile, xiC_thetaSource_all]

end

end RHTower.HedenmalmThetaSource
