import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierIntegrand
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAInteriorRadius

/-!
# Rescaled Gibbs force across the full coexistence interval

The same rational kernel controls every interior Gibbs gap and the
moving-middle barrier. Its limit is cubic, with zeros at the phase
endpoints and the limiting intermediate equilibrium.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAGibbsKernel (w φ τ t : ℝ) : ℝ :=
  egbFixedChargeAMeanRadius w φ τ * (t ^ 2 - 1) * egbFixedChargeABarrierPolynomial τ φ t /
    (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) *
      (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2)

theorem egbFixedChargeAInteriorScale_mapsTo (τ : ℝ) :
    MapsTo (fun t => 1 + egbCoexistenceASymmetricRatio τ * t) (Icc (-1 : ℝ) 1)
      (Icc (1 - egbCoexistenceASymmetricRatio τ) (1 + egbCoexistenceASymmetricRatio τ)) := by
  intro t ht
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hlo := mul_le_mul_of_nonneg_left ht.1 hd.le
  have hhi := mul_le_mul_of_nonneg_left ht.2 hd.le
  change 1 - egbCoexistenceASymmetricRatio τ ≤ 1 + egbCoexistenceASymmetricRatio τ * t ∧
    1 + egbCoexistenceASymmetricRatio τ * t ≤ 1 + egbCoexistenceASymmetricRatio τ
  constructor <;> nlinarith only [hlo, hhi]

theorem egbFixedChargeABarrierPolynomial_coordinate_limit (φ t : ℝ) :
    Tendsto (fun τ => egbFixedChargeABarrierPolynomial τ φ t) atBot
      (𝓝 (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * t)) := by
  have h1 := ((egbFixedChargeAMeanPressureNumerator_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit).mul
    (tendsto_const_nhds (x := t ^ 2))
  have h2 := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).mul (tendsto_const_nhds (x := t))
  simpa only [egbFixedChargeABarrierPolynomial, mul_zero, zero_mul, zero_add, add_zero] using
    (h1.add h2).add (egbFixedChargeAMiddleMeanResidual_linear_limit φ)

theorem egbFixedChargeAGibbsKernel_critical_limit (w φ t : ℝ) :
    Tendsto (fun τ => egbFixedChargeAGibbsKernel w φ τ t) atBot
      (𝓝 (4 * egbFixedChargeAGibbsBarrierCoefficient w φ * (t ^ 2 - 1) * t)) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hn := ((egbFixedChargeAMeanRadius_critical_limit w φ).mul
    (tendsto_const_nhds (x := t ^ 2 - 1))).mul (egbFixedChargeABarrierPolynomial_coordinate_limit φ t)
  have hd2 : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have hs : Tendsto (fun τ => (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2) atBot (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      (egbCoexistenceASymmetricRatio_critical_limit.mul (tendsto_const_nhds (x := t)))).pow 2
  have hd := (((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanDenominator_critical_limit φ)).mul hd2).mul hs
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  have he : egbFixedChargeACriticalRadius w φ * (t ^ 2 - 1) *
      (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * t) /
      (2 * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * 1 * 1) =
      4 * egbFixedChargeAGibbsBarrierCoefficient w φ * (t ^ 2 - 1) * t := by
    unfold egbFixedChargeAGibbsBarrierCoefficient
    field_simp <;> ring
  rw [he] at h
  exact h

theorem egbFixedChargeAGibbsKernel_measurable (w φ τ : ℝ) : Measurable (egbFixedChargeAGibbsKernel w φ τ) := by
  unfold egbFixedChargeAGibbsKernel egbFixedChargeABarrierPolynomial
  fun_prop

theorem egbFixedChargeAGibbsKernel_continuousOn (w φ τ : ℝ) :
    ContinuousOn (egbFixedChargeAGibbsKernel w φ τ) (Icc (-1 : ℝ) 1) := by
  unfold egbFixedChargeAGibbsKernel
  apply ContinuousOn.div
  · unfold egbFixedChargeABarrierPolynomial
    fun_prop
  · fun_prop
  · intro t ht
    have hs := (egbFixedChargeAInteriorScale_mapsTo τ ht).1
    have hd := (egbCoexistenceASymmetricRatio_bounds τ).2
    have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ * t := by linarith
    have hD := egbFixedChargeAMeanDenominator_pos τ φ
    positivity

theorem egbFixedChargeAGibbsKernel_polynomial_formula (w φ τ t : ℝ) :
    egbFixedChargeAGibbsKernel w φ τ t = egbFixedChargeAMeanRadius w φ τ *
      (egbFixedChargeAMeanStationaryPolynomial τ φ (1 + egbCoexistenceASymmetricRatio τ * t) /
        egbCoexistenceASymmetricRatio τ ^ 3) /
      (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) *
        (1 + egbCoexistenceASymmetricRatio τ * t) ^ 2) := by
  rw [egbFixedChargeAMeanStationaryPolynomial_scaled]
  unfold egbFixedChargeAGibbsKernel egbFixedChargeABarrierPolynomial
  ring

theorem egbFixedChargeABarrierIntegrand_kernel_formula (w φ τ u : ℝ) :
    egbFixedChargeABarrierIntegrand w φ τ u = (egbFixedChargeAMiddleGapCoordinate τ φ - 1) *
      egbFixedChargeAGibbsKernel w φ τ (egbFixedChargeABarrierPathCoordinate τ φ u) := by
  unfold egbFixedChargeABarrierIntegrand egbFixedChargeAGibbsKernel
  ring

end GaloisForLFunctions.HTGeometry
