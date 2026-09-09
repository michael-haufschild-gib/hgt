import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeABarrierPath
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Normalized integrand for the actual Gibbs barrier

The limiting polynomial arises from the exact factored Gibbs force and
the moving intermediate radius. Measurability and interval integrability
are verified for the actual rational integrand.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeABarrierPolynomial (τ φ t : ℝ) : ℝ :=
  egbFixedChargeAMeanPressureNumerator τ φ * egbCoexistenceASymmetricRatio τ * t ^ 2 +
    (2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) * t +
    (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
      egbCoexistenceASymmetricRatio τ

def egbFixedChargeABarrierIntegrand (w φ τ u : ℝ) : ℝ :=
  egbFixedChargeAMeanRadius w φ τ * (egbFixedChargeAMiddleGapCoordinate τ φ - 1) *
    (egbFixedChargeABarrierPathCoordinate τ φ u ^ 2 - 1) *
    egbFixedChargeABarrierPolynomial τ φ (egbFixedChargeABarrierPathCoordinate τ φ u) /
    (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) *
      (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) ^ 2)

def egbFixedChargeAGibbsBarrierCoefficient (w φ : ℝ) : ℝ :=
  egbFixedChargeACriticalRadius w φ * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) /
    (12 * (1 + 2 * egbFixedChargeACriticalCouplingWeight φ))

def egbFixedChargeABarrierLimitIntegrand (w φ u : ℝ) : ℝ :=
  4 * egbFixedChargeAGibbsBarrierCoefficient w φ * (2 * u - 3 * u ^ 2 + u ^ 3)

theorem egbFixedChargeAGibbsBarrierCoefficient_pos (w φ : ℝ) : 0 < egbFixedChargeAGibbsBarrierCoefficient w φ := by
  have hr := egbFixedChargeACriticalRadius_pos w φ
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAGibbsBarrierCoefficient
  positivity

theorem egbFixedChargeABarrierPolynomial_path_limit (φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeABarrierPolynomial τ φ (egbFixedChargeABarrierPathCoordinate τ φ u))
      atBot (𝓝 (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 - u))) := by
  have hx := egbFixedChargeABarrierPathCoordinate_critical_limit φ u
  have h1 := ((egbFixedChargeAMeanPressureNumerator_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit).mul (hx.pow 2)
  have h2 := (egbFixedChargeAMiddleMeanLinearCombination_limit φ).mul hx
  have h := (h1.add h2).add (egbFixedChargeAMiddleMeanResidual_linear_limit φ)
  simpa only [egbFixedChargeABarrierPolynomial, mul_zero, zero_mul, zero_add, add_zero] using h

theorem egbFixedChargeABarrierIntegrand_critical_limit (w φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeABarrierIntegrand w φ τ u) atBot (𝓝 (egbFixedChargeABarrierLimitIntegrand w φ u)) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hx := egbFixedChargeABarrierPathCoordinate_critical_limit φ u
  have hgap := (egbFixedChargeAMiddleGapCoordinate_critical_limit φ).sub (tendsto_const_nhds (x := (1 : ℝ)))
  have hpoly := (hx.pow 2).sub (tendsto_const_nhds (x := (1 : ℝ)))
  have hn := (((egbFixedChargeAMeanRadius_critical_limit w φ).mul hgap).mul hpoly).mul (egbFixedChargeABarrierPolynomial_path_limit φ u)
  have hd2 : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have hs : Tendsto (fun τ => (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) ^ 2)
      atBot (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.mul hx)).pow 2
  have hd := (((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanDenominator_critical_limit φ)).mul hd2).mul hs
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  have he : egbFixedChargeACriticalRadius w φ * (0 - 1) * ((1 - u) ^ 2 - 1) *
      (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 - u)) /
      (2 * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * 1 * 1) = egbFixedChargeABarrierLimitIntegrand w φ u := by
    unfold egbFixedChargeABarrierLimitIntegrand egbFixedChargeAGibbsBarrierCoefficient
    field_simp <;> ring
  rw [he] at h
  exact h

theorem egbFixedChargeABarrierIntegrand_measurable (w φ τ : ℝ) : Measurable (egbFixedChargeABarrierIntegrand w φ τ) := by
  unfold egbFixedChargeABarrierIntegrand egbFixedChargeABarrierPolynomial egbFixedChargeABarrierPathCoordinate
  fun_prop

theorem egbFixedChargeABarrierIntegrand_continuousOn (w φ τ : ℝ) :
    ContinuousOn (egbFixedChargeABarrierIntegrand w φ τ) (Icc 0 1) := by
  unfold egbFixedChargeABarrierIntegrand
  apply ContinuousOn.div
  · unfold egbFixedChargeABarrierPolynomial egbFixedChargeABarrierPathCoordinate
    fun_prop
  · unfold egbFixedChargeABarrierPathCoordinate
    fun_prop
  · intro u hu
    have hscale := (egbFixedChargeABarrierPathScale_mapsTo τ φ hu).1
    have hd := (egbCoexistenceASymmetricRatio_bounds τ).2
    have hs : 0 < 1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u := by linarith
    have hD := egbFixedChargeAMeanDenominator_pos τ φ
    positivity

theorem egbFixedChargeABarrierIntegrand_intervalIntegrable (w φ τ : ℝ) :
    IntervalIntegrable (egbFixedChargeABarrierIntegrand w φ τ) volume 0 1 :=
  ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (egbFixedChargeABarrierIntegrand_continuousOn w φ τ)

end GaloisForLFunctions.HTGeometry
