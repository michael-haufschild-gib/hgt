import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitPath
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanGibbsForce

/-!
# Quartic force on the shorter mean-to-middle path

The exact stationary polynomial admits a second rescaling at radius
m(1+d²cu). At the constructed middle shift the limiting force is linear
along the path, vanishing at the actual intermediate equilibrium.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanDeficitPolynomial (τ φ u : ℝ) : ℝ :=
  egbFixedChargeAMeanPressureNumerator τ φ * egbCoexistenceASymmetricRatio τ ^ 2 *
    egbFixedChargeAMiddleQuadraticShift τ φ ^ 2 * u ^ 2 +
  (2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) *
    egbFixedChargeAMiddleQuadraticShift τ φ * u +
  (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
    egbCoexistenceASymmetricRatio τ ^ 2

def egbFixedChargeAMeanDeficitForce (τ φ u : ℝ) : ℝ :=
  (egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ ^ 2 * u ^ 2 - 1) *
    egbFixedChargeAMeanDeficitPolynomial τ φ u /
    (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) *
      (1 + egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ * u) ^ 2)

theorem egbFixedChargeAMeanStationaryPolynomial_quadratic_scaled (τ φ c u : ℝ) :
    egbFixedChargeAMeanStationaryPolynomial τ φ (1 + egbCoexistenceASymmetricRatio τ ^ 2 * c * u) /
      egbCoexistenceASymmetricRatio τ ^ 4 =
    (egbCoexistenceASymmetricRatio τ ^ 2 * c ^ 2 * u ^ 2 - 1) *
      (egbFixedChargeAMeanPressureNumerator τ φ * egbCoexistenceASymmetricRatio τ ^ 2 * c ^ 2 * u ^ 2 +
        (2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) * c * u +
        (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
          egbCoexistenceASymmetricRatio τ ^ 2) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMeanStationaryPolynomial_factorization]
  field_simp <;> ring

theorem egbFixedChargeAMeanDeficitForce_polynomial_formula (τ φ u : ℝ) :
    egbFixedChargeAMeanDeficitForce τ φ u =
      (egbFixedChargeAMeanStationaryPolynomial τ φ (1 + egbCoexistenceASymmetricRatio τ ^ 2 *
        egbFixedChargeAMiddleQuadraticShift τ φ * u) / egbCoexistenceASymmetricRatio τ ^ 4) /
      (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) *
        (1 + egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ * u) ^ 2) := by
  rw [egbFixedChargeAMeanStationaryPolynomial_quadratic_scaled]
  rfl

theorem egbFixedChargeAMiddleMeanCorrection_force_identity (φ : ℝ) :
    4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * egbFixedChargeAMiddleMeanCorrection φ =
      -(1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) := by
  have hb := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  unfold egbFixedChargeAMiddleMeanCorrection
  field_simp <;> ring

theorem egbFixedChargeAMeanDeficitPolynomial_critical_limit (φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanDeficitPolynomial τ φ u) atBot
      (𝓝 ((1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) * (1 - u))) := by
  have hc := egbFixedChargeAMiddleQuadraticShift_critical_limit φ
  have h1 := ((((egbFixedChargeAMeanPressureNumerator_critical_limit φ).mul
    (egbCoexistenceASymmetricRatio_critical_limit.pow 2)).mul (hc.pow 2)).mul (tendsto_const_nhds (x := u ^ 2)))
  have h2 := ((egbFixedChargeAMiddleMeanLinearCombination_limit φ).mul hc).mul (tendsto_const_nhds (x := u))
  have h := (h1.add h2).add (egbFixedChargeAMiddleMeanResidual_critical_limit φ)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_add,
    egbFixedChargeAMiddleMeanCorrection_force_identity] at h
  have he : -(1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) * u +
      (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) =
      (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) * (1 - u) := by ring
  rw [he] at h
  exact h

theorem egbFixedChargeAMeanDeficitForce_critical_limit (φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanDeficitForce τ φ u) atBot
      (𝓝 (egbFixedChargeAMeanGibbsForceCoefficient φ * (1 - u))) := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hc := egbFixedChargeAMiddleQuadraticShift_critical_limit φ
  have ha : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ ^ 2 * u ^ 2)
      atBot (𝓝 (0 : ℝ)) := by
    simpa using ((egbCoexistenceASymmetricRatio_critical_limit.pow 2).mul (hc.pow 2)).mul (tendsto_const_nhds (x := u ^ 2))
  have hs : Tendsto (fun τ => (1 + egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ * u) ^ 2)
      atBot (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add
      (((egbCoexistenceASymmetricRatio_critical_limit.pow 2).mul hc).mul (tendsto_const_nhds (x := u)))).pow 2
  have h2 : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
  have hn := (ha.sub (tendsto_const_nhds (x := (1 : ℝ)))).mul (egbFixedChargeAMeanDeficitPolynomial_critical_limit φ u)
  have hd := (((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanDenominator_critical_limit φ)).mul h2).mul hs
  have h := hn.div hd (by positivity)
  simp only [Pi.div_def] at h
  have he : (0 - 1) * ((1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5) * (1 - u)) /
      (2 * (6 + 12 * egbFixedChargeACriticalCouplingWeight φ) * 1 * 1) =
      egbFixedChargeAMeanGibbsForceCoefficient φ * (1 - u) := by
    unfold egbFixedChargeAMeanGibbsForceCoefficient
    field_simp <;> ring
  rw [he] at h
  exact h

theorem egbFixedChargeAMeanDeficitForce_measurable (τ φ : ℝ) : Measurable (egbFixedChargeAMeanDeficitForce τ φ) := by
  unfold egbFixedChargeAMeanDeficitForce egbFixedChargeAMeanDeficitPolynomial
  fun_prop

theorem egbFixedChargeAMeanDeficitForce_continuousOn (τ φ : ℝ) :
    ContinuousOn (egbFixedChargeAMeanDeficitForce τ φ) (Icc (0 : ℝ) 1) := by
  unfold egbFixedChargeAMeanDeficitForce
  apply ContinuousOn.div
  · unfold egbFixedChargeAMeanDeficitPolynomial
    fun_prop
  · fun_prop
  · intro u hu
    have hs := (egbFixedChargeAMeanDeficitPathScale_mapsTo τ φ hu).1
    have hd := (egbCoexistenceASymmetricRatio_bounds τ).2
    have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ 2 * egbFixedChargeAMiddleQuadraticShift τ φ * u := by linarith
    have hD := egbFixedChargeAMeanDenominator_pos τ φ
    positivity

end GaloisForLFunctions.HTGeometry
