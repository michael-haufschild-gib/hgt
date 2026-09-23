import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAWeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Embed fixed charge fractions into the global coexistence family

An auxiliary angle certifies membership in the previous admissible family.
The pressure and temperature weights are independently explicit algebraic
functions; later differentiation never differentiates the auxiliary angle.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAAngle (τ φ : ℝ) : ℝ :=
  arcsin (sqrt (egbFixedChargeACouplingWeight τ φ / egbCoexistenceAMaxCoupling τ))

def egbFixedChargeADenominator (τ φ : ℝ) : ℝ :=
  egbCoexistenceShape τ + 4 * egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ

def egbFixedChargeATemperatureWeight (τ φ : ℝ) : ℝ :=
  4 * (thermalRatio τ + 1) / egbFixedChargeADenominator τ φ

def egbFixedChargeAPressureWeight (τ φ : ℝ) : ℝ :=
  (3 * (thermalRatio τ ^ (2 : ℕ) + 1) + 4 * egbFixedChargeACouplingWeight τ φ * (2 - egbCoexistenceALogKernel τ)) /
    (egbFixedChargeADenominator τ φ * (thermalRatio τ ^ (2 : ℕ) + 1))

theorem egbFixedChargeAAngle_coupling (τ φ : ℝ) :
    egbCoexistenceACouplingWeight τ (egbFixedChargeAAngle τ φ) = egbFixedChargeACouplingWeight τ φ := by
  have hm := egbCoexistenceAMaxCoupling_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  have hr : 0 ≤ egbFixedChargeACouplingWeight τ φ / egbCoexistenceAMaxCoupling τ := div_nonneg hb hm.le
  have hu : egbFixedChargeACouplingWeight τ φ / egbCoexistenceAMaxCoupling τ ≤ 1 :=
    (div_le_one hm).2 (egbFixedChargeACouplingWeight_le_max τ φ)
  have hs := sqrt_nonneg (egbFixedChargeACouplingWeight τ φ / egbCoexistenceAMaxCoupling τ)
  unfold egbCoexistenceACouplingWeight egbFixedChargeAAngle
  rw [sin_arcsin (by linarith) (sqrt_le_one.mpr hu), sq_sqrt hr]
  field_simp

theorem egbFixedChargeADenominator_pos (τ φ : ℝ) : 0 < egbFixedChargeADenominator τ φ := by
  have hD := egbCoexistenceShape_pos τ
  have hH := egbCoexistenceALogKernel_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  unfold egbFixedChargeADenominator
  positivity

theorem egbFixedChargeAAngle_denominator (τ φ : ℝ) :
    egbCoexistenceADenominator τ (egbFixedChargeAAngle τ φ) = egbFixedChargeADenominator τ φ := by
  unfold egbCoexistenceADenominator egbFixedChargeADenominator
  rw [egbFixedChargeAAngle_coupling]

theorem egbFixedChargeADenominator_quadratic (τ φ : ℝ) :
    egbFixedChargeADenominator τ φ * (thermalRatio τ ^ (2 : ℕ) + 1) =
      egbFixedChargeABase τ + egbCoexistenceAQuadraticA τ * egbFixedChargeACouplingWeight τ φ := by
  unfold egbFixedChargeADenominator egbFixedChargeABase egbCoexistenceAQuadraticA
  ring

/-- The original effective-charge weight agrees exactly with the fixed-fraction root. -/
theorem egbFixedChargeAAngle_charge_weight (τ φ : ℝ) :
    egbCoexistenceAChargeWeight τ (egbFixedChargeAAngle τ φ) = egbFixedChargeAWeight τ φ := by
  have hD := egbFixedChargeADenominator_pos τ φ
  have hbalance := egbFixedChargeAWeight_charge_balance τ φ
  have hN : thermalRatio τ ^ (2 : ℕ) * egbFixedChargeADenominator τ φ -
      4 * thermalRatio τ * (thermalRatio τ ^ (2 : ℕ) +
        2 * egbFixedChargeACouplingWeight τ φ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1)) =
    egbCoexistenceAQuadraticC τ + egbFixedChargeALinearCorrection τ * egbFixedChargeACouplingWeight τ φ := by
    unfold egbFixedChargeADenominator egbCoexistenceAQuadraticC egbFixedChargeALinearCorrection egbCoexistenceShape
    ring
  unfold egbCoexistenceAChargeWeight
  rw [egbFixedChargeAAngle_denominator, egbFixedChargeAAngle_coupling, hN]
  apply (div_eq_iff (show egbFixedChargeADenominator τ φ * (thermalRatio τ ^ (2 : ℕ) + 1) ≠ 0 by positivity)).2
  rw [egbFixedChargeADenominator_quadratic]
  simpa only [mul_comm] using hbalance.symm

theorem egbFixedChargeAAngle_temperature_weight (τ φ : ℝ) :
    egbCoexistenceATemperatureWeight τ (egbFixedChargeAAngle τ φ) = egbFixedChargeATemperatureWeight τ φ := by
  unfold egbCoexistenceATemperatureWeight egbFixedChargeATemperatureWeight
  rw [egbFixedChargeAAngle_denominator]

theorem egbFixedChargeAAngle_pressure_weight (τ φ : ℝ) :
    egbCoexistenceAPressureWeight τ (egbFixedChargeAAngle τ φ) = egbFixedChargeAPressureWeight τ φ := by
  unfold egbCoexistenceAPressureWeight egbFixedChargeAPressureWeight
  rw [egbFixedChargeAAngle_coupling, egbFixedChargeAAngle_denominator]

theorem egbFixedChargeATemperatureWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeATemperatureWeight τ φ := by
  rw [← egbFixedChargeAAngle_temperature_weight]
  exact egbCoexistenceATemperatureWeight_pos _ _

theorem egbFixedChargeAPressureWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeAPressureWeight τ φ := by
  rw [← egbFixedChargeAAngle_pressure_weight]
  exact egbCoexistenceAPressureWeight_pos _ _

/-- The remaining effective charge is exactly the complementary fixed angular fraction. -/
theorem egbFixedChargeAWeight_charge_fraction (τ φ : ℝ) :
    egbFixedChargeAWeight τ φ - egbFixedChargeACouplingWeight τ φ = cos φ ^ (2 : ℕ) * egbFixedChargeAWeight τ φ := by
  unfold egbFixedChargeACouplingWeight egbFixedChargeAFraction
  have h := congrArg (fun x : ℝ => x * egbFixedChargeAWeight τ φ) (sin_sq_add_cos_sq φ)
  nlinarith [h]

end GaloisForLFunctions.HTGeometry
