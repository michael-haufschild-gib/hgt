import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAGibbs
import GaloisForLFunctions.HTGeometry.GaussBonnetThermalResponseA

/-!
# Strict thermal slopes at all three coexistence equilibria

Differentiate the exact radial polynomial and transfer its root slopes to
the actual temperature derivative. The two global Gibbs minima have
strictly positive radial thermal response; the intermediate equilibrium
has strictly negative response.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceARadialPolynomialSlope (τ θ v : ℝ) : ℝ :=
  4 * egbCoexistenceAPressureWeight τ θ * v ^ (3 : ℕ) - 3 * egbCoexistenceATemperatureWeight τ θ * v ^ (2 : ℕ) +
    2 * v - 2 * egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ

theorem egbCoexistenceARadialPolynomial_hasDerivAt (τ θ v : ℝ) :
    HasDerivAt (egbCoexistenceARadialPolynomial τ θ) (egbCoexistenceARadialPolynomialSlope τ θ v) v := by
  have h := (((((hasDerivAt_id v).pow 4).const_mul (egbCoexistenceAPressureWeight τ θ)).sub
    (((hasDerivAt_id v).pow 3).const_mul (egbCoexistenceATemperatureWeight τ θ))).add
      ((hasDerivAt_id v).pow 2)).sub ((hasDerivAt_id v).const_mul
        (2 * egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ))
  apply (h.sub_const (egbCoexistenceAChargeWeight τ θ)).congr_deriv
  unfold egbCoexistenceARadialPolynomialSlope
  simp only [id_eq]
  ring

theorem egbCoexistenceARadialPolynomialSlope_factorization (τ θ v : ℝ) :
    egbCoexistenceARadialPolynomialSlope τ θ v = egbCoexistenceAPressureWeight τ θ *
      ((v - egbCoexistenceAMiddleRadius τ θ) * (v - 1) * (v + egbCoexistenceANegativeRootSize τ θ) +
        (v - thermalRatio τ) * (v - 1) * (v + egbCoexistenceANegativeRootSize τ θ) +
        (v - thermalRatio τ) * (v - egbCoexistenceAMiddleRadius τ θ) * (v + egbCoexistenceANegativeRootSize τ θ) +
        (v - thermalRatio τ) * (v - egbCoexistenceAMiddleRadius τ θ) * (v - 1)) := by
  have h := (((((hasDerivAt_id v).sub_const (thermalRatio τ)).const_mul (egbCoexistenceAPressureWeight τ θ)).mul
    ((hasDerivAt_id v).sub_const (egbCoexistenceAMiddleRadius τ θ))).mul
      ((hasDerivAt_id v).sub_const 1)).mul ((hasDerivAt_id v).add_const (egbCoexistenceANegativeRootSize τ θ))
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall (egbCoexistenceARadialPolynomial_full_factorization τ θ))
  calc
    _ = _ := (egbCoexistenceARadialPolynomial_hasDerivAt τ θ v).unique h'
    _ = _ := by
      simp only [Pi.mul_apply, id_eq]
      ring

theorem egbCoexistenceARadialPolynomialSlope_small_pos (τ θ : ℝ) :
    0 < egbCoexistenceARadialPolynomialSlope τ θ (thermalRatio τ) := by
  rw [egbCoexistenceARadialPolynomialSlope_factorization]
  simp only [sub_self, zero_mul, add_zero]
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  have hz := thermalRatio_pos τ
  exact mul_pos hp (mul_pos (mul_pos_of_neg_of_neg
    (sub_neg.mpr (egbCoexistenceAMiddleRadius_bounds τ θ).1) (sub_neg.mpr (thermalRatio_lt_one τ))) (by positivity))

theorem egbCoexistenceARadialPolynomialSlope_large_pos (τ θ : ℝ) :
    0 < egbCoexistenceARadialPolynomialSlope τ θ 1 := by
  rw [egbCoexistenceARadialPolynomialSlope_factorization]
  simp only [sub_self, zero_mul, mul_zero, zero_add, add_zero]
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  exact mul_pos hp (mul_pos (mul_pos (sub_pos.mpr (thermalRatio_lt_one τ))
    (sub_pos.mpr (egbCoexistenceAMiddleRadius_bounds τ θ).2)) (by positivity))

theorem egbCoexistenceARadialPolynomialSlope_middle_neg (τ θ : ℝ) :
    egbCoexistenceARadialPolynomialSlope τ θ (egbCoexistenceAMiddleRadius τ θ) < 0 := by
  rw [egbCoexistenceARadialPolynomialSlope_factorization]
  simp only [sub_self, zero_mul, mul_zero, zero_add, add_zero]
  have hp := egbCoexistenceAPressureWeight_pos τ θ
  have hd := egbCoexistenceANegativeRootSize_pos τ θ
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  exact mul_neg_of_pos_of_neg hp (mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sub_pos.mpr (egbCoexistenceAMiddleRadius_bounds τ θ).1)
      (sub_neg.mpr (egbCoexistenceAMiddleRadius_bounds τ θ).2)) (by positivity))

/-- The actual radial temperature derivative expressed through the coexistence polynomial. -/
theorem egbCoexistenceA_thermal_slope_scaling (k τ θ u : ℝ) :
    deriv (egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ)) (exp k * exp u) =
    (egbCoexistenceARadialPolynomialSlope τ θ (exp u) * exp u * (exp u ^ (2 : ℕ) + 2 * egbCoexistenceACouplingWeight τ θ) -
      egbCoexistenceARadialPolynomial τ θ (exp u) * (3 * exp u ^ (2 : ℕ) + 2 * egbCoexistenceACouplingWeight τ θ)) /
    (4 * Real.pi * exp k ^ (2 : ℕ) * exp u ^ (2 : ℕ) * (exp u ^ (2 : ℕ) + 2 * egbCoexistenceACouplingWeight τ θ) ^ (2 : ℕ)) := by
  have h := (egbTemperatureA_hasDerivAt (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
    (egbCoexistenceACouplingRoot k τ θ) (k + u)).deriv
  rw [exp_add] at h
  rw [h]
  unfold egbTemperatureARadialSlope
  rw [egbCoexistenceA_effective_charge, egbCoexistenceACouplingRoot_sq]
  unfold egbCoexistenceAPressure egbCoexistenceARadialPolynomialSlope egbCoexistenceARadialPolynomial
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  field_simp
  ring

theorem egbCoexistenceA_small_thermal_slope_pos (k τ θ : ℝ) :
    0 < deriv (egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ)) (egbCoexistenceSmallRadius k τ) := by
  have h := egbCoexistenceA_thermal_slope_scaling k τ θ (log (thermalRatio τ))
  rw [exp_log (thermalRatio_pos τ), egbCoexistenceA_stationarity_small, zero_mul, sub_zero] at h
  rw [egbCoexistenceSmallRadius, mul_comm (thermalRatio τ), h]
  have hz := thermalRatio_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  exact div_pos (mul_pos (mul_pos (egbCoexistenceARadialPolynomialSlope_small_pos τ θ) hz) (by positivity)) (by positivity)

theorem egbCoexistenceA_large_thermal_slope_pos (k τ θ : ℝ) :
    0 < deriv (egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ)) (egbCoexistenceLargeRadius k) := by
  have h := egbCoexistenceA_thermal_slope_scaling k τ θ 0
  simp only [exp_zero, mul_one, one_pow, egbCoexistenceA_stationarity_large, zero_mul, sub_zero] at h
  rw [egbCoexistenceLargeRadius, h]
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  exact div_pos (mul_pos (egbCoexistenceARadialPolynomialSlope_large_pos τ θ) (by positivity)) (by positivity)

theorem egbCoexistenceA_middle_thermal_slope_neg (k τ θ : ℝ) :
    deriv (egbTemperatureA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ)) (exp k * egbCoexistenceAMiddleRadius τ θ) < 0 := by
  have h := egbCoexistenceA_thermal_slope_scaling k τ θ (log (egbCoexistenceAMiddleRadius τ θ))
  have hF : egbCoexistenceARadialPolynomial τ θ (egbCoexistenceAMiddleRadius τ θ) = 0 := by
    rw [egbCoexistenceARadialPolynomial_full_factorization]
    simp only [sub_self, mul_zero, zero_mul]
  rw [exp_log (egbCoexistenceAMiddleRadius_pos τ θ), hF, zero_mul, sub_zero] at h
  rw [h]
  have hw := egbCoexistenceAMiddleRadius_pos τ θ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (egbCoexistenceARadialPolynomialSlope_middle_neg τ θ) hw) (by positivity)) (by positivity)

/-- The actual isobaric heat capacity of the small global minimum is strictly positive. -/
theorem egbCoexistenceA_small_heat_capacity_pos (k τ θ l : ℝ) :
    0 < egbHeatCapacityA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceSmallRadius k τ) := by
  have hS := egbEntropyA_radial_slope_pos (egbCoexistenceACouplingRoot k τ θ) l (k + log (thermalRatio τ))
  rw [exp_add, exp_log (thermalRatio_pos τ), mul_comm (exp k)] at hS
  unfold egbHeatCapacityA
  rw [egbCoexistenceA_small_temperature]
  exact div_pos (mul_pos (egbCoexistenceATemperature_pos k τ θ) hS)
    (egbCoexistenceA_small_thermal_slope_pos k τ θ)

/-- The actual isobaric heat capacity of the large global minimum is strictly positive. -/
theorem egbCoexistenceA_large_heat_capacity_pos (k τ θ l : ℝ) :
    0 < egbHeatCapacityA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) l (egbCoexistenceLargeRadius k) := by
  unfold egbHeatCapacityA
  rw [egbCoexistenceA_large_temperature]
  exact div_pos (mul_pos (egbCoexistenceATemperature_pos k τ θ)
    (egbEntropyA_radial_slope_pos (egbCoexistenceACouplingRoot k τ θ) l k))
      (egbCoexistenceA_large_thermal_slope_pos k τ θ)

/-- The unique intervening equilibrium has strictly negative actual isobaric heat capacity. -/
theorem egbCoexistenceA_middle_heat_capacity_neg (k τ θ l : ℝ) :
    egbHeatCapacityA (egbCoexistenceAPressure k τ θ) (egbCoexistenceACharge k τ θ)
      (egbCoexistenceACouplingRoot k τ θ) l (exp k * egbCoexistenceAMiddleRadius τ θ) < 0 := by
  have hS := egbEntropyA_radial_slope_pos (egbCoexistenceACouplingRoot k τ θ) l (k + log (egbCoexistenceAMiddleRadius τ θ))
  rw [exp_add, exp_log (egbCoexistenceAMiddleRadius_pos τ θ)] at hS
  unfold egbHeatCapacityA
  rw [egbCoexistenceA_middle_temperature]
  exact div_neg_of_pos_of_neg (mul_pos (egbCoexistenceATemperature_pos k τ θ) hS)
    (egbCoexistenceA_middle_thermal_slope_neg k τ θ)

end GaloisForLFunctions.HTGeometry
