import GaloisForLFunctions.HTGeometry.GaussBonnetThermodynamicPrescriptions
import GaloisForLFunctions.HTGeometry.CPVThermalRadiation

/-!
# Critical universality and heat-capacity poles

Equations (17), (21), (25), and (36) of arXiv:2609.00025v1 become exact
scale-free identities. A polar parameterization covers every split of a positive
effective squared charge into electric charge and Gauss--Bonnet coupling.
The reduced pressure has a certified critical inflection, its compressibility
ratio is `3/8`, and the heat-capacity denominator has two subcritical roots,
a critical double root, and no supercritical root.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def egbCriticalCharge (x θ : ℝ) : ℝ := Real.exp x / Real.sqrt 6 * Real.cos θ
def egbCriticalCouplingRoot (x θ : ℝ) : ℝ := Real.exp x / Real.sqrt 6 * Real.sin θ
def egbCriticalTemperature (x : ℝ) : ℝ := 1 / (3 * Real.pi * Real.exp x)
def egbCriticalPressure (x : ℝ) : ℝ := 1 / (16 * Real.pi * (Real.exp x) ^ (2 : ℕ))

def egbReducedPressure (τ ν : ℝ) : ℝ := 8 * τ / (3 * ν) - 2 / ν ^ (2 : ℕ) + 1 / (3 * ν ^ (4 : ℕ))
def egbReducedPressureD1 (τ ν : ℝ) : ℝ := -8 * τ / (3 * ν ^ (2 : ℕ)) + 4 / ν ^ (3 : ℕ) - 4 / (3 * ν ^ (5 : ℕ))

theorem egbCritical_effective_charge (x θ : ℝ) :
    egbCriticalCharge x θ ^ (2 : ℕ) + egbCriticalCouplingRoot x θ ^ (2 : ℕ) = (Real.exp x) ^ (2 : ℕ) / 6 := by
  unfold egbCriticalCharge egbCriticalCouplingRoot
  rw [mul_pow, div_pow, mul_pow, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 6)]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem egbPressureB_reduced_universality (x θ τ v : ℝ) :
    egbPressureB (τ * egbCriticalTemperature x) (egbCriticalCharge x θ)
      (egbCriticalCouplingRoot x θ) (Real.exp v * Real.exp x) =
        egbCriticalPressure x * egbReducedPressure τ (Real.exp v) := by
  unfold egbPressureB
  rw [egbCritical_effective_charge]
  unfold egbCriticalTemperature egbCriticalPressure egbReducedPressure
  field_simp
  ring

theorem egbCritical_pressure_value (x θ : ℝ) :
    egbPressureB (egbCriticalTemperature x) (egbCriticalCharge x θ)
      (egbCriticalCouplingRoot x θ) (Real.exp x) = egbCriticalPressure x := by
  have h := egbPressureB_reduced_universality x θ 1 0
  norm_num [egbReducedPressure] at h
  exact h

theorem egbCritical_compressibility_ratio (x : ℝ) :
    egbCriticalPressure x * (2 * Real.exp x) / egbCriticalTemperature x = 3 / 8 := by
  unfold egbCriticalPressure egbCriticalTemperature
  field_simp
  ring

theorem egbReducedPressure_derivative (τ v : ℝ) :
    HasDerivAt (egbReducedPressure τ) (egbReducedPressureD1 τ (Real.exp v)) (Real.exp v) := by
  have h1 := (hasDerivAt_const (Real.exp v) (8 * τ)).div
    ((hasDerivAt_id (Real.exp v)).const_mul 3) (by dsimp; positivity)
  have h2 := (hasDerivAt_const (Real.exp v) 2).div
    ((hasDerivAt_id (Real.exp v)).pow 2) (by dsimp; positivity)
  have h3 := (hasDerivAt_const (Real.exp v) 1).div
    (((hasDerivAt_id (Real.exp v)).pow 4).const_mul 3) (by dsimp; positivity)
  apply ((h1.sub h2).add h3).congr_deriv
  dsimp [egbReducedPressureD1]
  field_simp
  ring

theorem egbReducedPressureD1_derivative (τ v : ℝ) :
    HasDerivAt (egbReducedPressureD1 τ)
      (16 * τ / (3 * (Real.exp v) ^ (3 : ℕ)) - 12 / (Real.exp v) ^ (4 : ℕ) +
        20 / (3 * (Real.exp v) ^ (6 : ℕ))) (Real.exp v) := by
  have h1 := (hasDerivAt_const (Real.exp v) (-8 * τ)).div
    (((hasDerivAt_id (Real.exp v)).pow 2).const_mul 3) (by dsimp; positivity)
  have h2 := (hasDerivAt_const (Real.exp v) 4).div
    ((hasDerivAt_id (Real.exp v)).pow 3) (by dsimp; positivity)
  have h3 := (hasDerivAt_const (Real.exp v) 4).div
    (((hasDerivAt_id (Real.exp v)).pow 5).const_mul 3) (by dsimp; positivity)
  apply ((h1.add h2).sub h3).congr_deriv
  dsimp
  field_simp
  ring

theorem egbReducedPressure_critical_inflection :
    HasDerivAt (egbReducedPressure 1) 0 1 ∧ HasDerivAt (egbReducedPressureD1 1) 0 1 := by
  constructor
  · convert egbReducedPressure_derivative 1 0 using 1 <;> norm_num [egbReducedPressureD1]
  · convert egbReducedPressureD1_derivative 1 0 using 1 <;> norm_num

def egbHeatCapacityDenominator (p s : ℝ) : ℝ := 3 * p * s ^ (2 : ℕ) - 6 * s + 3

theorem egbHeatCapacity_critical_double_root (s : ℝ) :
    egbHeatCapacityDenominator 1 s = 3 * (s - 1) ^ (2 : ℕ) := by
  unfold egbHeatCapacityDenominator
  ring

theorem egbHeatCapacity_supercritical_no_pole (q s : ℝ) :
    0 < egbHeatCapacityDenominator (1 + Real.exp q) s := by
  unfold egbHeatCapacityDenominator
  have hs : 0 ≤ Real.exp q * s ^ (2 : ℕ) := mul_nonneg (Real.exp_pos q).le (sq_nonneg s)
  by_cases h : s = 0
  · subst s
    norm_num
  · have hpos : 0 < Real.exp q * s ^ (2 : ℕ) := mul_pos (Real.exp_pos q) (sq_pos_of_ne_zero h)
    nlinarith [sq_nonneg (s - 1)]

theorem egbHeatCapacity_subcritical_factorization (d s : ℝ) :
    egbHeatCapacityDenominator (1 - d ^ (2 : ℕ)) s =
      3 * ((1 - d) * s - 1) * ((1 + d) * s - 1) := by
  unfold egbHeatCapacityDenominator
  ring

theorem egbHeatCapacity_subcritical_two_poles (tau : ℝ) :
    egbHeatCapacityDenominator (1 - CPV.thermalRatio tau ^ (2 : ℕ)) (1 / (1 + CPV.thermalRatio tau)) = 0 ∧
    egbHeatCapacityDenominator (1 - CPV.thermalRatio tau ^ (2 : ℕ)) (1 / (1 - CPV.thermalRatio tau)) = 0 ∧
    1 / (1 + CPV.thermalRatio tau) < 1 / (1 - CPV.thermalRatio tau) := by
  have hp : 0 < 1 + CPV.thermalRatio tau := by linarith [CPV.thermalRatio_pos tau]
  have hm : 0 < 1 - CPV.thermalRatio tau := sub_pos.mpr (CPV.thermalRatio_lt_one tau)
  constructor
  · rw [egbHeatCapacity_subcritical_factorization]
    field_simp
    ring
  constructor
  · rw [egbHeatCapacity_subcritical_factorization]
    field_simp
    ring
  · apply (div_lt_div_iff₀ hp hm).mpr
    linarith [CPV.thermalRatio_pos tau]

/-- The critical inflection also holds for the literal iterated derivative. -/
theorem egbReducedPressure_critical_second_derivative :
    deriv (deriv (egbReducedPressure 1)) 1 = 0 := by
  have heq : Filter.EventuallyEq (nhds (1 : ℝ)) (deriv (egbReducedPressure 1)) (egbReducedPressureD1 1) := by
    filter_upwards [Ioi_mem_nhds (by positivity : (0 : ℝ) < 1)] with x hx
    have hd := (egbReducedPressure_derivative 1 (Real.log x)).deriv
    simpa only [Real.exp_log hx] using hd
  rw [heq.deriv_eq]
  exact egbReducedPressure_critical_inflection.2.deriv

/-- Numerator of the reduced model-B heat capacity. -/
def egbHeatCapacityNumerator (p s : ℝ) : ℝ := 2 * s * (3 * p * s ^ (2 : ℕ) + 6 * s - 1)

/-- The two subcritical denominator zeros have nonzero numerators, so neither cancels. -/
theorem egbHeatCapacity_subcritical_numerators_pos (tau : ℝ) :
    0 < egbHeatCapacityNumerator (1 - CPV.thermalRatio tau ^ (2 : ℕ)) (1 / (1 + CPV.thermalRatio tau)) ∧
    0 < egbHeatCapacityNumerator (1 - CPV.thermalRatio tau ^ (2 : ℕ)) (1 / (1 - CPV.thermalRatio tau)) := by
  have hp : 0 < 1 + CPV.thermalRatio tau := by linarith [CPV.thermalRatio_pos tau]
  have hm : 0 < 1 - CPV.thermalRatio tau := sub_pos.mpr (CPV.thermalRatio_lt_one tau)
  have h1 : (1 / 3 : ℝ) < 1 / (1 + CPV.thermalRatio tau) :=
    (lt_div_iff₀ hp).mpr (by linarith [CPV.thermalRatio_lt_one tau])
  have h2 : (1 / 3 : ℝ) < 1 / (1 - CPV.thermalRatio tau) :=
    (lt_div_iff₀ hm).mpr (by linarith [CPV.thermalRatio_pos tau])
  have hzero := egbHeatCapacity_subcritical_two_poles tau
  have hn1 : 3 * (1 - CPV.thermalRatio tau ^ (2 : ℕ)) * (1 / (1 + CPV.thermalRatio tau)) ^ (2 : ℕ) +
      6 * (1 / (1 + CPV.thermalRatio tau)) - 1 > 0 := by
    have hz := hzero.1
    unfold egbHeatCapacityDenominator at hz
    linarith
  have hn2 : 3 * (1 - CPV.thermalRatio tau ^ (2 : ℕ)) * (1 / (1 - CPV.thermalRatio tau)) ^ (2 : ℕ) +
      6 * (1 / (1 - CPV.thermalRatio tau)) - 1 > 0 := by
    have hz := hzero.2.1
    unfold egbHeatCapacityDenominator at hz
    linarith
  constructor
  · exact mul_pos (by positivity) hn1
  · exact mul_pos (by positivity) hn2

end GaloisForLFunctions.HTGeometry

