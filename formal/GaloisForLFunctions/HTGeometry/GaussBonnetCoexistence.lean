import GaloisForLFunctions.HTGeometry.GaussBonnetThermodynamicPrescriptions
import GaloisForLFunctions.HTGeometry.CPVThermalRadiation

/-!
# Exact small/large coexistence in the area-entropy prescription

A constructive extension of the Gibbs coexistence discussion in
arXiv:2609.00025, equations (19), (30), and (31). Two distinct positive radii
have equal temperature and free energy at the same pressure, charge, and
coupling. An exact squared-factor decomposition identifies them as the only
global minimizers of the off-shell Gibbs functional on all positive radii.
The thermal ratio supplies an unrestricted-real parameterization of (0,1).
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry

open CPV

def egbCoexistenceShape (tau : ℝ) : ℝ := thermalRatio tau ^ 2 + 4 * thermalRatio tau + 1

def egbCoexistenceScale (k tau : ℝ) : ℝ :=
  Real.exp k * thermalRatio tau / Real.sqrt (egbCoexistenceShape tau)

def egbCoexistenceCharge (k tau theta : ℝ) : ℝ := egbCoexistenceScale k tau * Real.cos theta

def egbCoexistenceCouplingRoot (k tau theta : ℝ) : ℝ := egbCoexistenceScale k tau * Real.sin theta

def egbCoexistenceSmallRadius (k tau : ℝ) : ℝ := thermalRatio tau * Real.exp k

def egbCoexistenceLargeRadius (k : ℝ) : ℝ := Real.exp k

def egbCoexistencePressure (k tau : ℝ) : ℝ :=
  3 / (8 * Real.pi * Real.exp k ^ 2 * egbCoexistenceShape tau)

def egbCoexistenceTemperature (k tau : ℝ) : ℝ :=
  (1 + thermalRatio tau) / (Real.pi * Real.exp k * egbCoexistenceShape tau)

def egbCoexistenceGibbs (k tau : ℝ) : ℝ :=
  Real.exp k * thermalRatio tau * (1 + thermalRatio tau) / egbCoexistenceShape tau

/-- Off-shell free energy at prescribed external temperature, pressure, charge and coupling. -/
def egbOffShellGibbs (P T Q a r : ℝ) : ℝ := egbMass P Q a r - T * egbEntropyB r

theorem egbCoexistenceShape_pos (tau : ℝ) : 0 < egbCoexistenceShape tau := by
  unfold egbCoexistenceShape
  nlinarith [thermalRatio_pos tau, sq_nonneg (thermalRatio tau)]

theorem egbCoexistenceScale_pos (k tau : ℝ) : 0 < egbCoexistenceScale k tau :=
  div_pos (mul_pos (Real.exp_pos k) (thermalRatio_pos tau))
    (Real.sqrt_pos.mpr (egbCoexistenceShape_pos tau))

theorem egbCoexistence_effective_charge (k tau theta : ℝ) :
    egbCoexistenceCharge k tau theta ^ 2 + egbCoexistenceCouplingRoot k tau theta ^ 2 =
      Real.exp k ^ 2 * thermalRatio tau ^ 2 / egbCoexistenceShape tau := by
  unfold egbCoexistenceCharge egbCoexistenceCouplingRoot
  have h : (egbCoexistenceScale k tau * Real.cos theta)^2 +
      (egbCoexistenceScale k tau * Real.sin theta)^2 = egbCoexistenceScale k tau ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [h, egbCoexistenceScale, div_pow, mul_pow, Real.sq_sqrt (egbCoexistenceShape_pos tau).le]

theorem egbCoexistence_radii_order (k tau : ℝ) :
    0 < egbCoexistenceSmallRadius k tau ∧
      egbCoexistenceSmallRadius k tau < egbCoexistenceLargeRadius k := by
  constructor
  · exact mul_pos (thermalRatio_pos tau) (Real.exp_pos k)
  · exact mul_lt_of_lt_one_left (Real.exp_pos k) (thermalRatio_lt_one tau)

theorem egbCoexistencePressure_pos (k tau : ℝ) : 0 < egbCoexistencePressure k tau := by
  unfold egbCoexistencePressure
  have h := egbCoexistenceShape_pos tau
  positivity

theorem egbCoexistenceTemperature_pos (k tau : ℝ) : 0 < egbCoexistenceTemperature k tau := by
  unfold egbCoexistenceTemperature
  exact div_pos (by linarith [thermalRatio_pos tau])
    (mul_pos (mul_pos Real.pi_pos (Real.exp_pos k)) (egbCoexistenceShape_pos tau))

/-- The small black-hole branch has the prescribed coexistence temperature. -/
theorem egbCoexistence_small_temperature (k tau theta : ℝ) :
    egbTemperatureB (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
      (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceSmallRadius k tau) =
        egbCoexistenceTemperature k tau := by
  unfold egbTemperatureB
  rw [sub_sub, egbCoexistence_effective_charge]
  unfold egbCoexistencePressure egbCoexistenceSmallRadius egbCoexistenceTemperature
  field_simp [Real.pi_ne_zero, (thermalRatio_pos tau).ne', (egbCoexistenceShape_pos tau).ne']
  unfold egbCoexistenceShape
  ring

/-- The large black-hole branch has exactly the same temperature at the same conserved parameters. -/
theorem egbCoexistence_large_temperature (k tau theta : ℝ) :
    egbTemperatureB (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
      (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceLargeRadius k) =
        egbCoexistenceTemperature k tau := by
  unfold egbTemperatureB
  rw [sub_sub, egbCoexistence_effective_charge]
  unfold egbCoexistencePressure egbCoexistenceLargeRadius egbCoexistenceTemperature
  field_simp [Real.pi_ne_zero, (egbCoexistenceShape_pos tau).ne']
  unfold egbCoexistenceShape
  ring

/-- The entire off-shell landscape factors into the squares of the distances from both phases. -/
theorem egbCoexistence_gibbs_gap_factorization (k tau theta u : ℝ) :
    egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
      (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta) (Real.exp u) -
        egbCoexistenceGibbs k tau =
      (Real.exp u - egbCoexistenceSmallRadius k tau)^2 *
        (Real.exp u - egbCoexistenceLargeRadius k)^2 /
          (2 * Real.exp u * Real.exp k ^ 2 * egbCoexistenceShape tau) := by
  unfold egbOffShellGibbs egbMass egbEntropyB
  rw [egbCoexistence_effective_charge]
  unfold egbCoexistencePressure egbCoexistenceTemperature egbCoexistenceGibbs
    egbCoexistenceSmallRadius egbCoexistenceLargeRadius
  field_simp [Real.pi_ne_zero, (egbCoexistenceShape_pos tau).ne']
  unfold egbCoexistenceShape
  ring

theorem egbCoexistence_gibbs_global_lower_bound (k tau theta u : ℝ) :
    egbCoexistenceGibbs k tau ≤
      egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
        (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta) (Real.exp u) := by
  have h := egbCoexistence_gibbs_gap_factorization k tau theta u
  have hd : 0 < 2 * Real.exp u * Real.exp k ^ 2 * egbCoexistenceShape tau := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos u))
      (sq_pos_of_pos (Real.exp_pos k))) (egbCoexistenceShape_pos tau)
  have hn := div_nonneg (mul_nonneg (sq_nonneg (Real.exp u - egbCoexistenceSmallRadius k tau))
    (sq_nonneg (Real.exp u - egbCoexistenceLargeRadius k))) hd.le
  linarith

/-- Complete global minimizer classification: exactly two distinct positive-radius phases. -/
theorem egbCoexistence_gibbs_minimizers (k tau theta u : ℝ) :
    egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
      (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta) (Real.exp u) =
        egbCoexistenceGibbs k tau ↔
      Real.exp u = egbCoexistenceSmallRadius k tau ∨ Real.exp u = egbCoexistenceLargeRadius k := by
  rw [← sub_eq_zero, egbCoexistence_gibbs_gap_factorization]
  have hd : 2 * Real.exp u * Real.exp k ^ 2 * egbCoexistenceShape tau ≠ 0 := by
    exact ne_of_gt (mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos u))
      (sq_pos_of_pos (Real.exp_pos k))) (egbCoexistenceShape_pos tau))
  simp only [div_eq_zero_iff, hd, or_false, mul_eq_zero, pow_eq_zero_iff (by norm_num : 2 ≠ 0), sub_eq_zero]


/-- The small radius attains the global Gibbs minimum. -/
theorem egbCoexistence_small_gibbs (k tau theta : ℝ) :
    egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
      (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta)
        (egbCoexistenceSmallRadius k tau) = egbCoexistenceGibbs k tau := by
  have hp := (egbCoexistence_radii_order k tau).1
  have h := (egbCoexistence_gibbs_minimizers k tau theta (Real.log (egbCoexistenceSmallRadius k tau))).mpr
    (Or.inl (Real.exp_log hp))
  simpa only [Real.exp_log hp] using h

/-- The distinct large radius attains exactly the same global Gibbs minimum. -/
theorem egbCoexistence_large_gibbs (k tau theta : ℝ) :
    egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
      (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta)
        (egbCoexistenceLargeRadius k) = egbCoexistenceGibbs k tau :=
  (egbCoexistence_gibbs_minimizers k tau theta k).mpr (Or.inr rfl)

/-- The discontinuity in area entropy is explicit. -/
theorem egbCoexistence_entropy_jump (k tau : ℝ) :
    egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k tau) =
      Real.pi * Real.exp k ^ 2 * (1 - thermalRatio tau ^ 2) := by
  unfold egbEntropyB egbCoexistenceLargeRadius egbCoexistenceSmallRadius
  ring

theorem egbCoexistence_entropy_jump_pos (k tau : ℝ) :
    0 < egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k tau) := by
  rw [egbCoexistence_entropy_jump]
  have hr := thermalRatio_pos tau
  have hr1 := thermalRatio_lt_one tau
  exact mul_pos (mul_pos Real.pi_pos (sq_pos_of_pos (Real.exp_pos k))) (by nlinarith)

/-- Equal Gibbs minima produce the exact latent-heat identity at the same pressure and charge. -/
theorem egbCoexistence_latent_heat (k tau theta : ℝ) :
    egbMass (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
        (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceLargeRadius k) -
      egbMass (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
        (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceSmallRadius k tau) =
      egbCoexistenceTemperature k tau *
        (egbEntropyB (egbCoexistenceLargeRadius k) - egbEntropyB (egbCoexistenceSmallRadius k tau)) := by
  have hs := egbCoexistence_small_gibbs k tau theta
  have hl := egbCoexistence_large_gibbs k tau theta
  unfold egbOffShellGibbs at hs hl
  nlinarith

/-- This coexistence family has strictly positive latent heat for every finite ratio parameter. -/
theorem egbCoexistence_latent_heat_pos (k tau theta : ℝ) :
    0 < egbMass (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
        (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceLargeRadius k) -
      egbMass (egbCoexistencePressure k tau) (egbCoexistenceCharge k tau theta)
        (egbCoexistenceCouplingRoot k tau theta) (egbCoexistenceSmallRadius k tau) := by
  rw [egbCoexistence_latent_heat]
  exact mul_pos (egbCoexistenceTemperature_pos k tau) (egbCoexistence_entropy_jump_pos k tau)

/-- Every coexistence state lies below the critical pressure for its effective charge. -/
theorem egbCoexistence_normalized_pressure (k tau theta : ℝ) :
    96 * Real.pi * (egbCoexistenceCharge k tau theta ^ 2 + egbCoexistenceCouplingRoot k tau theta ^ 2) *
      egbCoexistencePressure k tau = 36 * thermalRatio tau ^ 2 / egbCoexistenceShape tau ^ 2 := by
  rw [egbCoexistence_effective_charge]
  unfold egbCoexistencePressure
  field_simp
  ring

theorem egbCoexistence_subcritical (k tau theta : ℝ) :
    96 * Real.pi * (egbCoexistenceCharge k tau theta ^ 2 + egbCoexistenceCouplingRoot k tau theta ^ 2) *
      egbCoexistencePressure k tau < 1 := by
  rw [egbCoexistence_normalized_pressure]
  apply (div_lt_one (sq_pos_of_pos (egbCoexistenceShape_pos tau))).mpr
  have hr := thermalRatio_pos tau
  have hdiff := sq_pos_of_pos (sub_pos.mpr (thermalRatio_lt_one tau))
  have hd : 6 * thermalRatio tau < egbCoexistenceShape tau := by
    unfold egbCoexistenceShape
    nlinarith
  nlinarith [egbCoexistenceShape_pos tau]

/-- A strictly positive free-energy barrier is witnessed at the arithmetic midpoint of the phases. -/
theorem egbCoexistence_midpoint_gap (k tau theta : ℝ) :
    egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
      (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta)
        ((egbCoexistenceSmallRadius k tau + egbCoexistenceLargeRadius k) / 2) -
      egbCoexistenceGibbs k tau =
        Real.exp k * (1 - thermalRatio tau)^4 / (16 * (1 + thermalRatio tau) * egbCoexistenceShape tau) := by
  have hp : 0 < (egbCoexistenceSmallRadius k tau + egbCoexistenceLargeRadius k) / 2 := by
    have h := egbCoexistence_radii_order k tau
    linarith
  have h := egbCoexistence_gibbs_gap_factorization k tau theta
    (Real.log ((egbCoexistenceSmallRadius k tau + egbCoexistenceLargeRadius k) / 2))
  rw [Real.exp_log hp] at h
  rw [h]
  unfold egbCoexistenceSmallRadius egbCoexistenceLargeRadius
  have h1 : 1 + thermalRatio tau ≠ 0 := by linarith [thermalRatio_pos tau]
  rw [show thermalRatio tau * Real.exp k + Real.exp k =
    (1 + thermalRatio tau) * Real.exp k by ring]
  field_simp [h1, (egbCoexistenceShape_pos tau).ne']
  ring

theorem egbCoexistence_midpoint_gap_pos (k tau theta : ℝ) :
    egbCoexistenceGibbs k tau <
      egbOffShellGibbs (egbCoexistencePressure k tau) (egbCoexistenceTemperature k tau)
        (egbCoexistenceCharge k tau theta) (egbCoexistenceCouplingRoot k tau theta)
          ((egbCoexistenceSmallRadius k tau + egbCoexistenceLargeRadius k) / 2) := by
  have h := egbCoexistence_midpoint_gap k tau theta
  have hn := mul_pos (Real.exp_pos k) (pow_pos (sub_pos.mpr (thermalRatio_lt_one tau)) 4)
  have hd : 0 < 16 * (1 + thermalRatio tau) * egbCoexistenceShape tau := by
    exact mul_pos (mul_pos (by norm_num) (by linarith [thermalRatio_pos tau])) (egbCoexistenceShape_pos tau)
  have hp := div_pos hn hd
  linarith

end GaloisForLFunctions.HTGeometry
