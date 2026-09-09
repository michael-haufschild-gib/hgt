import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleState

/-!
# Exact coefficients for the unstable root in mean-radius coordinates

The stable-phase equilibrium quadratic also simplifies the constant term
of the remaining stationary quadratic. Its residual at the mean radius
has an exact logarithmic-kernel remainder.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAMiddleMeanRatio (τ φ : ℝ) : ℝ :=
  (1 + egbCoexistenceASymmetricRatio τ) * egbCoexistenceAMiddleRadius τ (egbFixedChargeAAngle τ φ)
def egbFixedChargeAMiddleMeanLinear (τ φ : ℝ) : ℝ :=
  2 * egbFixedChargeAMeanPressureNumerator τ φ - 8 * (1 + egbCoexistenceASymmetricRatio τ ^ 2)
def egbFixedChargeAMiddleMeanConstant (τ φ : ℝ) : ℝ :=
  -egbFixedChargeAMeanWeight τ φ * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ 2) /
    (1 - egbCoexistenceASymmetricRatio τ ^ 2)

theorem egbFixedChargeAMiddleMeanRatio_pos (τ φ : ℝ) : 0 < egbFixedChargeAMiddleMeanRatio τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMiddleMeanRatio
  exact mul_pos (by positivity) (egbCoexistenceAMiddleRadius_pos τ (egbFixedChargeAAngle τ φ))

theorem egbFixedChargeAMiddleMeanRatio_bounds (τ φ : ℝ) :
    1 - egbCoexistenceASymmetricRatio τ < egbFixedChargeAMiddleMeanRatio τ φ ∧
      egbFixedChargeAMiddleMeanRatio τ φ < 1 + egbCoexistenceASymmetricRatio τ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have h := egbCoexistenceAMiddleRadius_bounds τ (egbFixedChargeAAngle τ φ)
  have hp : 0 < 1 + egbCoexistenceASymmetricRatio τ := by positivity
  constructor
  · have he := mul_lt_mul_of_pos_left h.1 hp
    rw [mul_comm (1 + egbCoexistenceASymmetricRatio τ), egbCoexistenceASymmetricRatio_cross] at he
    exact he
  · simpa only [egbFixedChargeAMiddleMeanRatio, mul_one] using mul_lt_mul_of_pos_left h.2 hp

theorem egbFixedChargeAMiddleRadius_mean_formula (w φ τ : ℝ) :
    egbFixedChargeAMiddleRadius w φ τ = egbFixedChargeAMeanRadius w φ τ * egbFixedChargeAMiddleMeanRatio τ φ := by
  unfold egbFixedChargeAMiddleRadius egbFixedChargeAMiddleMeanRatio
  rw [egbFixedChargeA_large_radius_mean]
  ring

theorem egbFixedChargeAMiddleMeanRatio_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleMeanRatio τ φ) atBot (𝓝 (1 : ℝ)) := by
  have hlo : Tendsto (fun τ => 1 - egbCoexistenceASymmetricRatio τ) atBot (𝓝 (1 : ℝ)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub egbCoexistenceASymmetricRatio_critical_limit
  have hhi : Tendsto (fun τ => 1 + egbCoexistenceASymmetricRatio τ) atBot (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add egbCoexistenceASymmetricRatio_critical_limit
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun τ => (egbFixedChargeAMiddleMeanRatio_bounds τ φ).1.le)
    (fun τ => (egbFixedChargeAMiddleMeanRatio_bounds τ φ).2.le)

theorem egbFixedChargeAMiddleMeanConstant_neg (τ φ : ℝ) : egbFixedChargeAMiddleMeanConstant τ φ < 0 := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hx : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  have hS := egbFixedChargeAMeanWeight_pos τ φ
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  unfold egbFixedChargeAMiddleMeanConstant
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hS) hD) (by positivity)) hx

theorem egbFixedChargeAMiddleMeanConstant_formula (τ φ : ℝ) :
    egbFixedChargeAMiddleMeanConstant τ φ =
      -(1 - egbCoexistenceASymmetricRatio τ ^ 4) + 2 * egbFixedChargeAMeanCoupling τ φ *
        (6 - egbCoexistenceALogKernel τ + (egbCoexistenceALogKernel τ + 2) * egbCoexistenceASymmetricRatio τ ^ 2) := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hx : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ 2 := by nlinarith [hd.1, hd.2]
  unfold egbFixedChargeAMiddleMeanConstant
  apply (div_eq_iff hx.ne').2
  have h := egbFixedChargeAMeanWeight_quadratic τ φ
  unfold egbFixedChargeAMeanQuadraticA egbFixedChargeAMeanQuadraticB egbFixedChargeAMeanQuadraticC at h
  unfold egbFixedChargeAMeanDenominator egbFixedChargeAMeanCoupling
  linear_combination -h

theorem egbFixedChargeAMiddleMeanResidual_formula (τ φ : ℝ) :
    (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
      egbCoexistenceASymmetricRatio τ ^ 2 =
    1 + egbCoexistenceASymmetricRatio τ ^ 2 + egbFixedChargeAMeanCoupling τ φ *
      (-8 * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ 2) + 2 * (egbCoexistenceALogKernel τ + 2)) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMiddleMeanConstant_formula]
  unfold egbFixedChargeAMiddleMeanLinear egbFixedChargeAMeanPressureNumerator
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
