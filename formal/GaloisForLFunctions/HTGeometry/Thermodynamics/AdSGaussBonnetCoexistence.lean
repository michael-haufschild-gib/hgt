import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetCoexistenceParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exact global coexistence of two black-hole radii

The potential on the constructive coexistence surface factors as two
squared root factors times a positive quadratic. This certifies exactly
two global black-hole minima, their attainment, and a strictly positive
entropy gap. Thermal AdS is a separate competitor at zero charge.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

/-- Eliminating charge and temperature leaves one algebraic coexistence equation. -/
theorem coexistence_parameter_equation (τ θ : ℝ) :
    coexistenceSum τ θ ^ 4 - coexistenceProduct τ θ * coexistenceSum τ θ ^ 2 +
      3 * coexistenceProduct τ θ ^ 2 - coexistenceSum τ θ ^ 2 - coexistenceProduct τ θ +
      6 * coexistenceCoupling τ θ * (3 * coexistenceSum τ θ ^ 2 - 3 * coexistenceProduct τ θ + 1) = 0 := by
  have hK := (coexistence_polynomials_pos τ).2.2.2
  have hd : 3 * coexistenceK (CPV.thermalRatio τ) * coexistenceRadius τ θ ^ 2 + 1 ≠ 0 := by positivity
  unfold coexistenceSum coexistenceProduct coexistenceCoupling
  field_simp [hd]
  unfold coexistenceN coexistenceD coexistenceK
  ring

theorem coexistence_quadratic_coefficient (τ θ : ℝ) :
    coexistenceConstant τ θ - 2 * coexistenceSum τ θ * coexistenceLinear τ θ +
      coexistenceSum τ θ ^ 2 + 2 * coexistenceProduct τ θ = 1 := by
  have heq := coexistence_parameter_equation τ θ
  unfold coexistenceConstant coexistenceLinear
  field_simp [(coexistenceDenominator_pos τ θ).ne']
  unfold coexistenceDenominator
  nlinarith only [heq]

theorem coexistence_cubic_coefficient (τ θ : ℝ) :
    (coexistenceSum τ θ ^ 2 + 2 * coexistenceProduct τ θ) * coexistenceLinear τ θ -
      2 * coexistenceSum τ θ * coexistenceConstant τ θ -
      2 * coexistenceSum τ θ * coexistenceProduct τ θ =
        -6 * coexistenceCoupling τ θ * (2 * coexistenceSum τ θ - coexistenceLinear τ θ) := by
  unfold coexistenceConstant coexistenceLinear
  field_simp [(coexistenceDenominator_pos τ θ).ne']
  unfold coexistenceDenominator
  ring

theorem coexistence_linear_coefficient (τ θ : ℝ) :
    coexistenceProduct τ θ ^ 2 * coexistenceLinear τ θ -
      2 * coexistenceSum τ θ * coexistenceProduct τ θ * coexistenceConstant τ θ = 0 := by
  unfold coexistenceConstant coexistenceLinear
  ring

private theorem two_root_expansion (S P B C x : ℝ) :
    (x ^ 2 - S * x + P) ^ 2 * (x ^ 2 + B * x + C) =
      x ^ 6 + (B - 2 * S) * x ^ 5 + (C - 2 * S * B + S ^ 2 + 2 * P) * x ^ 4 +
      ((S ^ 2 + 2 * P) * B - 2 * S * C - 2 * S * P) * x ^ 3 +
      ((S ^ 2 + 2 * P) * C - 2 * S * P * B + P ^ 2) * x ^ 2 +
      (P ^ 2 * B - 2 * S * P * C) * x + P ^ 2 * C := by ring

theorem coexistence_potential_gap (τ θ u : ℝ) :
    potential (coexistenceTemperature τ θ) 0 (coexistenceCoupling τ θ)
        (coexistenceCharge τ θ) (Real.exp u) - coexistenceMinimum τ θ =
      3 * (Real.exp u - CPV.thermalRatio τ * coexistenceRadius τ θ) ^ 2 *
        (Real.exp u - coexistenceRadius τ θ) ^ 2 *
        (Real.exp u ^ 2 + coexistenceLinear τ θ * Real.exp u + coexistenceConstant τ θ) /
        Real.exp u ^ 2 := by
  have hp : (Real.exp u - CPV.thermalRatio τ * coexistenceRadius τ θ) *
      (Real.exp u - coexistenceRadius τ θ) =
        Real.exp u ^ 2 - coexistenceSum τ θ * Real.exp u + coexistenceProduct τ θ := by
    unfold coexistenceSum coexistenceProduct
    ring
  have hf := two_root_expansion (coexistenceSum τ θ) (coexistenceProduct τ θ)
    (coexistenceLinear τ θ) (coexistenceConstant τ θ) (Real.exp u)
  rw [coexistence_quadratic_coefficient, coexistence_cubic_coefficient,
    coexistence_linear_coefficient] at hf
  have hs : (Real.exp u - CPV.thermalRatio τ * coexistenceRadius τ θ) ^ 2 *
      (Real.exp u - coexistenceRadius τ θ) ^ 2 =
        (Real.exp u ^ 2 - coexistenceSum τ θ * Real.exp u + coexistenceProduct τ θ) ^ 2 := by
    rw [← mul_pow, hp]
  rw [show 3 * (Real.exp u - CPV.thermalRatio τ * coexistenceRadius τ θ) ^ 2 *
      (Real.exp u - coexistenceRadius τ θ) ^ 2 =
        3 * ((Real.exp u - CPV.thermalRatio τ * coexistenceRadius τ θ) ^ 2 *
          (Real.exp u - coexistenceRadius τ θ) ^ 2) by ring, hs]
  unfold potential energy entropy
  rw [coexistenceCharge_sq]
  unfold coexistenceMinimum coexistenceTemperature
  field_simp
  nlinarith only [hf]

theorem coexistence_residual_pos (τ θ u : ℝ) :
    0 < Real.exp u ^ 2 + coexistenceLinear τ θ * Real.exp u + coexistenceConstant τ θ := by
  have hb := coexistenceLinear_nonneg τ θ
  have hc := coexistenceConstant_nonneg τ θ
  positivity

/-- These are global minima over every positive black-hole radius. -/
theorem coexistence_global_lower_bound (τ θ u : ℝ) :
    coexistenceMinimum τ θ ≤ potential (coexistenceTemperature τ θ) 0
      (coexistenceCoupling τ θ) (coexistenceCharge τ θ) (Real.exp u) := by
  apply sub_nonneg.mp
  rw [coexistence_potential_gap]
  have hf := coexistence_residual_pos τ θ u
  positivity

theorem coexistence_exactly_two_minimizers (τ θ u : ℝ) :
    potential (coexistenceTemperature τ θ) 0 (coexistenceCoupling τ θ)
        (coexistenceCharge τ θ) (Real.exp u) = coexistenceMinimum τ θ ↔
      Real.exp u = CPV.thermalRatio τ * coexistenceRadius τ θ ∨ Real.exp u = coexistenceRadius τ θ := by
  rw [← sub_eq_zero, coexistence_potential_gap, div_eq_zero_iff]
  simp only [pow_ne_zero 2 (Real.exp_ne_zero u), or_false, mul_eq_zero,
    (coexistence_residual_pos τ θ u).ne', show (3 : ℝ) ≠ 0 by norm_num, false_or,
    pow_eq_zero_iff (by norm_num : 2 ≠ 0), sub_eq_zero]

theorem coexistence_minima_attained (τ θ : ℝ) :
    potential (coexistenceTemperature τ θ) 0 (coexistenceCoupling τ θ) (coexistenceCharge τ θ)
        (CPV.thermalRatio τ * coexistenceRadius τ θ) = coexistenceMinimum τ θ ∧
      potential (coexistenceTemperature τ θ) 0 (coexistenceCoupling τ θ) (coexistenceCharge τ θ)
        (coexistenceRadius τ θ) = coexistenceMinimum τ θ := by
  have hsmall := mul_pos (CPV.thermalRatio_pos τ) (coexistenceRadius_pos τ θ)
  have hlarge := coexistenceRadius_pos τ θ
  constructor
  · have h := (coexistence_exactly_two_minimizers τ θ
      (Real.log (CPV.thermalRatio τ * coexistenceRadius τ θ))).mpr (Or.inl (Real.exp_log hsmall))
    simpa only [Real.exp_log hsmall] using h
  · have h := (coexistence_exactly_two_minimizers τ θ (Real.log (coexistenceRadius τ θ))).mpr
      (Or.inr (Real.exp_log hlarge))
    simpa only [Real.exp_log hlarge] using h

theorem coexistence_radii_distinct (τ θ : ℝ) :
    CPV.thermalRatio τ * coexistenceRadius τ θ < coexistenceRadius τ θ := by
  have h := mul_lt_mul_of_pos_right (CPV.thermalRatio_lt_one τ) (coexistenceRadius_pos τ θ)
  simpa only [one_mul] using h

theorem coexistence_entropy_gap (τ θ : ℝ) :
    entropy (coexistenceCoupling τ θ) (coexistenceRadius τ θ) -
        entropy (coexistenceCoupling τ θ) (CPV.thermalRatio τ * coexistenceRadius τ θ) =
      4 * Real.pi * coexistenceRadius τ θ * (1 - CPV.thermalRatio τ) *
        (coexistenceRadius τ θ ^ 2 * (1 + CPV.thermalRatio τ + CPV.thermalRatio τ ^ 2) +
          6 * coexistenceCoupling τ θ) := by
  unfold entropy
  ring

theorem coexistence_entropy_gap_pos (τ θ : ℝ) :
    0 < entropy (coexistenceCoupling τ θ) (coexistenceRadius τ θ) -
      entropy (coexistenceCoupling τ θ) (CPV.thermalRatio τ * coexistenceRadius τ θ) := by
  rw [coexistence_entropy_gap]
  have hk := CPV.thermalRatio_pos τ
  have hgap := sub_pos.mpr (CPV.thermalRatio_lt_one τ)
  have hr := coexistenceRadius_pos τ θ
  have hl := coexistenceCoupling_nonneg τ θ
  positivity

#print axioms coexistence_potential_gap
#print axioms coexistence_exactly_two_minimizers
#print axioms coexistence_minima_attained
#print axioms coexistence_entropy_gap_pos

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
