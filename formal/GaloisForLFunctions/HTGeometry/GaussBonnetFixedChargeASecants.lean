import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAJumps
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeATangents

/-!
# Strict secant bounds for the logarithmic-entropy Clapeyron tangent

Exact positive factorizations place the entropy/volume jump ratio strictly
between the two local inverse pressure responses. The logarithmic terms
have the correct signs by the elementary log inequality, uniformly over
all charge and coupling fractions.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeASmallPressureResponse (w φ τ : ℝ) : ℝ :=
  egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeASmallRadius w φ τ)
def egbFixedChargeALargePressureResponse (w φ τ : ℝ) : ℝ :=
  egbThermalPressureResponseA (exp w * sin φ) (egbFixedChargeALargeRadius w φ τ)

theorem egbFixedChargeASmallPressureResponse_formula (w φ τ : ℝ) :
    egbFixedChargeASmallPressureResponse w φ τ =
      2 * egbFixedChargeALargeRadius w φ τ * thermalRatio τ ^ (3 : ℕ) / (thermalRatio τ ^ (2 : ℕ) + 2 * egbFixedChargeACouplingWeight τ φ) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hz := thermalRatio_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  unfold egbFixedChargeASmallPressureResponse egbThermalPressureResponseA egbFixedChargeASmallRadius
  rw [egbFixedChargeA_coupling_scaling]
  field_simp

theorem egbFixedChargeALargePressureResponse_formula (w φ τ : ℝ) :
    egbFixedChargeALargePressureResponse w φ τ =
      2 * egbFixedChargeALargeRadius w φ τ / (1 + 2 * egbFixedChargeACouplingWeight τ φ) := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  unfold egbFixedChargeALargePressureResponse egbThermalPressureResponseA
  rw [egbFixedChargeA_coupling_scaling]
  field_simp

theorem egbFixedChargeASmallPressureResponse_pos (w φ τ : ℝ) : 0 < egbFixedChargeASmallPressureResponse w φ τ := by
  rw [egbFixedChargeASmallPressureResponse_formula]
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hz := thermalRatio_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  positivity

theorem egbFixedChargeALargePressureResponse_pos (w φ τ : ℝ) : 0 < egbFixedChargeALargePressureResponse w φ τ := by
  rw [egbFixedChargeALargePressureResponse_formula]
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  positivity

theorem egbFixedChargeA_log_upper (τ : ℝ) :
    0 ≤ -3 * log (thermalRatio τ) - (1 - thermalRatio τ ^ (3 : ℕ)) := by
  have h := log_le_sub_one_of_pos (pow_pos (thermalRatio_pos τ) 3)
  simp only [log_pow, Nat.cast_ofNat] at h
  linarith

theorem egbFixedChargeA_log_lower (τ : ℝ) :
    0 ≤ 1 - thermalRatio τ ^ (3 : ℕ) + 3 * thermalRatio τ ^ (3 : ℕ) * log (thermalRatio τ) := by
  have hz := pow_pos (thermalRatio_pos τ) 3
  have h := log_le_sub_one_of_pos (inv_pos.mpr hz)
  simp only [log_inv, log_pow, Nat.cast_ofNat] at h
  have hm := mul_le_mul_of_nonneg_left h hz.le
  have hi := mul_inv_cancel₀ hz.ne'
  nlinarith

/-- Exact positive decomposition of the small-phase secant margin. -/
theorem egbFixedChargeA_small_secant_factorization (w φ τ : ℝ) :
    egbFixedChargeAVolumeJump w φ τ - egbFixedChargeASmallPressureResponse w φ τ * egbFixedChargeAEntropyJump w φ τ =
    (2 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ) / (3 * (thermalRatio τ ^ (2 : ℕ) + 2 * egbFixedChargeACouplingWeight τ φ))) *
      (thermalRatio τ ^ (2 : ℕ) * (1 - thermalRatio τ) ^ (2 : ℕ) * (thermalRatio τ + 2) +
        4 * egbFixedChargeACouplingWeight τ φ * (1 - thermalRatio τ ^ (3 : ℕ) + 3 * thermalRatio τ ^ (3 : ℕ) * log (thermalRatio τ))) := by
  have hz := thermalRatio_pos τ
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  rw [egbFixedChargeAVolumeJump_formula, egbFixedChargeAEntropyJump_formula, egbFixedChargeASmallPressureResponse_formula]
  field_simp
  ring

/-- Exact positive decomposition of the large-phase secant margin. -/
theorem egbFixedChargeA_large_secant_factorization (w φ τ : ℝ) :
    egbFixedChargeALargePressureResponse w φ τ * egbFixedChargeAEntropyJump w φ τ - egbFixedChargeAVolumeJump w φ τ =
    (2 * Real.pi * egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ) / (3 * (1 + 2 * egbFixedChargeACouplingWeight τ φ))) *
      ((1 - thermalRatio τ) ^ (2 : ℕ) * (1 + 2 * thermalRatio τ) +
        4 * egbFixedChargeACouplingWeight τ φ * (-3 * log (thermalRatio τ) - (1 - thermalRatio τ ^ (3 : ℕ)))) := by
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  rw [egbFixedChargeAVolumeJump_formula, egbFixedChargeAEntropyJump_formula, egbFixedChargeALargePressureResponse_formula]
  field_simp
  ring

theorem egbFixedChargeA_small_secant_margin_pos (w φ τ : ℝ) :
    0 < egbFixedChargeAVolumeJump w φ τ - egbFixedChargeASmallPressureResponse w φ τ * egbFixedChargeAEntropyJump w φ τ := by
  rw [egbFixedChargeA_small_secant_factorization]
  have hz := thermalRatio_pos τ
  have hgap := sub_pos.mpr (thermalRatio_lt_one τ)
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hlog := egbFixedChargeA_log_lower τ
  positivity

theorem egbFixedChargeA_large_secant_margin_pos (w φ τ : ℝ) :
    0 < egbFixedChargeALargePressureResponse w φ τ * egbFixedChargeAEntropyJump w φ τ - egbFixedChargeAVolumeJump w φ τ := by
  rw [egbFixedChargeA_large_secant_factorization]
  have hz := thermalRatio_pos τ
  have hgap := sub_pos.mpr (thermalRatio_lt_one τ)
  have hb := (egbFixedChargeACouplingWeight_bounds τ φ).1
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  have hlog := egbFixedChargeA_log_upper τ
  positivity

theorem egbFixedChargeA_small_clapeyron_bound (w φ τ : ℝ) :
    egbFixedChargeASmallPressureResponse w φ τ * egbFixedChargeAClapeyronSlope w φ τ < 1 := by
  have hm := egbFixedChargeA_small_secant_margin_pos w φ τ
  unfold egbFixedChargeAClapeyronSlope
  rw [← mul_div_assoc]
  exact (div_lt_one (egbFixedChargeAVolumeJump_pos w φ τ)).2 (by linarith)

theorem egbFixedChargeA_large_clapeyron_bound (w φ τ : ℝ) :
    1 < egbFixedChargeALargePressureResponse w φ τ * egbFixedChargeAClapeyronSlope w φ τ := by
  have hm := egbFixedChargeA_large_secant_margin_pos w φ τ
  unfold egbFixedChargeAClapeyronSlope
  rw [← mul_div_assoc]
  exact (one_lt_div (egbFixedChargeAVolumeJump_pos w φ τ)).2 (by linarith)

end GaloisForLFunctions.HTGeometry
