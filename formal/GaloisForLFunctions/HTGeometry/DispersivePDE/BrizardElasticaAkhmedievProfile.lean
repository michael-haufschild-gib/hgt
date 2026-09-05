import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaNLS
import Mathlib.Tactic

/-!
# Regularity, period, and center height of the printed Akhmediev breather

For the open angle range in paper equation (35), the real denominator is everywhere positive, so
the displayed quotient is globally regular and spatially periodic.  Exact evaluation at its center
also tracks the paper's explicit background normalization `1/sqrt 2`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open GaloisForLFunctions.HTGeometry.FDNLS

/-- Nondegenerate Akhmediev angle range `0<φ<π/2`. -/
abbrev BreatherAngle := {φ : ℝ // 0 < φ ∧ φ < Real.pi / 2}

noncomputable def akhmedievOmega (φ : BreatherAngle) : ℝ := Real.sin (2 * (φ : ℝ))

noncomputable def akhmedievWaveNumber (φ : BreatherAngle) : ℝ :=
  Real.sqrt 2 * Real.sin (φ : ℝ)

noncomputable def akhmedievDenominator (φ : BreatherAngle) (ξ τ : ℝ) : ℝ :=
  Real.cosh (akhmedievOmega φ * τ) -
    Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ)

/-- Real/imaginary expansion of `cosh(Ωτ-2iφ)-cos φ cos(pξ)`. -/
noncomputable def akhmedievNumerator (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  ((Real.cosh (akhmedievOmega φ * τ) * Real.cos (2 * (φ : ℝ)) -
      Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ) : ℝ) : ℂ) -
    Complex.I *
      ((Real.sinh (akhmedievOmega φ * τ) * Real.sin (2 * (φ : ℝ)) : ℝ) : ℂ)

noncomputable def akhmedievBreather (φ : BreatherAngle) (ξ τ : ℝ) : ℂ :=
  -(akhmedievNumerator φ ξ τ / (akhmedievDenominator φ ξ τ : ℂ)) *
      linearPhase 1 0 τ ξ / (Real.sqrt 2 : ℂ)

theorem breatherAngle_cos_pos (φ : BreatherAngle) : 0 < Real.cos (φ : ℝ) := by
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [φ.property.1, Real.pi_pos], φ.property.2⟩

theorem breatherAngle_cos_lt_one (φ : BreatherAngle) : Real.cos (φ : ℝ) < 1 := by
  have hφπ : (φ : ℝ) < Real.pi := by linarith [φ.property.2, Real.pi_pos]
  have h := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, Real.pi_pos.le⟩)
    (show (φ : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨φ.property.1.le, hφπ.le⟩)
    φ.property.1
  simpa using h

/-- Printed Akhmediev denominator never vanishes in its nondegenerate angle range. -/
theorem akhmedievDenominator_pos (φ : BreatherAngle) (ξ τ : ℝ) :
    0 < akhmedievDenominator φ ξ τ := by
  have hcpos := breatherAngle_cos_pos φ
  have hcos := Real.cos_le_one (akhmedievWaveNumber φ * ξ)
  have hprod : Real.cos (φ : ℝ) * Real.cos (akhmedievWaveNumber φ * ξ) ≤
      Real.cos (φ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hcos hcpos.le
  have hcosh := Real.one_le_cosh (akhmedievOmega φ * τ)
  rw [akhmedievDenominator]
  linarith [breatherAngle_cos_lt_one φ]

theorem akhmedievWaveNumber_pos (φ : BreatherAngle) :
    0 < akhmedievWaveNumber φ := by
  rw [akhmedievWaveNumber]
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num))
    (Real.sin_pos_of_pos_of_lt_pi φ.property.1
      (by linarith [φ.property.2, Real.pi_pos]))

/-- Printed spatial period `2π/p`. -/
noncomputable def akhmedievSpatialPeriod (φ : BreatherAngle) : ℝ :=
  2 * Real.pi / akhmedievWaveNumber φ

theorem akhmedievWaveNumber_mul_period (φ : BreatherAngle) :
    akhmedievWaveNumber φ * akhmedievSpatialPeriod φ = 2 * Real.pi := by
  rw [akhmedievSpatialPeriod]
  field_simp [ne_of_gt (akhmedievWaveNumber_pos φ)]

theorem akhmedievDenominator_periodic (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievDenominator φ (ξ + akhmedievSpatialPeriod φ) τ =
      akhmedievDenominator φ ξ τ := by
  rw [akhmedievDenominator, akhmedievDenominator]
  have harg : akhmedievWaveNumber φ * (ξ + akhmedievSpatialPeriod φ) =
      akhmedievWaveNumber φ * ξ + 2 * Real.pi := by
    rw [mul_add, akhmedievWaveNumber_mul_period]
  rw [harg, Real.cos_add_two_pi]

theorem akhmedievNumerator_periodic (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievNumerator φ (ξ + akhmedievSpatialPeriod φ) τ =
      akhmedievNumerator φ ξ τ := by
  rw [akhmedievNumerator, akhmedievNumerator]
  have harg : akhmedievWaveNumber φ * (ξ + akhmedievSpatialPeriod φ) =
      akhmedievWaveNumber φ * ξ + 2 * Real.pi := by
    rw [mul_add, akhmedievWaveNumber_mul_period]
  rw [harg, Real.cos_add_two_pi]

/-- Equation (35) is exactly spatially periodic on its whole regular domain. -/
theorem akhmedievBreather_periodic (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievBreather φ (ξ + akhmedievSpatialPeriod φ) τ =
      akhmedievBreather φ ξ τ := by
  rw [akhmedievBreather, akhmedievBreather, akhmedievNumerator_periodic,
    akhmedievDenominator_periodic]
  simp [linearPhase, staggerPhase]

theorem akhmediev_center_real_ratio (φ : BreatherAngle) :
    -(Real.cos (2 * (φ : ℝ)) - Real.cos (φ : ℝ)) /
        (1 - Real.cos (φ : ℝ)) = 1 + 2 * Real.cos (φ : ℝ) := by
  have hden : 1 - Real.cos (φ : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (breatherAngle_cos_lt_one φ))
  field_simp [hden]
  rw [Real.cos_two_mul]
  ring

/-- Exact center value of the formula as printed, including its `1/sqrt 2` normalization. -/
theorem akhmedievBreather_center (φ : BreatherAngle) :
    akhmedievBreather φ 0 0 =
      (((1 + 2 * Real.cos (φ : ℝ)) / Real.sqrt 2 : ℝ) : ℂ) := by
  rw [akhmedievBreather]
  simp only [akhmedievNumerator, akhmedievDenominator, mul_zero, Real.cosh_zero,
    Real.sinh_zero, Real.cos_zero, mul_one, mul_zero, sub_zero, linearPhase,
    staggerPhase, neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  norm_cast
  rw [← neg_div]
  rw [akhmediev_center_real_ratio]

theorem norm_akhmedievBreather_center (φ : BreatherAngle) :
    ‖akhmedievBreather φ 0 0‖ =
      (1 + 2 * Real.cos (φ : ℝ)) / Real.sqrt 2 := by
  rw [akhmedievBreather_center, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos]
  exact div_pos (by linarith [breatherAngle_cos_pos φ])
    (Real.sqrt_pos.mpr (by norm_num))

/-- The center height is strictly below the unscaled value printed in the following sentence. -/
theorem norm_akhmedievBreather_center_lt_printed (φ : BreatherAngle) :
    ‖akhmedievBreather φ 0 0‖ < 1 + 2 * Real.cos (φ : ℝ) := by
  rw [norm_akhmedievBreather_center]
  have hA : 0 < 1 + 2 * Real.cos (φ : ℝ) := by
    linarith [breatherAngle_cos_pos φ]
  exact div_lt_self hA Real.one_lt_sqrt_two

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
