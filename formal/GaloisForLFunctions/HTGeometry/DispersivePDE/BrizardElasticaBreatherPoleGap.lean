import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherMaxima
import Mathlib.Tactic

/-!
# Uniform pole gaps for Brizard's breather quotients

The positivity results for equations (35)--(36) sharpen to exact global denominator minima.  These
give uniform reciprocal bounds and characterize every point where the minimum is attained.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

theorem akhmedievDenominator_gap_decomposition (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievDenominator φ ξ τ - (1 - Real.cos (φ : ℝ)) =
      (Real.cosh (akhmedievOmega φ * τ) - 1) +
        Real.cos (φ : ℝ) * (1 - Real.cos (akhmedievWaveNumber φ * ξ)) := by
  rw [akhmedievDenominator]
  ring

/-- Exact uniform lower bound for the Akhmediev denominator. -/
theorem akhmedievDenominator_center_le (φ : BreatherAngle) (ξ τ : ℝ) :
    1 - Real.cos (φ : ℝ) ≤ akhmedievDenominator φ ξ τ := by
  have h₁ : 0 ≤ Real.cosh (akhmedievOmega φ * τ) - 1 := by
    linarith [Real.one_le_cosh (akhmedievOmega φ * τ)]
  have h₂ : 0 ≤ Real.cos (φ : ℝ) *
      (1 - Real.cos (akhmedievWaveNumber φ * ξ)) := by
    exact mul_nonneg (breatherAngle_cos_pos φ).le
      (sub_nonneg.mpr (Real.cos_le_one _))
  rw [← sub_nonneg]
  rw [akhmedievDenominator_gap_decomposition]
  exact add_nonneg h₁ h₂

theorem akhmedievDenominator_center (φ : BreatherAngle) :
    akhmedievDenominator φ 0 0 = 1 - Real.cos (φ : ℝ) := by
  simp [akhmedievDenominator]

theorem akhmedievDenominator_eq_center_iff (φ : BreatherAngle) (ξ τ : ℝ) :
    akhmedievDenominator φ ξ τ = 1 - Real.cos (φ : ℝ) ↔
      Real.cosh (akhmedievOmega φ * τ) = 1 ∧
        Real.cos (akhmedievWaveNumber φ * ξ) = 1 := by
  have h₁ : 0 ≤ Real.cosh (akhmedievOmega φ * τ) - 1 := by
    linarith [Real.one_le_cosh (akhmedievOmega φ * τ)]
  have hc := breatherAngle_cos_pos φ
  have h₂ : 0 ≤ 1 - Real.cos (akhmedievWaveNumber φ * ξ) := by
    linarith [Real.cos_le_one (akhmedievWaveNumber φ * ξ)]
  constructor
  · intro h
    have hsum : (Real.cosh (akhmedievOmega φ * τ) - 1) +
        Real.cos (φ : ℝ) * (1 - Real.cos (akhmedievWaveNumber φ * ξ)) = 0 := by
      rw [← akhmedievDenominator_gap_decomposition]
      linarith
    constructor <;> nlinarith
  · rintro ⟨hcosh, hcos⟩
    rw [akhmedievDenominator, hcosh, hcos]
    ring

/-- Uniform bound on the reciprocal denominator controlling the quotient's pole distance. -/
theorem akhmedievDenominator_inv_le (φ : BreatherAngle) (ξ τ : ℝ) :
    (akhmedievDenominator φ ξ τ)⁻¹ ≤ (1 - Real.cos (φ : ℝ))⁻¹ := by
  exact inv_anti₀ (sub_pos.mpr (breatherAngle_cos_lt_one φ))
    (akhmedievDenominator_center_le φ ξ τ)

theorem maDenominator_gap_decomposition (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ ξ τ - (Real.cosh (φ : ℝ) - 1) =
      Real.cosh (φ : ℝ) * (Real.cosh (maWaveNumber φ * ξ) - 1) +
        (1 - Real.cos (maOmega φ * τ)) := by
  rw [maDenominator]
  ring

/-- Exact uniform lower bound for the Ma denominator. -/
theorem maDenominator_center_le (φ : MaAngle) (ξ τ : ℝ) :
    Real.cosh (φ : ℝ) - 1 ≤ maDenominator φ ξ τ := by
  have h₁ : 0 ≤ Real.cosh (φ : ℝ) *
      (Real.cosh (maWaveNumber φ * ξ) - 1) := by
    exact mul_nonneg (Real.cosh_pos _).le
      (sub_nonneg.mpr (Real.one_le_cosh _))
  have h₂ : 0 ≤ 1 - Real.cos (maOmega φ * τ) := by
    linarith [Real.cos_le_one (maOmega φ * τ)]
  rw [← sub_nonneg]
  rw [maDenominator_gap_decomposition]
  exact add_nonneg h₁ h₂

theorem maDenominator_center (φ : MaAngle) :
    maDenominator φ 0 0 = Real.cosh (φ : ℝ) - 1 := by
  simp [maDenominator]

theorem maDenominator_eq_center_iff (φ : MaAngle) (ξ τ : ℝ) :
    maDenominator φ ξ τ = Real.cosh (φ : ℝ) - 1 ↔
      Real.cosh (maWaveNumber φ * ξ) = 1 ∧ Real.cos (maOmega φ * τ) = 1 := by
  have hc := Real.cosh_pos (φ : ℝ)
  have h₁ : 0 ≤ Real.cosh (maWaveNumber φ * ξ) - 1 := by
    linarith [Real.one_le_cosh (maWaveNumber φ * ξ)]
  have h₂ : 0 ≤ 1 - Real.cos (maOmega φ * τ) := by
    linarith [Real.cos_le_one (maOmega φ * τ)]
  constructor
  · intro h
    have hsum : Real.cosh (φ : ℝ) *
          (Real.cosh (maWaveNumber φ * ξ) - 1) +
        (1 - Real.cos (maOmega φ * τ)) = 0 := by
      rw [← maDenominator_gap_decomposition]
      linarith
    constructor <;> nlinarith
  · rintro ⟨hcosh, hcos⟩
    rw [maDenominator, hcosh, hcos, mul_one]

theorem maDenominator_inv_le (φ : MaAngle) (ξ τ : ℝ) :
    (maDenominator φ ξ τ)⁻¹ ≤ (Real.cosh (φ : ℝ) - 1)⁻¹ := by
  exact inv_anti₀ (sub_pos.mpr (maAngle_one_lt_cosh φ))
    (maDenominator_center_le φ ξ τ)

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
