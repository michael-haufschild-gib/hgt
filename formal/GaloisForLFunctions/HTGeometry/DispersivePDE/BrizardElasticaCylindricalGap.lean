import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaSpatialFrame
import Mathlib.Tactic

/-!
# Cylindrical-frame gap for Brizard's spatial elastica

Section VI of arXiv:2607.21750 uses `1-C²` in denominators when converting the Frenet frame to
cylindrical coordinates.  The paper identifies this gap with
`(κ²-k₀²Ω²)/κ²`.  This module proves that identity from the already certified frame
normalization and classifies its positivity and torsionless zero set.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- The binormal weight is the angular weight divided by squared curvature. -/
theorem spatialCcoefSq_eq_omega (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    spatialCcoefSq k₀ γ ν κ =
      (k₀ : ℝ) ^ 2 * spatialOmegaSq γ ν / (κ : ℝ) ^ 2 := by
  rw [spatialCcoefSq, spatialRadiusFourth, spatialOmegaSq]
  field_simp [k₀.ne_zero, κ.ne_zero, ne_of_gt (spatialOmegaSq_den_pos γ ν)]
  ring

/-- Exact identity following paper equation (81). -/
theorem one_sub_spatialCcoefSq (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    1 - spatialCcoefSq k₀ γ ν κ =
      ((κ : ℝ) ^ 2 - (k₀ : ℝ) ^ 2 * spatialOmegaSq γ ν) / (κ : ℝ) ^ 2 := by
  rw [spatialCcoefSq_eq_omega]
  field_simp [κ.ne_zero]

theorem spatialCcoefSq_nonneg (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    0 ≤ spatialCcoefSq k₀ γ ν κ := by
  rw [spatialCcoefSq_eq_omega]
  exact div_nonneg
    (mul_nonneg (sq_nonneg (k₀ : ℝ)) (spatialOmegaSq_nonneg γ ν))
    (sq_nonneg (κ : ℝ))

/-- Cylindrical coordinates are regular exactly above the angular curvature floor. -/
theorem one_sub_spatialCcoefSq_pos_iff (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    0 < 1 - spatialCcoefSq k₀ γ ν κ ↔
      (k₀ : ℝ) ^ 2 * spatialOmegaSq γ ν < (κ : ℝ) ^ 2 := by
  rw [one_sub_spatialCcoefSq, div_pos_iff]
  have hκ : 0 < (κ : ℝ) ^ 2 := sq_pos_of_ne_zero κ.ne_zero
  constructor
  · rintro (h | h)
    · linarith
    · exact False.elim (not_lt_of_ge (le_of_lt hκ) h.2)
  · intro h
    left
    exact ⟨by linarith, hκ⟩

/-- The binormal coefficient vanishes exactly for a torsionless spatial curve. -/
theorem spatialCcoefSq_eq_zero_iff (k₀ : ℝˣ) (γ ν : ℝ) (κ : ℝˣ) :
    spatialCcoefSq k₀ γ ν κ = 0 ↔ ν = 0 := by
  rw [spatialCcoefSq_eq_omega, div_eq_zero_iff]
  have hden : (κ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 κ.ne_zero
  have hk : (k₀ : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 k₀.ne_zero
  simp only [hden, or_false, mul_eq_zero, hk, false_or]
  exact spatialOmegaSq_eq_zero_iff γ ν

/-- At initial curvature the cylindrical gap is unconditionally positive. -/
theorem initial_spatialCcoefSq_lt_one (k₀ : ℝˣ) (γ ν : ℝ) :
    spatialCcoefSq k₀ γ ν k₀ < 1 := by
  rw [spatialCcoefSq_initial]
  exact spatialOmegaSq_lt_one γ ν

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
