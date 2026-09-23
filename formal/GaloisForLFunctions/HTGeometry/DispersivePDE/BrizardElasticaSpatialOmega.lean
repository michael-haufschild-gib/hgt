import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Spatial-knot angular normalization

Equation (662) of arXiv:2607.21750 defines the squared cylindrical parameter
`Ω² = 4ν² / ((2+γ²)² + 4ν²)`.  Its denominator is unconditionally positive.  This module proves
the exact complementary fraction, the global bound `0 ≤ Ω² < 1`, and the precise torsionless
zero set.  These facts justify every later square root involving `1-Ω²` in the spatial-curve
construction.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Paper equation (662), represented directly as a squared real parameter. -/
noncomputable def spatialOmegaSq (γ ν : ℝ) : ℝ :=
  4 * ν ^ (2 : ℕ) / ((2 + γ ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * ν ^ (2 : ℕ))

theorem spatialOmegaSq_den_pos (γ ν : ℝ) :
    0 < (2 + γ ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * ν ^ (2 : ℕ) := by
  have h : 0 < 2 + γ ^ (2 : ℕ) := by positivity
  nlinarith [sq_pos_of_pos h, sq_nonneg ν]

theorem spatialOmegaSq_nonneg (γ ν : ℝ) : 0 ≤ spatialOmegaSq γ ν := by
  rw [spatialOmegaSq]
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg ν))
    (le_of_lt (spatialOmegaSq_den_pos γ ν))

theorem spatialOmegaSq_lt_one (γ ν : ℝ) : spatialOmegaSq γ ν < 1 := by
  rw [spatialOmegaSq, div_lt_one (spatialOmegaSq_den_pos γ ν)]
  have h : 0 < (2 + γ ^ (2 : ℕ)) ^ (2 : ℕ) := sq_pos_of_pos (by positivity)
  linarith

/-- Exact positive reserve below the cylindrical degeneracy wall `Ω² = 1`. -/
theorem one_sub_spatialOmegaSq (γ ν : ℝ) :
    1 - spatialOmegaSq γ ν =
      (2 + γ ^ (2 : ℕ)) ^ (2 : ℕ) / ((2 + γ ^ (2 : ℕ)) ^ (2 : ℕ) + 4 * ν ^ (2 : ℕ)) := by
  rw [spatialOmegaSq]
  field_simp [ne_of_gt (spatialOmegaSq_den_pos γ ν)]
  ring

theorem one_sub_spatialOmegaSq_pos (γ ν : ℝ) :
    0 < 1 - spatialOmegaSq γ ν := by
  linarith [spatialOmegaSq_lt_one γ ν]

/-- The spatial curve is planar exactly on the paper's torsionless wall. -/
theorem spatialOmegaSq_eq_zero_iff (γ ν : ℝ) :
    spatialOmegaSq γ ν = 0 ↔ ν = 0 := by
  rw [spatialOmegaSq, div_eq_zero_iff]
  simp [ne_of_gt (spatialOmegaSq_den_pos γ ν)]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
