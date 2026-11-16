import GaloisForLFunctions.BiScaleUncertainty.CoprimeProjectionNeighbors

/-!
# Exact uncertainty modes of adjacent arithmetic tents

The two-projection decomposition in arXiv:2611.13129, §8.3, identifies
sum and difference vectors as uncertainty modes. For consecutive tent
spacings their overlap is exactly `-1/2`; hence `2-P-Q` has eigenvalues
`3/2` and `1/2` on their span. Both bounds are attained by explicit
nonzero velocities, independently of the spacing.
-/

open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
noncomputable section

/-- Uncertainty operator for the two arithmetic interpolation projections. -/
def coprimeUncertainty (d e : ℕ) : Velocity →L[ℝ] Velocity :=
  (2 : ℝ) • ContinuousLinearMap.id ℝ Velocity - coprimeProjector d - coprimeProjector e

/-- The first tents of consecutive spacings, with arbitrary real amplitudes. -/
def adjacentTentPair (n : ℕ) (a b : ℝ) : Velocity :=
  a • tentVelocity (n + 1) 0 + b • tentVelocity (n + 2) 0

private theorem first_adjacent (n : ℕ) : TentAdjacent (n + 1) 0 (n + 2) 0 := by
  left
  simp only [coprimeCenter, zero_add, mul_one]

private theorem cross_left (n : ℕ) :
    coprimeProjector (n + 1) (tentVelocity (n + 2) 0) =
      (-1 / 2 : ℝ) • tentVelocity (n + 1) 0 :=
  coprimeProjection_tent_one_neighbor (by omega) (first_adjacent n)

private theorem cross_right (n : ℕ) :
    coprimeProjector (n + 2) (tentVelocity (n + 1) 0) =
      (-1 / 2 : ℝ) • tentVelocity (n + 2) 0 :=
  coprimeProjection_tent_one_neighbor (by omega) (first_adjacent n).symm

private theorem pair_inner (n : ℕ) :
    ⟪tentVelocity (n + 1) 0, tentVelocity (n + 2) 0⟫ = -1 := by
  simp only [inner_tentVelocity_cross, if_neg (first_adjacent n).ne,
    ← tentAdjacent_iff, first_adjacent, ite_true]

/-- The entire two-dimensional uncertainty action is explicit. -/
theorem coprimeUncertainty_adjacent_pair (n : ℕ) (a b : ℝ) :
    coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n a b) =
      adjacentTentPair n (a + b / 2) (b + a / 2) := by
  simp only [coprimeUncertainty, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply, adjacentTentPair, map_add, map_smul]
  rw [cross_left, cross_right]
  simp only [coprimeProjector_apply, coprimeProjection_tent_self]
  module

/-- Squared norm of the pair in its nonorthogonal tent coordinates. -/
theorem adjacentTentPair_norm_sq (n : ℕ) (a b : ℝ) :
    ‖adjacentTentPair n a b‖ ^ 2 = 2 * (a ^ 2 + b ^ 2 - a * b) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [adjacentTentPair, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_tentVelocity,
    ite_true, pair_inner, real_inner_comm (tentVelocity (n + 1) 0)
      (tentVelocity (n + 2) 0)]
  ring

/-- The uncertainty energy is diagonal in the two original tent amplitudes. -/
theorem adjacentTentPair_uncertainty_energy (n : ℕ) (a b : ℝ) :
    ⟪adjacentTentPair n a b,
      coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n a b)⟫ =
        (3 / 2 : ℝ) * (a ^ 2 + b ^ 2) := by
  rw [coprimeUncertainty_adjacent_pair]
  simp only [adjacentTentPair, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_tentVelocity,
    ite_true, pair_inner, real_inner_comm (tentVelocity (n + 1) 0)
      (tentVelocity (n + 2) 0)]
  ring

/-- Exact remainder above the lower uncertainty bound. -/
theorem adjacentTentPair_lower_defect (n : ℕ) (a b : ℝ) :
    ⟪adjacentTentPair n a b,
      coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n a b)⟫ -
        (1 / 2 : ℝ) * ‖adjacentTentPair n a b‖ ^ 2 = (a + b) ^ 2 / 2 := by
  rw [adjacentTentPair_uncertainty_energy, adjacentTentPair_norm_sq]
  ring

/-- Exact remainder below the upper uncertainty bound. -/
theorem adjacentTentPair_upper_defect (n : ℕ) (a b : ℝ) :
    (3 / 2 : ℝ) * ‖adjacentTentPair n a b‖ ^ 2 -
      ⟪adjacentTentPair n a b,
        coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n a b)⟫ =
          (3 / 2 : ℝ) * (a - b) ^ 2 := by
  rw [adjacentTentPair_uncertainty_energy, adjacentTentPair_norm_sq]
  ring

/-- The sum mode attains the upper eigenvalue. -/
theorem adjacentTentPair_upper_eigen (n : ℕ) :
    coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n 1 1) =
      (3 / 2 : ℝ) • adjacentTentPair n 1 1 := by
  rw [coprimeUncertainty_adjacent_pair]
  simp only [adjacentTentPair]
  module

/-- The difference mode attains the lower eigenvalue. -/
theorem adjacentTentPair_lower_eigen (n : ℕ) :
    coprimeUncertainty (n + 1) (n + 2) (adjacentTentPair n 1 (-1)) =
      (1 / 2 : ℝ) • adjacentTentPair n 1 (-1) := by
  rw [coprimeUncertainty_adjacent_pair]
  simp only [adjacentTentPair]
  module

/-- Both extremal modes have positive squared norm. -/
theorem adjacentTentPair_eigen_norms (n : ℕ) :
    ‖adjacentTentPair n 1 1‖ ^ 2 = 2 ∧
      ‖adjacentTentPair n 1 (-1)‖ ^ 2 = 6 := by
  constructor <;> rw [adjacentTentPair_norm_sq] <;> norm_num

#print axioms adjacentTentPair_uncertainty_energy
#print axioms adjacentTentPair_lower_defect
#print axioms adjacentTentPair_upper_defect
#print axioms adjacentTentPair_upper_eigen
#print axioms adjacentTentPair_lower_eigen
#print axioms adjacentTentPair_eigen_norms

end
end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
