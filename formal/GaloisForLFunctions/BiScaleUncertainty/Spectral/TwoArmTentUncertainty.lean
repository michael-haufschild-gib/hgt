import GaloisForLFunctions.BiScaleUncertainty.Spectral.AdjacentTentUncertainty

/-!
# A three-tent uncertainty block

Two neighboring even-grid tents and their common odd-grid neighbor form an invariant
three-dimensional block. Its modes have eigenvalues `1` and `1 ± sqrt(2)/2`.
Exact sum-of-squares defects give both sharp energy bounds.
-/

open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
noncomputable section

def twoArmTent (n : ℕ) (a b c : ℝ) : Velocity :=
  a • tentVelocity 0 n + b • tentVelocity 0 (n + 1) + c • tentVelocity (2 * n + 1) 0

private theorem left_adjacent (n : ℕ) : TentAdjacent 0 n (2 * n + 1) 0 := by
  left; simp only [coprimeCenter]; omega

private theorem right_adjacent (n : ℕ) : TentAdjacent 0 (n + 1) (2 * n + 1) 0 := by
  right; simp only [coprimeCenter]; omega

private theorem star_cross (n : ℕ) :
    coprimeProjector 0 (tentVelocity (2 * n + 1) 0) =
      (-1 / 2 : ℝ) • (tentVelocity 0 n + tentVelocity 0 (n + 1)) := by
  apply coprimeProjection_tent_two_neighbors <;> simp only [coprimeCenter] <;> omega

private theorem left_cross (n : ℕ) :
    coprimeProjector (2 * n + 1) (tentVelocity 0 n) =
      (-1 / 2 : ℝ) • tentVelocity (2 * n + 1) 0 :=
  coprimeProjection_tent_one_neighbor (by omega) (left_adjacent n).symm

private theorem right_cross (n : ℕ) :
    coprimeProjector (2 * n + 1) (tentVelocity 0 (n + 1)) =
      (-1 / 2 : ℝ) • tentVelocity (2 * n + 1) 0 :=
  coprimeProjection_tent_one_neighbor (by omega) (right_adjacent n).symm

private theorem inner_left (n : ℕ) :
    ⟪tentVelocity 0 n, tentVelocity (2 * n + 1) 0⟫ = -1 := by
  simp only [inner_tentVelocity_cross, if_neg (left_adjacent n).ne,
    ← tentAdjacent_iff, left_adjacent, ite_true]

private theorem inner_right (n : ℕ) :
    ⟪tentVelocity 0 (n + 1), tentVelocity (2 * n + 1) 0⟫ = -1 := by
  simp only [inner_tentVelocity_cross, if_neg (right_adjacent n).ne,
    ← tentAdjacent_iff, right_adjacent, ite_true]

theorem coprimeUncertainty_twoArm (n : ℕ) (a b c : ℝ) :
    coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c) =
      twoArmTent n (a + c / 2) (b + c / 2) (c + (a + b) / 2) := by
  simp only [coprimeUncertainty, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
    twoArmTent, map_add, map_smul]
  rw [star_cross, left_cross, right_cross]
  simp only [coprimeProjector_apply, coprimeProjection_tent_self]
  module

theorem twoArmTent_norm_sq (n : ℕ) (a b c : ℝ) :
    ‖twoArmTent n a b c‖ ^ 2 = 2 * (a ^ 2 + b ^ 2 + c ^ 2 - a * c - b * c) := by
  have hl : ⟪tentVelocity (2 * n + 1) 0, tentVelocity 0 n⟫ = -1 := by
    rw [real_inner_comm]; exact inner_left n
  have hr : ⟪tentVelocity (2 * n + 1) 0, tentVelocity 0 (n + 1)⟫ = -1 := by
    rw [real_inner_comm]; exact inner_right n
  rw [← real_inner_self_eq_norm_sq]
  simp only [twoArmTent, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_tentVelocity, ite_true, inner_left, inner_right, hl, hr]
  simp only [show n ≠ n + 1 by omega, show n + 1 ≠ n by omega, if_false]
  ring


private theorem twoArmTent_inner (n : ℕ) (a b c x y z : ℝ) :
    ⟪twoArmTent n a b c, twoArmTent n x y z⟫ =
      2 * (a * x + b * y + c * z) - a * z - b * z - c * x - c * y := by
  have hl : ⟪tentVelocity (2 * n + 1) 0, tentVelocity 0 n⟫ = -1 := by
    rw [real_inner_comm]; exact inner_left n
  have hr : ⟪tentVelocity (2 * n + 1) 0, tentVelocity 0 (n + 1)⟫ = -1 := by
    rw [real_inner_comm]; exact inner_right n
  simp only [twoArmTent, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_tentVelocity, ite_true, inner_left, inner_right, hl, hr]
  simp only [show n ≠ n + 1 by omega, show n + 1 ≠ n by omega, if_false]
  ring

theorem twoArmTent_uncertainty_energy (n : ℕ) (a b c : ℝ) :
    ⟪twoArmTent n a b c, coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c)⟫ =
      3 / 2 * (a ^ 2 + b ^ 2) - a * b + c ^ 2 := by
  rw [coprimeUncertainty_twoArm, twoArmTent_inner]
  ring

theorem twoArmTent_lower_defect (n : ℕ) (a b c : ℝ) :
    ⟪twoArmTent n a b c, coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c)⟫ -
      (1 - Real.sqrt 2 / 2) * ‖twoArmTent n a b c‖ ^ 2 =
      (Real.sqrt 2 - 1) / 2 * (a + b + Real.sqrt 2 * c) ^ 2 +
        Real.sqrt 2 / 2 * (a - b) ^ 2 := by
  rw [twoArmTent_uncertainty_energy, twoArmTent_norm_sq]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  linear_combination (-c * (a + b) - (Real.sqrt 2 - 1) * c ^ 2 / 2) * hs

theorem twoArmTent_upper_defect (n : ℕ) (a b c : ℝ) :
    (1 + Real.sqrt 2 / 2) * ‖twoArmTent n a b c‖ ^ 2 -
      ⟪twoArmTent n a b c, coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c)⟫ =
      (1 + Real.sqrt 2) / 2 * (a + b - Real.sqrt 2 * c) ^ 2 +
        Real.sqrt 2 / 2 * (a - b) ^ 2 := by
  rw [twoArmTent_uncertainty_energy, twoArmTent_norm_sq]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  linear_combination (c * (a + b) - (Real.sqrt 2 + 1) * c ^ 2 / 2) * hs

theorem twoArmTent_middle_eigen (n : ℕ) :
    coprimeUncertainty 0 (2 * n + 1) (twoArmTent n 1 (-1) 0) =
      twoArmTent n 1 (-1) 0 := by
  rw [coprimeUncertainty_twoArm]
  norm_num

theorem twoArmTent_lower_eigen (n : ℕ) :
    coprimeUncertainty 0 (2 * n + 1) (twoArmTent n 1 1 (-Real.sqrt 2)) =
      (1 - Real.sqrt 2 / 2) • twoArmTent n 1 1 (-Real.sqrt 2) := by
  rw [coprimeUncertainty_twoArm]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hc : -Real.sqrt 2 + (1 + 1) / 2 =
      (1 - Real.sqrt 2 / 2) * (-Real.sqrt 2) := by nlinarith only [hs]
  simp only [twoArmTent, smul_add, smul_smul, mul_one]
  rw [hc]
  module

theorem twoArmTent_upper_eigen (n : ℕ) :
    coprimeUncertainty 0 (2 * n + 1) (twoArmTent n 1 1 (Real.sqrt 2)) =
      (1 + Real.sqrt 2 / 2) • twoArmTent n 1 1 (Real.sqrt 2) := by
  rw [coprimeUncertainty_twoArm]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hc : Real.sqrt 2 + (1 + 1) / 2 =
      (1 + Real.sqrt 2 / 2) * Real.sqrt 2 := by nlinarith only [hs]
  simp only [twoArmTent, smul_add, smul_smul, mul_one]
  rw [hc]

theorem twoArmTent_eigen_norms (n : ℕ) :
    ‖twoArmTent n 1 (-1) 0‖ ^ 2 = 4 ∧
    ‖twoArmTent n 1 1 (-Real.sqrt 2)‖ ^ 2 = 8 + 4 * Real.sqrt 2 ∧
    ‖twoArmTent n 1 1 (Real.sqrt 2)‖ ^ 2 = 8 - 4 * Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  simp only [twoArmTent_norm_sq]
  constructor
  · ring
  constructor <;> nlinarith only [hs]


/-- The two endpoint eigenvalues are sharp bounds throughout the three-tent block. -/
theorem twoArmTent_energy_bounds (n : ℕ) (a b c : ℝ) :
    (1 - Real.sqrt 2 / 2) * ‖twoArmTent n a b c‖ ^ 2 ≤
      ⟪twoArmTent n a b c, coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c)⟫ ∧
    ⟪twoArmTent n a b c, coprimeUncertainty 0 (2 * n + 1) (twoArmTent n a b c)⟫ ≤
      (1 + Real.sqrt 2 / 2) * ‖twoArmTent n a b c‖ ^ 2 := by
  have hr : 1 ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  constructor <;> apply sub_nonneg.mp
  · rw [twoArmTent_lower_defect]
    positivity
  · rw [twoArmTent_upper_defect]
    positivity

/-- All three modes are nonzero; each displayed eigenvalue belongs to the spectrum. -/
theorem twoArmTent_modes_nonzero (n : ℕ) :
    twoArmTent n 1 (-1) 0 ≠ 0 ∧ twoArmTent n 1 1 (-Real.sqrt 2) ≠ 0 ∧
      twoArmTent n 1 1 (Real.sqrt 2) ≠ 0 := by
  obtain ⟨h0, hl, hu⟩ := twoArmTent_eigen_norms n
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  constructor
  · intro hz; rw [hz, norm_zero] at h0; norm_num at h0
  constructor
  · intro hz; rw [hz, norm_zero] at hl; nlinarith only [hl, hn]
  · intro hz; rw [hz, norm_zero] at hu; nlinarith only [hu, hr]


/-- The three tent coefficients are identifiable; the block has no hidden linear relation. -/
theorem twoArmTent_zero_iff (n : ℕ) (a b c : ℝ) :
    twoArmTent n a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro hz
    have hn := twoArmTent_norm_sq n a b c
    rw [hz, norm_zero] at hn
    have ha : a ^ 2 = 0 := by
      nlinarith only [hn, sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg a, sq_nonneg b]
    have hb : b ^ 2 = 0 := by
      nlinarith only [hn, sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg a, sq_nonneg b]
    have ha0 := sq_eq_zero_iff.mp ha
    have hb0 := sq_eq_zero_iff.mp hb
    refine ⟨ha0, hb0, ?_⟩
    rw [ha0, hb0] at hn
    nlinarith only [hn, sq_nonneg c]
  · rintro ⟨rfl, rfl, rfl⟩; simp [twoArmTent]

#print axioms twoArmTent_zero_iff
#print axioms coprimeUncertainty_twoArm
#print axioms twoArmTent_energy_bounds
#print axioms twoArmTent_modes_nonzero

end
end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
