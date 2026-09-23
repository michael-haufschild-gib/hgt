import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Quantum Stag Hunt payoff-to-Ising potential

Closed algebraic consequences of the symmetric binary-game potential map used in
arXiv:2609.02957. Column shifts preserve both Ising parameters and the full potential,
while potential differences reproduce unilateral payoff differences. The noiseless
quantum Stag Hunt has constant interaction `3/4` and neutrality at `sin(Γ)^(2 : ℕ) = 1/6`.
-/

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Pair interaction extracted from a symmetric binary payoff matrix `[[m,n],[r,q]]`. -/
def binaryGameInteraction (m n r q : ℝ) : ℝ := (m + q - r - n) / 4

/-- One-endpoint field extracted from a symmetric binary payoff matrix. -/
def binaryGameField (m n r q : ℝ) : ℝ := (m + n - r - q) / 4

/-- Two-spin potential associated with a symmetric binary payoff matrix. -/
def binaryGamePotential (m n r q s t : ℝ) : ℝ :=
  binaryGameInteraction m n r q * s * t + binaryGameField m n r q * (s + t)

theorem binaryGame_interaction_field_plus (m n r q : ℝ) :
    2 * (binaryGameInteraction m n r q + binaryGameField m n r q) = m - r := by
  simp [binaryGameInteraction, binaryGameField]
  ring

theorem binaryGame_interaction_field_minus (m n r q : ℝ) :
    2 * (binaryGameInteraction m n r q - binaryGameField m n r q) = q - n := by
  simp [binaryGameInteraction, binaryGameField]
  ring

/-- The four potential values are the canonical Ising matrix from the paper. -/
theorem binaryGamePotential_entries (m n r q : ℝ) :
    binaryGamePotential m n r q 1 1 =
        binaryGameInteraction m n r q + 2 * binaryGameField m n r q ∧
    binaryGamePotential m n r q 1 (-1) = -binaryGameInteraction m n r q ∧
    binaryGamePotential m n r q (-1) 1 = -binaryGameInteraction m n r q ∧
    binaryGamePotential m n r q (-1) (-1) =
        binaryGameInteraction m n r q - 2 * binaryGameField m n r q := by
  constructor
  · simp [binaryGamePotential]
    ring
  · constructor
    · simp [binaryGamePotential]
    · constructor
      · simp [binaryGamePotential]
      · simp [binaryGamePotential]
        ring

/-- Potential change against the first opponent action equals the payoff change. -/
theorem binaryGamePotential_first_column_difference (m n r q : ℝ) :
    binaryGamePotential m n r q 1 1 - binaryGamePotential m n r q (-1) 1 = m - r := by
  rw [show binaryGamePotential m n r q 1 1 - binaryGamePotential m n r q (-1) 1 =
    2 * (binaryGameInteraction m n r q + binaryGameField m n r q) by
      simp [binaryGamePotential]
      ring]
  exact binaryGame_interaction_field_plus m n r q

/-- Potential change against the second opponent action equals the payoff change. -/
theorem binaryGamePotential_second_column_difference (m n r q : ℝ) :
    binaryGamePotential m n r q 1 (-1) - binaryGamePotential m n r q (-1) (-1) = n - q := by
  simp [binaryGamePotential, binaryGameInteraction, binaryGameField]
  ring

/-- Adding a constant to either payoff column leaves the interaction invariant. -/
theorem binaryGameInteraction_columnShift (m n r q a b : ℝ) :
    binaryGameInteraction (m + a) (n + b) (r + a) (q + b) =
      binaryGameInteraction m n r q := by
  simp [binaryGameInteraction]
  ring

/-- Adding a constant to either payoff column leaves the field invariant. -/
theorem binaryGameField_columnShift (m n r q a b : ℝ) :
    binaryGameField (m + a) (n + b) (r + a) (q + b) =
      binaryGameField m n r q := by
  simp [binaryGameField]
  ring

/-- Payoff-column gauge shifts leave the entire spin potential invariant. -/
theorem binaryGamePotential_columnShift (m n r q a b s t : ℝ) :
    binaryGamePotential (m + a) (n + b) (r + a) (q + b) s t =
      binaryGamePotential m n r q s t := by
  simp [binaryGamePotential, binaryGameInteraction_columnShift, binaryGameField_columnShift]

/-- Noiseless quantum Stag Hunt interaction from payoff matrix
`[[4, 3 sin(Γ)^(2 : ℕ)], [3 cos(Γ)^(2 : ℕ), 2]]`. -/
def quantumStagHuntNoiselessInteraction (Γ : ℝ) : ℝ :=
  binaryGameInteraction 4 (3 * Real.sin Γ ^ (2 : ℕ)) (3 * Real.cos Γ ^ (2 : ℕ)) 2

/-- Noiseless quantum Stag Hunt field. -/
def quantumStagHuntNoiselessField (Γ : ℝ) : ℝ :=
  binaryGameField 4 (3 * Real.sin Γ ^ (2 : ℕ)) (3 * Real.cos Γ ^ (2 : ℕ)) 2

theorem quantumStagHuntNoiselessInteraction_eq (Γ : ℝ) :
    quantumStagHuntNoiselessInteraction Γ = 3 / 4 := by
  unfold quantumStagHuntNoiselessInteraction binaryGameInteraction
  nlinarith [Real.sin_sq_add_cos_sq Γ]

theorem quantumStagHuntNoiselessField_eq (Γ : ℝ) :
    quantumStagHuntNoiselessField Γ = (-1 + 6 * Real.sin Γ ^ (2 : ℕ)) / 4 := by
  unfold quantumStagHuntNoiselessField binaryGameField
  nlinarith [Real.sin_sq_add_cos_sq Γ]

theorem quantumStagHuntNoiselessField_eq_cos_two_mul (Γ : ℝ) :
    quantumStagHuntNoiselessField Γ = (2 - 3 * Real.cos (2 * Γ)) / 4 := by
  rw [quantumStagHuntNoiselessField_eq, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq Γ]

/-- The quantum action is always a best reply to itself in this payoff family. -/
theorem quantumStagHuntQQGain_nonnegative (Γ : ℝ) :
    0 ≤ 4 - 3 * Real.cos Γ ^ (2 : ℕ) := by
  nlinarith [sq_nonneg (Real.sin Γ), Real.sin_sq_add_cos_sq Γ]

/-- Exact classical-action Nash boundary. -/
theorem quantumStagHuntDDGain_nonnegative_iff (Γ : ℝ) :
    0 ≤ 2 - 3 * Real.sin Γ ^ (2 : ℕ) ↔ Real.sin Γ ^ (2 : ℕ) ≤ 2 / 3 := by
  constructor <;> intro h <;> linarith

/-- Exact noiseless coexistence line. -/
theorem quantumStagHuntNoiselessField_zero_iff (Γ : ℝ) :
    quantumStagHuntNoiselessField Γ = 0 ↔ Real.sin Γ ^ (2 : ℕ) = 1 / 6 := by
  rw [quantumStagHuntNoiselessField_eq]
  constructor <;> intro h <;> linarith

end
end GaloisForLFunctions.HTGeometry
