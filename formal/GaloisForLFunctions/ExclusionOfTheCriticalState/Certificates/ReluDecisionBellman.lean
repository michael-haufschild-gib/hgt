import GaloisForLFunctions.ExclusionOfTheCriticalState.Certificates.BinaryChoiceBellman
import GaloisForLFunctions.HTGeometry.HadamardLipschitz.Activation

/-!
# Exact ReLU realization of finite Bellman decisions

Each binary minimum uses one ReLU and affine operations. The resulting
feedforward evaluation realizes the exact signed-cost Bellman value;
its gate count is the number of branches. Complete binary decisions on
n signs use exactly 2^n - 1 ReLU gates, with no fitted parameters.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman
open HTGeometry.HadamardLipschitz
noncomputable section
variable {α : Type*}

private theorem min_eq_relu (x y : ℝ) : x - relu (x - y) = min x y := by
  by_cases h : x ≤ y
  · rw [relu, max_eq_right (sub_nonpos.mpr h), sub_zero, min_eq_left h]
  · rw [relu, max_eq_left (sub_nonneg.mpr (le_of_not_ge h)), min_eq_right (le_of_not_ge h)]
    ring

/-- A feedforward evaluator with one ReLU at each binary decision. -/
def reluValue (g : α → ℝ) : Tree α → ℝ
  | .leaf a => g a
  | .branch a l b r =>
      let x := a + reluValue g l
      let y := b + reluValue g r
      x - relu (x - y)

def reluGates : Tree α → ℕ
  | .leaf _ => 0
  | .branch _ l _ r => reluGates l + reluGates r + 1

/-- The network output is exactly the optimum over complete routes. -/
theorem reluValue_eq_value (g : α → ℝ) (t : Tree α) : reluValue g t = value g t := by
  induction t with
  | leaf a => rfl
  | branch a l b r ihl ihr =>
    simp only [reluValue, ihl, ihr, min_eq_relu, value]

/-- Complete binary sign selection requires exactly one fewer gate than terminal configurations. -/
theorem choices_reluGates (n : ℕ) (f : (Fin n → Bool) → α) :
    reluGates (choices n f) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [choices, reluGates, pow_succ]
    have hl := ih (fun σ => f (Fin.cases false σ))
    have hr := ih (fun σ => f (Fin.cases true σ))
    omega

/-- The ReLU realization retains the exact Bellman residual certificate for every candidate. -/
theorem reluValue_error_certificate (g : α → ℝ) (W : Tree α → ℝ) (t : Tree α) :
    |W t - reluValue g t| ≤ certificate g W t := by
  rw [reluValue_eq_value]
  exact abs_error_le_certificate g W t

#print axioms reluValue_eq_value
#print axioms choices_reluGates
#print axioms reluValue_error_certificate
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.DecisionBellman
