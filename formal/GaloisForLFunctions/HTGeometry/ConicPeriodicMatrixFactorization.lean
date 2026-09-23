import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

/-!
# The two-periodic conic matrix factorization

The symmetric linear pencil and its linear adjugate factor the projective conic
`c₀c₂-c₁²`.  The coefficient commutators on an even descendant layer form three independent
matrix channels.  This is the finite-rank algebraic core of the periodic conic
hypertranscendence-horizon realization.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- The nondegenerate projective conic potential. -/
def conicHorizonPotential (c : Fin 3 → K) : K :=
  c 0 * c 2 - c 1 ^ (2 : ℕ)

/-- The symmetric linear matrix pencil defining the conic. -/
def conicHorizonMatrix (c : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![c 0, c 1; c 1, c 2]

/-- The linear adjugate pencil. -/
def conicHorizonAdjugate (c : Fin 3 → K) : Matrix (Fin 2) (Fin 2) K :=
  !![c 2, -c 1; -c 1, c 0]

/-- The adjugate followed by the symmetric pencil is the conic potential times the identity. -/
theorem conicHorizonAdjugate_mul_matrix (c : Fin 3 → K) :
    conicHorizonAdjugate c * conicHorizonMatrix c =
      conicHorizonPotential c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conicHorizonAdjugate, conicHorizonMatrix, conicHorizonPotential,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The symmetric pencil followed by its adjugate gives the same scalar factorization. -/
theorem conicHorizonMatrix_mul_adjugate (c : Fin 3 → K) :
    conicHorizonMatrix c * conicHorizonAdjugate c =
      conicHorizonPotential c • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conicHorizonAdjugate, conicHorizonMatrix, conicHorizonPotential,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- Coefficient matrices of the symmetric conic pencil. -/
def conicHorizonMatrixCoefficient : Fin 3 → Matrix (Fin 2) (Fin 2) K
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, 0; 0, 1]

/-- Coefficient matrices of the adjugate pencil. -/
def conicHorizonAdjugateCoefficient : Fin 3 → Matrix (Fin 2) (Fin 2) K
  | 0 => !![0, 0; 0, 1]
  | 1 => !![0, -1; -1, 0]
  | 2 => !![1, 0; 0, 0]

/-- Even-layer coefficient commutator of two periodic conic law operators. -/
def conicHorizonEvenCommutator (i j : Fin 3) : Matrix (Fin 2) (Fin 2) K :=
  conicHorizonAdjugateCoefficient i * conicHorizonMatrixCoefficient j -
    conicHorizonAdjugateCoefficient j * conicHorizonMatrixCoefficient i

theorem conicHorizonEvenCommutator_zero_one :
    conicHorizonEvenCommutator (K := K) 0 1 = !![0, 0; 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conicHorizonEvenCommutator, conicHorizonAdjugateCoefficient,
      conicHorizonMatrixCoefficient]
  all_goals ring

theorem conicHorizonEvenCommutator_zero_two :
    conicHorizonEvenCommutator (K := K) 0 2 = !![-1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conicHorizonEvenCommutator, conicHorizonAdjugateCoefficient,
      conicHorizonMatrixCoefficient]

theorem conicHorizonEvenCommutator_one_two :
    conicHorizonEvenCommutator (K := K) 1 2 = !![0, -2; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conicHorizonEvenCommutator, conicHorizonAdjugateCoefficient,
      conicHorizonMatrixCoefficient]
  all_goals ring

/-- In characteristic zero, the three conic factorization commutator channels admit no linear
cancellation. -/
theorem conicHorizonEvenCommutator_coefficients_zero
    [CharZero K] (a b d : K)
    (h : a • conicHorizonEvenCommutator (K := K) 0 1 +
          b • conicHorizonEvenCommutator (K := K) 0 2 +
          d • conicHorizonEvenCommutator (K := K) 1 2 = 0) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  rw [conicHorizonEvenCommutator_zero_one,
    conicHorizonEvenCommutator_zero_two,
    conicHorizonEvenCommutator_one_two] at h
  have h10 := congrFun (congrFun h (1 : Fin 2)) (0 : Fin 2)
  have h00 := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  have h01 := congrFun (congrFun h (0 : Fin 2)) (1 : Fin 2)
  simp at h10 h00 h01
  exact ⟨h10, h00, h01⟩

end

end GaloisForLFunctions.HTGeometry
