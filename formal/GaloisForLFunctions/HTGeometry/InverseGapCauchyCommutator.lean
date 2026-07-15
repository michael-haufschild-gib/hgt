/-
# Inverse-gap energy as a boundary Cauchy commutator

For right-half-plane nodes `w_i = epsilon + i x_i`, commute the Cauchy Gram
`C_ij = 1 / (w_i + conj(w_j))` with a diagonal value packet `v`.  Its entries are

`[C, diag(v)]_ij = (v_j-v_i) / (2 epsilon + i(x_i-x_j))`.

The squared finite Hilbert--Schmidt entry energy is therefore the Lorentzian regularization of
the inverse-square gap energy.  This module is source-agnostic and deliberately has no RHTower
import; source realizations belong in downstream modules.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hadamard

open scoped BigOperators ComplexConjugate
open Complex Matrix

noncomputable section

namespace HTGeometry

/-- The universal Cauchy Gram of a finite right-half-plane packet. -/
def rightHalfPlaneCauchyGram {N : ℕ} (w : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => 1 / (w i + star (w j))

/-- Entrywise commutator with the diagonal value operator. -/
def gramValueCommutator {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => G i j * (v j - v i)

/-- The entrywise definition is the literal matrix commutator with `diag(v)`. -/
theorem gramValueCommutator_eq_matrixCommutator {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    gramValueCommutator G v =
      G * Matrix.diagonal v - Matrix.diagonal v * G := by
  ext i j
  simp [gramValueCommutator, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

/-- The diagonal-value commutator transports a signed three-channel incidence exactly. -/
theorem gramValueCommutator_sub_add {N : ℕ}
    (E B M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    gramValueCommutator (E - B + M) v =
      gramValueCommutator E v - gramValueCommutator B v + gramValueCommutator M v := by
  ext i j
  simp [gramValueCommutator]
  ring

/-- Nodes approaching the imaginary boundary of the right half-plane. -/
def cauchyBoundaryNode {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (i : Fin N) : ℂ :=
  (ε : ℂ) + (x i : ℂ) * I

theorem cauchyBoundaryNode_add_star {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (i j : Fin N) :
    cauchyBoundaryNode ε x i + star (cauchyBoundaryNode ε x j) =
      ((2 * ε : ℝ) : ℂ) + ((x i - x j : ℝ) : ℂ) * I := by
  simp [cauchyBoundaryNode]
  ring

/-- Exact boundary-packet commutator entry. -/
theorem gramValueCommutator_cauchyBoundary_apply {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) (i j : Fin N) :
    gramValueCommutator
        (rightHalfPlaneCauchyGram (cauchyBoundaryNode ε x)) v i j =
      (v j - v i) /
        (((2 * ε : ℝ) : ℂ) + ((x i - x j : ℝ) : ℂ) * I) := by
  rw [gramValueCommutator, rightHalfPlaneCauchyGram,
    cauchyBoundaryNode_add_star]
  simp only [div_eq_mul_inv]
  ring

/-- Squared entry norm is the exact Lorentzian inverse-gap regularization. -/
theorem norm_sq_gramValueCommutator_cauchyBoundary_apply {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) (i j : Fin N) :
    ‖gramValueCommutator
        (rightHalfPlaneCauchyGram (cauchyBoundaryNode ε x)) v i j‖ ^ 2 =
      ‖v j - v i‖ ^ 2 / ((2 * ε) ^ 2 + (x i - x j) ^ 2) := by
  rw [gramValueCommutator_cauchyBoundary_apply, norm_div, div_pow]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

/-- Finite Hilbert--Schmidt entry energy of the regularized Cauchy commutator. -/
def regularizedInverseGapCommutatorEnergy {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) : ℝ :=
  ∑ i, ∑ j,
    ‖gramValueCommutator
        (rightHalfPlaneCauchyGram (cauchyBoundaryNode ε x)) v i j‖ ^ 2

theorem regularizedInverseGapCommutatorEnergy_eq {N : ℕ}
    (ε : ℝ) (x : Fin N → ℝ) (v : Fin N → ℂ) :
    regularizedInverseGapCommutatorEnergy ε x v =
      ∑ i, ∑ j, ‖v j - v i‖ ^ 2 /
        ((2 * ε) ^ 2 + (x i - x j) ^ 2) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact norm_sq_gramValueCommutator_cauchyBoundary_apply ε x v i j

/-- Ordered inverse-gap energy.  For pairwise distinct nodes it is twice the usual `i<j` sum. -/
def orderedInverseGapEnergy {N : ℕ}
    (x : Fin N → ℝ) (v : Fin N → ℂ) : ℝ :=
  ∑ i, ∑ j, ‖v j - v i‖ ^ 2 / (x i - x j) ^ 2

theorem regularizedInverseGapCommutatorEnergy_zero {N : ℕ}
    (x : Fin N → ℝ) (v : Fin N → ℂ) :
    regularizedInverseGapCommutatorEnergy 0 x v = orderedInverseGapEnergy x v := by
  rw [regularizedInverseGapCommutatorEnergy_eq]
  unfold orderedInverseGapEnergy
  simp

end HTGeometry
