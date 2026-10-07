import GaloisForLFunctions.HTGeometry.SteinitzInverseCovariance

/-!
# Exact scalar reduction of the Steinitz inverse remainder

Every nonnegative diagonal covariance is realized by a diagonal synthesis.
Its regularized inverse and matrix remainder are explicit. The remainder is
exactly twice the inverse-branch scalar remainder from the source, coordinate
by coordinate, formally identifying the scalar and noncommutative constructions.
-/

open Matrix
open scoped Matrix NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Diagonal synthesis realizes every nonnegative diagonal covariance. -/
def diagonalCovarianceSynthesis (w : Fin d → ℝ≥0) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal fun i => (Real.sqrt (w i) : ℂ)

@[simp] theorem diagonalCovarianceSynthesis_covariance (w : Fin d → ℝ≥0) :
    diagonalCovarianceSynthesis w * (diagonalCovarianceSynthesis w)ᴴ =
      diagonal (fun i => ((w i : ℝ) : ℂ)) := by
  simp only [diagonalCovarianceSynthesis, diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext i
  simp [← Complex.ofReal_mul]

@[simp] theorem diagonalCovarianceSynthesis_regularization (w : Fin d → ℝ≥0) :
    synthesisRegularizedCovariance (diagonalCovarianceSynthesis w) =
      diagonal (fun i => ((1 + (w i : ℝ) : ℝ) : ℂ)) := by
  rw [synthesisRegularizedCovariance_eq, diagonalCovarianceSynthesis_covariance,
    ← diagonal_one, diagonal_add]
  congr 1
  funext i
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  exact add_comm _ _

@[simp] theorem diagonalCovarianceSynthesis_resolvent (w : Fin d → ℝ≥0) :
    synthesisResolvent (diagonalCovarianceSynthesis w) =
      diagonal (fun i => (((1 + (w i : ℝ))⁻¹ : ℝ) : ℂ)) := by
  unfold synthesisResolvent
  rw [diagonalCovarianceSynthesis_regularization]
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt (by positivity)), Complex.ofReal_one]

/-- The noncommutative remainder recovers exactly twice the paper's scalar inverse branch. -/
theorem synthesisInverseRemainder_diagonal (r s : Fin d → ℝ≥0) :
    synthesisInverseRemainder (diagonalCovarianceSynthesis r) (diagonalCovarianceSynthesis s) =
      diagonal (fun i => ((2 * steinitzInverseBranchRemainder (1 + r i) (1 + s i) : ℝ) : ℂ)) := by
  simp only [synthesisInverseRemainder, diagonalCovarianceSynthesis_resolvent,
    diagonalCovarianceSynthesis_regularization, diagonal_sub, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [steinitzInverseBranchRemainder_regularized]
  push_cast
  have hr : (1 : ℂ) + ((r i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + r i by positivity))
  have hs : (1 : ℂ) + ((s i : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show (0 : ℝ) < 1 + s i by positivity))
  field_simp [hr, hs]
  ring

end

end GaloisForLFunctions.HTGeometry
