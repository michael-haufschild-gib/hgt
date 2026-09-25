import GaloisForLFunctions.RHTower.ReciprocalFactorialKernelFailure
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Factorial decay is compatible with positivity; the reciprocal-factorial shape is not

With the same diagonal `1/(2k)!`, the rank-one kernel `c_m c_n` with `c_k = 1/√((2k)!)` is positive,
and log-convexity of the factorial puts its off-diagonal entry below the reciprocal factorials:

`1/(√((2m)!)·√((2n)!)) ≤ 1/(m+n)!`.

So a positive kernel may decay factorially.  What it may not do is take the value `1/(m+n)!` off the
diagonal, which lies strictly above that ceiling.  The obstruction is the shape of the reciprocal
factorials, not the rate of decay.
-/

open Nat Matrix

namespace RHTower

/-- The square-root-factorial weight vector. -/
noncomputable def sqrtFactorialVec (m n : ℕ) : Fin 2 → ℝ :=
  ![1 / Real.sqrt ((2 * m)! : ℝ), 1 / Real.sqrt ((2 * n)! : ℝ)]

/-- The rank-one kernel with the same diagonal as the reciprocal factorials. -/
noncomputable def sqrtFactorialBlock (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j => sqrtFactorialVec m n i * sqrtFactorialVec m n j)

/-- It is positive: it is a rank-one Gram. -/
theorem sqrtFactorialBlock_posSemidef (m n : ℕ) : (sqrtFactorialBlock m n).PosSemidef := by
  have hEq : sqrtFactorialBlock m n
      = (Matrix.of (fun (_ : Unit) i => sqrtFactorialVec m n i))ᴴ *
        (Matrix.of (fun (_ : Unit) i => sqrtFactorialVec m n i)) := by
    ext i j
    simp [sqrtFactorialBlock, Matrix.mul_apply]
  rw [hEq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem sqrtFactorialBlock_diag_zero (m n : ℕ) :
    sqrtFactorialBlock m n 0 0 = 1 / ((2 * m)! : ℝ) := by
  have h2m : (0 : ℝ) < ((2 * m)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * m)
  have hval : sqrtFactorialBlock m n 0 0
      = (1 / Real.sqrt ((2 * m)! : ℝ)) * (1 / Real.sqrt ((2 * m)! : ℝ)) := by
    simp [sqrtFactorialBlock, sqrtFactorialVec]
  rw [hval, one_div_mul_one_div, Real.mul_self_sqrt h2m.le]

theorem sqrtFactorialBlock_diag_one (m n : ℕ) :
    sqrtFactorialBlock m n 1 1 = 1 / ((2 * n)! : ℝ) := by
  have h2n : (0 : ℝ) < ((2 * n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * n)
  have hval : sqrtFactorialBlock m n 1 1
      = (1 / Real.sqrt ((2 * n)! : ℝ)) * (1 / Real.sqrt ((2 * n)! : ℝ)) := by
    simp [sqrtFactorialBlock, sqrtFactorialVec]
  rw [hval, one_div_mul_one_div, Real.mul_self_sqrt h2n.le]

/-- **The positive kernel stays below the reciprocal factorials off the diagonal.**  This is exactly
log-convexity of the factorial. -/
theorem sqrtFactorialBlock_offDiag_le (m n : ℕ) :
    sqrtFactorialBlock m n 0 1 ≤ 1 / (((m + n)! : ℕ) : ℝ) := by
  have h2m : (0 : ℝ) < ((2 * m)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * m)
  have h2n : (0 : ℝ) < ((2 * n)! : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * n)
  have hmn : (0 : ℝ) < (((m + n)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (m + n)
  have hentry : sqrtFactorialBlock m n 0 1
      = 1 / (Real.sqrt ((2 * m)! : ℝ) * Real.sqrt ((2 * n)! : ℝ)) := by
    have h : sqrtFactorialBlock m n 0 1
        = (1 / Real.sqrt ((2 * m)! : ℝ)) * (1 / Real.sqrt ((2 * n)! : ℝ)) := by
      simp [sqrtFactorialBlock, sqrtFactorialVec]
    rw [h, one_div_mul_one_div]
  rw [hentry, ← Real.sqrt_mul h2m.le]
  refine one_div_le_one_div_of_le hmn ?_
  have hle : (((m + n)! : ℕ) : ℝ) * (((m + n)! : ℕ) : ℝ) ≤ ((2 * m)! : ℝ) * ((2 * n)! : ℝ) := by
    exact_mod_cast factorial_add_sq_le m n
  calc (((m + n)! : ℕ) : ℝ)
      = Real.sqrt ((((m + n)! : ℕ) : ℝ) * (((m + n)! : ℕ) : ℝ)) := (Real.sqrt_mul_self hmn.le).symm
    _ ≤ Real.sqrt (((2 * m)! : ℝ) * ((2 * n)! : ℝ)) := Real.sqrt_le_sqrt hle

end RHTower
