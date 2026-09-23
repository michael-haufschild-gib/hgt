import Mathlib

/-!
# Semilocal prolate critical potential

The parity-block Jacobi matrix of a formal prolate operator lies at a double-root critical edge:
its negative squared-Jacobi diagonal cancels, to leading order, against the two neighbouring
off-diagonal products.  This file isolates the exact residual left by that cancellation.

The residual has two equivalent forms.  The first is a four-point expression in consecutive Jacobi
radii.  The second separates a discrete curvature of their squares from a negative sum of adjacent
increment energies.  After subtracting the archimedean affine squared-radius law, this becomes an
exact second difference of the metaplectic anomaly, a universal curvature `4`, and the increment
energies.  Thus the limit-point/limit-circle decision is controlled by a concrete source invariant,
not by the coarse quadratic growth of the parity off-diagonals.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- Four-point residual left after cancelling the double-root diagonal against its two
off-diagonal neighbours. -/
def routeJProlateSourceCriticalResidual (x₀ x₁ x₂ x₃ : ℝ) : ℝ :=
  x₀ * x₁ - x₁ ^ (2 : ℕ) - x₂ ^ (2 : ℕ) + x₂ * x₃

/-- Exact curvature-minus-increment-energy decomposition of the source critical residual. -/
theorem two_mul_routeJProlateSourceCriticalResidual
    (x₀ x₁ x₂ x₃ : ℝ) :
    2 * routeJProlateSourceCriticalResidual x₀ x₁ x₂ x₃ =
      (x₃ ^ (2 : ℕ) - x₂ ^ (2 : ℕ)) - (x₁ ^ (2 : ℕ) - x₀ ^ (2 : ℕ)) -
        ((x₃ - x₂) ^ (2 : ℕ) + (x₁ - x₀) ^ (2 : ℕ)) := by
  unfold routeJProlateSourceCriticalResidual
  ring_nf

/-- Defect of one squared Jacobi-radius increment from the archimedean affine law. -/
def routeJJacobiSquaredIncrementDefect (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a (n + 1) ^ (2 : ℕ) - a n ^ (2 : ℕ) - (2 * (n + 1 : ℝ) + 1 / 2)

/-- The critical residual is exactly a second difference of the metaplectic anomaly, minus
the two adjacent increment energies, plus the universal archimedean curvature `4`. -/
theorem two_mul_routeJProlateSourceCriticalResidual_eq_incrementDefect
    (a : ℕ → ℝ) (n : ℕ) :
    2 * routeJProlateSourceCriticalResidual
        (a (2 * n)) (a (2 * n + 1)) (a (2 * n + 2)) (a (2 * n + 3)) =
      4 +
        routeJJacobiSquaredIncrementDefect a (2 * n + 2) -
        routeJJacobiSquaredIncrementDefect a (2 * n) -
        ((a (2 * n + 3) - a (2 * n + 2)) ^ (2 : ℕ) +
          (a (2 * n + 1) - a (2 * n)) ^ (2 : ℕ)) := by
  rw [two_mul_routeJProlateSourceCriticalResidual]
  unfold routeJJacobiSquaredIncrementDefect
  push_cast
  ring_nf

/-- Positive-phase off-diagonal coefficient of the even prolate parity block. -/
def routeJProlateEvenOffDiagonal (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  a (2 * n) * a (2 * n + 1)

/-- Diagonal coefficient of the even prolate parity block. -/
def routeJProlateEvenDiagonal (a : ℕ → ℝ) (grading : ℝ) (n : ℕ) : ℝ :=
  -(a (2 * n) ^ (2 : ℕ) + a (2 * n - 1) ^ (2 : ℕ)) + (2 * n : ℝ) * grading

/-- At every positive even-parity block, diagonal plus adjacent off-diagonals equals the
grading contribution plus the four-point source critical residual. -/
theorem routeJProlateEven_criticalPotential_succ
    (a : ℕ → ℝ) (grading : ℝ) (n : ℕ) :
    routeJProlateEvenDiagonal a grading (n + 1) +
          routeJProlateEvenOffDiagonal a n +
          routeJProlateEvenOffDiagonal a (n + 1) =
      (2 * (n + 1) : ℝ) * grading +
        routeJProlateSourceCriticalResidual
          (a (2 * n)) (a (2 * n + 1)) (a (2 * n + 2)) (a (2 * n + 3)) := by
  have hpred : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  unfold routeJProlateEvenDiagonal routeJProlateEvenOffDiagonal
    routeJProlateSourceCriticalResidual
  rw [hpred]
  push_cast
  ring_nf

end RHTower
