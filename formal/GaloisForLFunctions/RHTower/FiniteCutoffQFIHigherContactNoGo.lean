import GaloisForLFunctions.RHTower.FiniteCutoffCompensatingInfinityNoGo
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The inverse QFI chart adds no compensated zero law

The mixed-qubit boundary coordinate used by the multi-law route is the standard homeomorphism from
the complex plane to the open unit ball.  Its finite antidiagonal coincidence is therefore exactly
equivalent to vanishing of the original two-law sum.  Pulling a finer contact datum back through
the inverse chart reconstructs the finite zeta continuation identically.

Consequently the universal QFI boundary loses the zero datum, while the most direct attempt to
restore it supplies no new arithmetic or global-topological constraint.  A surviving refinement
must produce a boundary gluing law that is not equivalent to applying the inverse chart.
-/

noncomputable section

open Complex Metric

namespace RHTower.DeletionMixedRefinement

/-- Open-ball coordinate underlying the equatorial mixed-qubit chart. -/
def qfiOpenBallCoordinate (w : ℂ) : ℂ :=
  ((Homeomorph.unitBall w : Metric.ball (0 : ℂ) 1) : ℂ)

/-- Explicit radial formula for the QFI open-ball coordinate. -/
theorem qfiOpenBallCoordinate_eq (w : ℂ) :
    qfiOpenBallCoordinate w =
      (Real.sqrt (1 + ‖w‖ ^ (2 : ℕ)))⁻¹ • w := by
  rfl

/-- No finite complex output is identified with another by the QFI chart. -/
theorem qfiOpenBallCoordinate_injective :
    Function.Injective qfiOpenBallCoordinate := by
  intro x y hxy
  apply (Homeomorph.unitBall : ℂ ≃ₜ Metric.ball (0 : ℂ) 1).injective
  exact Subtype.ext hxy

/-- The QFI coordinate intertwines additive negation with the ball antipode. -/
@[simp] theorem qfiOpenBallCoordinate_neg (w : ℂ) :
    qfiOpenBallCoordinate (-w) = -qfiOpenBallCoordinate w := by
  rw [qfiOpenBallCoordinate_eq, qfiOpenBallCoordinate_eq, norm_neg]
  simp

/-- Finite antidiagonal coincidence in the QFI ball is exactly ordinary additive cancellation. -/
theorem qfiAntidiagonal_eq_zero_iff (x y : ℂ) :
    qfiOpenBallCoordinate x + qfiOpenBallCoordinate y = 0 ↔ x + y = 0 := by
  constructor
  · intro h
    have hxy : qfiOpenBallCoordinate x = qfiOpenBallCoordinate (-y) := by
      rw [qfiOpenBallCoordinate_neg]
      linear_combination h
    have := qfiOpenBallCoordinate_injective hxy
    linear_combination this
  · intro h
    have : x = -y := by linear_combination h
    rw [this, qfiOpenBallCoordinate_neg]
    abel

/-- Antidiagonal mismatch of the formation head and continuation correction in the QFI ball. -/
def finiteCutoffQFIAntidiagonalDefect (N : ℕ) (s : ℂ) : ℂ :=
  qfiOpenBallCoordinate (finiteZetaFormationHead N s) +
    qfiOpenBallCoordinate (finiteCutoffContinuationCorrection N s)

/-- The finite QFI antidiagonal condition detects exactly the already known finite continuation. -/
theorem finiteCutoffQFIAntidiagonalDefect_eq_zero_iff
    (N : ℕ) (s : ℂ) :
    finiteCutoffQFIAntidiagonalDefect N s = 0 ↔ finiteCutoffZeta N s = 0 := by
  rw [finiteCutoffQFIAntidiagonalDefect, qfiAntidiagonal_eq_zero_iff,
    finiteZetaFormationHead_add_continuationCorrection]

/-- Inverse of the finite QFI open-ball coordinate. -/
def qfiOpenBallInverse (b : Metric.ball (0 : ℂ) 1) : ℂ :=
  (Homeomorph.unitBall : ℂ ≃ₜ Metric.ball (0 : ℂ) 1).symm b

/-- Pulling a finite QFI coordinate back through its chart returns the original output. -/
theorem qfiOpenBallInverse_coordinate (w : ℂ) :
    qfiOpenBallInverse (Homeomorph.unitBall w) = w := by
  exact (Homeomorph.unitBall : ℂ ≃ₜ Metric.ball (0 : ℂ) 1).left_inv w

/-- The inverse-chart compensated charge is identically the finite zeta continuation. -/
theorem qfiInverseCompensatedCharge_eq_finiteCutoffZeta (N : ℕ) (s : ℂ) :
    qfiOpenBallInverse (Homeomorph.unitBall (finiteZetaFormationHead N s)) +
      qfiOpenBallInverse
        (Homeomorph.unitBall (finiteCutoffContinuationCorrection N s)) =
      finiteCutoffZeta N s := by
  rw [qfiOpenBallInverse_coordinate, qfiOpenBallInverse_coordinate,
    finiteZetaFormationHead_add_continuationCorrection]

end RHTower.DeletionMixedRefinement
