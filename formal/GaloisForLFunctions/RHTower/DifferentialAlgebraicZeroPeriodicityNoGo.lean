import GaloisForLFunctions.HTGeometry.FiniteJetNonidentifiability

/-!
# Differential algebraicity does not make zero sets periodic

The report's differential-Galois step asserts that differentially algebraic functions have
periodic zero sets.  This is false even in order zero: a nonconstant linear polynomial is
differentially algebraic and its singleton zero set is invariant under no nonzero translation.

Consequently no zero-periodicity dichotomy between differential algebraicity and
hypertranscendence can support the proposed off-line-quartet veto.  The corpus separately proves
that hypertranscendental functional-equation carriers may carry arbitrary finite off-line packets.
-/

set_option maxHeartbeats 800000

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Linear polynomial carrier with its zero at `a`. -/
noncomputable def differentialAlgebraicLinearCarrier (a : ℂ) : ℂ → ℂ :=
  fun z => (Polynomial.X - Polynomial.C a).eval z

/-- Linear polynomial carrier is differentially algebraic. -/
theorem differentialAlgebraic_linearCarrier (a : ℂ) :
    DifferentiallyAlgebraic (differentialAlgebraicLinearCarrier a) := by
  exact GaloisForLFunctions.HTGeometry.differentiallyAlgebraic_polynomial
    (Polynomial.X - Polynomial.C a)

@[simp] theorem differentialAlgebraicLinearCarrier_eq_zero_iff (a z : ℂ) :
    differentialAlgebraicLinearCarrier a z = 0 ↔ z = a := by
  rw [differentialAlgebraicLinearCarrier, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact sub_eq_zero

/-- Its zero set has no nonzero translation period. -/
theorem differentialAlgebraicLinearCarrier_zeroSet_not_periodic
    (a : ℂ) {tau : ℂ} (htau : tau ≠ 0) :
    ¬ ∀ z, differentialAlgebraicLinearCarrier a z = 0 ↔
      differentialAlgebraicLinearCarrier a (z + tau) = 0 := by
  intro hperiodic
  have hzero := (hperiodic a).mp (by simp)
  have : tau = 0 := by simpa [differentialAlgebraicLinearCarrier] using hzero
  exact htau this

end RHTower
