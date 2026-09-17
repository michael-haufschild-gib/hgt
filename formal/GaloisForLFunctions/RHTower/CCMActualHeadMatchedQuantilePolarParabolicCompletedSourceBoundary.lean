import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicSourceBoundary

/-!
# Terminal-completed source boundary for the matched--quantile parabolic carrier

The finite cross-cell current cannot be substituted for its completed source: the oriented interval
from the last quantile boundary to the physical polar endpoint is part of the literal geometry.
This module adds that interval in the same parabolic carrier.  It collapses the quantile side to
one oriented complete interval and computes the exact terminal correction to the strict-cross
source current.  No terminal ordering, sign, or bound is assumed.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Literal oriented terminal interval, from the finite quantile endpoint to the physical polar
coordinate of `T`. -/
def ccmActualHeadQuantileParabolicTerminal (K : ℕ) (T : ℝ) : Fin 3 → ℝ :=
  ccmParabolicMoment (ccmActualHeadQuantilePolarCoordinate (K + 3))
    (ccmActualHeadPolarMassCoordinate T)

/-- Quantile cells together with their literal oriented terminal interval. -/
def ccmActualHeadCompletedQuantileParabolicAggregate (K : ℕ) (T : ℝ) : Fin 3 → ℝ :=
  ccmActualHeadQuantileParabolicAggregate K +
    ccmActualHeadQuantileParabolicTerminal K T

/-- Full matched-minus-completed-quantile parabolic codiagonal. -/
def ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal (K : ℕ) (T : ℝ) : Fin 3 → ℝ :=
  ccmActualHeadMatchedParabolicAggregate K -
    ccmActualHeadCompletedQuantileParabolicAggregate K T

/-- Literal nonzero-mass source boundary for the terminal-completed codiagonal. -/
def ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary (K : ℕ) (T : ℝ) : Fin 3 → ℝ :=
  ccmActualHeadMatchedParabolicAggregate K +
    ccmActualHeadCompletedQuantileParabolicAggregate K T

theorem ccmParabolicMoment_add_adjacent (a b c : ℝ) :
    ccmParabolicMoment a b + ccmParabolicMoment b c =
      ccmParabolicMoment a c := by
  funext i
  fin_cases i <;> simp [ccmParabolicMoment] <;> ring

/-- The finite quantile carrier concatenates without any residual boundary term. -/
theorem ccmActualHeadQuantileParabolicAggregate_eq_moment (K : ℕ) :
    ccmActualHeadQuantileParabolicAggregate K =
      ccmParabolicMoment (ccmActualHeadQuantilePolarCoordinate 2)
        (ccmActualHeadQuantilePolarCoordinate (K + 3)) := by
  induction K with
  | zero =>
      norm_num [ccmActualHeadQuantileParabolicAggregate,
        ccmActualHeadQuantileParabolicMoment]
  | succ K ih =>
      calc
        ccmActualHeadQuantileParabolicAggregate (K + 1) =
            ccmActualHeadQuantileParabolicAggregate K +
              ccmActualHeadQuantileParabolicMoment (K + 3) := by
          simp [ccmActualHeadQuantileParabolicAggregate, Finset.sum_range_succ]
        _ = ccmParabolicMoment (ccmActualHeadQuantilePolarCoordinate 2)
              (ccmActualHeadQuantilePolarCoordinate (K + 4)) := by
          rw [ih]
          exact ccmParabolicMoment_add_adjacent _ _ _

/-- Quantile cells and the oriented terminal collapse to the one completed physical interval. -/
theorem ccmActualHeadCompletedQuantileParabolicAggregate_eq_moment (K : ℕ) (T : ℝ) :
    ccmActualHeadCompletedQuantileParabolicAggregate K T =
      ccmParabolicMoment (ccmActualHeadQuantilePolarCoordinate 2)
        (ccmActualHeadPolarMassCoordinate T) := by
  rw [ccmActualHeadCompletedQuantileParabolicAggregate,
    ccmActualHeadQuantileParabolicAggregate_eq_moment]
  exact ccmParabolicMoment_add_adjacent _ _ _

/-- The zeroth completed codiagonal coordinate is exactly the oriented terminal mass mismatch. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero (K : ℕ) (T : ℝ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T 0 =
      ccmActualHeadQuantilePolarCoordinate (K + 3) -
        ccmActualHeadPolarMassCoordinate T := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
    ccmActualHeadCompletedQuantileParabolicAggregate
    ccmActualHeadQuantileParabolicTerminal
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [ccmActualHeadMatchedParabolicAggregate_zero,
    ccmActualHeadQuantileParabolicAggregate_zero]
  simp [ccmParabolicMoment]

/-- Terminal completion supplies the exact mass lever by which diagonal parabolic energy can see
the second codiagonal coordinate.  Its coefficient is the signed physical endpoint mismatch. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_form (K : ℕ) (T : ℝ) :
    ccmParabolicForm (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T) =
      2 * (ccmActualHeadQuantilePolarCoordinate (K + 3) -
          ccmActualHeadPolarMassCoordinate T) *
          ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T 2 -
        (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T 1) ^ 2 := by
  unfold ccmParabolicForm
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_zero]

theorem ccmParabolicForm_add (v w : Fin 3 → ℝ) :
    ccmParabolicForm (v + w) =
      ccmParabolicForm v + 2 * ccmParabolicPairing v w + ccmParabolicForm w := by
  simp only [ccmParabolicForm, ccmParabolicPairing, Pi.add_apply]
  ring

/-- The terminal-completed source boundary is the exact difference of complete parabolic forms. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_pairing_sourceBoundary
    (K : ℕ) (T : ℝ) :
    ccmParabolicPairing (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T)
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T) =
      ccmParabolicForm (ccmActualHeadMatchedParabolicAggregate K) -
        ccmParabolicForm (ccmActualHeadCompletedQuantileParabolicAggregate K T) := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary
  exact ccmParabolicPairing_sub_add_eq_form_sub _ _

/-- **Completed correction law.** The full source current is the finite strict-cross current less
the terminal's exact interaction with the quantile aggregate and its own parabolic form.  Thus no
terminal term may be discarded while attempting to control the complete source. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolic_pairing_eq_finite_sub_terminal
    (K : ℕ) (T : ℝ) :
    ccmParabolicPairing (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T)
        (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K T) =
      ccmParabolicPairing (ccmActualHeadMatchedQuantileParabolicCodiagonal K)
          (ccmActualHeadMatchedQuantileParabolicSourceBoundary K) -
        (2 * ccmParabolicPairing (ccmActualHeadQuantileParabolicAggregate K)
            (ccmActualHeadQuantileParabolicTerminal K T) +
          ccmParabolicForm (ccmActualHeadQuantileParabolicTerminal K T)) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_pairing_sourceBoundary,
    ccmActualHeadCompletedQuantileParabolicAggregate,
    ccmParabolicForm_add]
  ring

theorem ccmActualHeadPolarMassCoordinate_quantileBoundary (N : ℕ) :
    ccmActualHeadPolarMassCoordinate (ccmOutgoingPrimeQuantileBoundary N) =
      ccmActualHeadQuantilePolarCoordinate N := by
  rfl

theorem ccmParabolicMoment_self (a : ℝ) : ccmParabolicMoment a a = 0 := by
  funext i
  fin_cases i <;> simp [ccmParabolicMoment]

/-- At an exact quantile wall the completed terminal interval vanishes identically. -/
theorem ccmActualHeadQuantileParabolicTerminal_at_quantileBoundary (K : ℕ) :
    ccmActualHeadQuantileParabolicTerminal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3)) = 0 := by
  unfold ccmActualHeadQuantileParabolicTerminal
  rw [ccmActualHeadPolarMassCoordinate_quantileBoundary]
  exact ccmParabolicMoment_self _

/-- The terminal-completed codiagonal is the original mass-neutral codiagonal at every exact
quantile wall. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_at_quantileBoundary
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3)) =
      ccmActualHeadMatchedQuantileParabolicCodiagonal K := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
    ccmActualHeadCompletedQuantileParabolicAggregate
  rw [ccmActualHeadQuantileParabolicTerminal_at_quantileBoundary]
  funext i
  simp [ccmActualHeadMatchedQuantileParabolicCodiagonal,
    ccmActualHeadMatchedParabolicAggregate,
    ccmActualHeadQuantileParabolicAggregate]

/-- **Quantile-wall no-go.** Terminal completion cannot make diagonal parabolic energy observe
the second coordinate at an exact quantile wall: the terminal disappears and the form returns to
the mass-neutral, first-coordinate-only expression. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_form_at_quantileBoundary
    (K : ℕ) :
    ccmParabolicForm (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K
        (ccmOutgoingPrimeQuantileBoundary (K + 3))) =
      -(ccmActualHeadMatchedQuantileParabolicCodiagonal K 1) ^ 2 := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal_at_quantileBoundary,
    ccmActualHeadMatchedQuantileParabolicCodiagonal_form]

end RHTower
