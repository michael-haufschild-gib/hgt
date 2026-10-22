import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCompleteAccountingOfTheWork
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkChangesSignOnce

/-!
# The core dominance criterion

The accounting of the signed work has one explicit positive piece — the core
`Σ_{n ≤ T} ψ_ε(n)/(n(n+1))`, the pronic average of the damped Chebyshev prefix — and three pieces
that involve the deviation of the source from the constant one, plus the explicit polar correction.
The core is not small: `ψ_ε(n)` grows like `n^{1-ε}`, so the core grows like `1/ε` as the damping
decreases, and it is the natural unit against which the deviation terms must be measured.

Hence the criterion: if at every horizon and every damping below one half the two linear
functionals of the deviation and its quadratic dilation form together stay below the core plus the
polar correction, then the signed work is nonnegative and the Riemann hypothesis follows
(`riemannHypothesis_of_core_dominance`).

Every quantity in the hypothesis is named: the core and the polar correction are explicit, the two
linear terms pair the deviation against explicit rows, and the quadratic term is bounded by the
prime-dilation series times the deviation's energy.  The criterion is therefore a *comparison in
explicit units*, not a bound with an unspecified constant.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-- The explicit positive core of the work at horizon `T` and damping `ε`. -/
def workCore (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, dampedPrimePrefix ε n / ((n : ℝ) * ((n : ℝ) + 1))

/-- The first linear functional of the deviation: against the prime-weighted window means of the
constant row. -/
def workLinearWindow (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 T, dampedPrimeWeight ε j *
    pronicPairing T (rowFibreAverage j T (fun _ => 1)) (deviationRow ε)

/-- The second linear functional of the deviation: against the damped Chebyshev prefix. -/
def workLinearPrefix (ε : ℝ) (T : ℕ) : ℝ :=
  pronicPairing T (deviationRow ε) (dampedPrimePrefix ε)

/-- The quadratic term: the deviation's own dilation form. -/
def workQuadratic (ε : ℝ) (T : ℕ) : ℝ := rowDilationForm ε T (deviationRow ε)

theorem signedDampingWork_eq_core_add (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T =
      workCore ε T + workLinearWindow ε T + workLinearPrefix ε T + workQuadratic ε T +
        polarDilationCorrection ε T := by
  rw [workCore, workLinearWindow, workLinearPrefix, workQuadratic]
  exact signedDampingWork_accounting ε T

/-- **The core dominance criterion.**  If the deviation terms stay below the core plus the polar
correction, the work is nonnegative and the Riemann hypothesis follows. -/
theorem riemannHypothesis_of_core_dominance
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      |workLinearWindow ε T| + |workLinearPrefix ε T| + |workQuadratic ε T| ≤
        workCore ε T + polarDilationCorrection ε T) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_nonneg_signedWork fun T ε hε hε2 => ?_
  have hid := signedDampingWork_eq_core_add ε T
  have hbound := h T ε hε hε2
  have h2 := neg_abs_le (workLinearWindow ε T)
  have h3 := neg_abs_le (workLinearPrefix ε T)
  have h4 := neg_abs_le (workQuadratic ε T)
  linarith

/-- The quadratic term, in the units of the deviation's energy. -/
theorem abs_workQuadratic_le (ε : ℝ) (T : ℕ) :
    |workQuadratic ε T| ≤
      (∑ j ∈ Icc 1 T, dampedPrimeWeight ε j * (1 / Real.sqrt (j : ℝ))) *
        pronicNorm T (deviationRow ε) ^ 2 :=
  abs_rowDilationForm_deviationRow_le ε T

/-- The core is nonnegative, and strictly positive from the second horizon on. -/
theorem workCore_pos (ε : ℝ) {T : ℕ} (hT : 2 ≤ T) : 0 < workCore ε T := by
  rw [workCore, ← rowDilationForm_one_eq]
  exact rowDilationForm_one_pos ε hT

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
