import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspOperatorIntertwining
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
Finite positive derivative moments of the original real compact cusp window.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- The jth actual real derivative of the original compact cusp window. -/
def cuspWindowDerivative (j : ℕ) : ℝ → ℝ := deriv^[j] cuspWindow

theorem cuspWindowDerivative_smooth (j : ℕ) : ContDiff ℝ ∞ (cuspWindowDerivative j) :=
  cuspWindow_smooth.iterate_deriv j

theorem cuspWindowDerivative_support (j : ℕ) :
    tsupport (cuspWindowDerivative j) ⊆ Icc (-1) 1 := by
  induction j with
  | zero => exact cuspWindow_support
  | succ j hj =>
    change tsupport (deriv^[j+1] cuspWindow) ⊆ _
    rw [Function.iterate_succ_apply']
    exact tsupport_deriv_subset.trans hj

theorem cuspWindowDerivative_compact (j : ℕ) : HasCompactSupport (cuspWindowDerivative j) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (cuspWindowDerivative_support j)

theorem cuspWindowDerivative_sq_integrable (j : ℕ) :
    Integrable (fun x : ℝ => cuspWindowDerivative j x^(2 : ℕ)) := by
  apply ((cuspWindowDerivative_smooth j).continuous.pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two] using (cuspWindowDerivative_compact j).mul_right

/-- The finite real squared derivative moments of the original compact window. -/
def cuspWindowMoment (j : ℕ) : ℝ := ∫ x : ℝ, cuspWindowDerivative j x^(2 : ℕ)

theorem cuspWindowMoment_nonneg (j : ℕ) : 0 ≤ cuspWindowMoment j :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- The original window has strictly positive mass, witnessed by its value one at zero. -/
theorem cuspWindowMoment_zero_pos : 0 < cuspWindowMoment 0 := by
  apply integral_pos_of_integrable_nonneg_nonzero
    ((cuspWindowDerivative_smooth 0).continuous.pow 2) (cuspWindowDerivative_sq_integrable 0)
    (fun _ => sq_nonneg _) (x := 0)
  simp [cuspWindowDerivative,cuspWindow,Real.smoothTransition.zero,Real.smoothTransition.one]

end
end RHTower.D4BMModularCore
