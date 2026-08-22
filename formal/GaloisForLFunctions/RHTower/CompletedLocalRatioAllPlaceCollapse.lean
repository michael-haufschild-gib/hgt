import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The regularized completed local ratio is trivial

The completed Riemann zeta functional equation identifies the numerator and
denominator of its reflected ratio.  Filling the removable zero-over-zero
values by one therefore gives a globally constant symbol.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The completion-compatible filling of the reflected completed-zeta ratio. -/
def regularizedCompletedLocalRatio (s : ℂ) : ℂ :=
  if completedRiemannZeta (1 - s) = 0 then 1
  else completedRiemannZeta s / completedRiemannZeta (1 - s)

/-- The filled reflected completed-zeta ratio is identically one. -/
theorem regularizedCompletedLocalRatio_eq_one (s : ℂ) :
    regularizedCompletedLocalRatio s = 1 := by
  unfold regularizedCompletedLocalRatio
  split_ifs with h
  · rfl
  · rw [← completedRiemannZeta_one_sub s, div_self h]

/-- The regularized completed local-ratio symbol is the constant unit function. -/
theorem regularizedCompletedLocalRatio_eq_const_one :
    regularizedCompletedLocalRatio = fun _ => 1 := by
  funext s
  exact regularizedCompletedLocalRatio_eq_one s

/-- The regularized completed local-ratio symbol is entire. -/
theorem analyticAt_regularizedCompletedLocalRatio (s : ℂ) :
    AnalyticAt ℂ regularizedCompletedLocalRatio s := by
  rw [regularizedCompletedLocalRatio_eq_const_one]
  exact analyticAt_const

/-- The regularized completed local-ratio symbol has no differential defect. -/
theorem differentiable_regularizedCompletedLocalRatio :
    Differentiable ℂ regularizedCompletedLocalRatio := by
  rw [regularizedCompletedLocalRatio_eq_const_one]
  exact differentiable_const 1

/-- Multiplication by the regularized completed local-ratio symbol is the identity. -/
theorem regularizedCompletedLocalRatio_mul (s z : ℂ) :
    regularizedCompletedLocalRatio s * z = z := by
  rw [regularizedCompletedLocalRatio_eq_one, one_mul]

/-- A regularized completed local-ratio multiplier leaves every complex-valued observable unchanged. -/
theorem regularizedCompletedLocalRatio_mul_apply (f : ℂ → ℂ) (s : ℂ) :
    regularizedCompletedLocalRatio s * f s = f s :=
  regularizedCompletedLocalRatio_mul s (f s)

end GaloisForLFunctions.RHTower

end
