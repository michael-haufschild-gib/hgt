import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Critical completion of nonzero period incidence

The analytic divided-difference normalization uses the unique scale
`lambda / (1 + norm lambda)`.  Rather than closing its nonclosed image in the raw sup norm, the
critical trace remembers the decoded bounded coordinates in a complete `ell-infinity` space and
realizes them by the weighted period incidence.  Every nonzero coordinate is reconstructed
explicitly, and the phase of the weight is unitary.  The unscaled period remains a separate
integral comparison datum.
-/

open scoped ENNReal

namespace GaloisForLFunctions

noncomputable section

universe u

def criticalPeriodWeight (lambda : ℂ) : ℂ :=
  lambda / ((1 + ‖lambda‖ : ℝ) : ℂ)

theorem criticalPeriodWeight_ne_zero {lambda : ℂ} (hlambda : lambda ≠ 0) :
    criticalPeriodWeight lambda ≠ 0 := by
  apply div_ne_zero hlambda
  exact_mod_cast (by positivity : (1 + ‖lambda‖ : ℝ) ≠ 0)

abbrev CriticalPeriodTrace (L : Type u) : Type u :=
  lp (fun _ : L ↦ ℂ) ∞

theorem criticalPeriodTrace_completeSpace (L : Type u) :
    CompleteSpace (CriticalPeriodTrace L) := inferInstance

def criticalPeriodTraceRealization
    {L : Type u} (period : L → ℂ) (x : CriticalPeriodTrace L) : L → ℂ :=
  fun lambda ↦ criticalPeriodWeight (period lambda) * x lambda

theorem criticalPeriodTraceRealization_injective
    {L : Type u} (period : L → ℂ) (hperiod : ∀ lambda, period lambda ≠ 0) :
    Function.Injective (criticalPeriodTraceRealization period) := by
  intro x y hxy
  apply lp.ext
  funext lambda
  have h := congrFun hxy lambda
  exact mul_left_cancel₀ (criticalPeriodWeight_ne_zero (hperiod lambda)) h

theorem criticalPeriodTrace_reconstruction
    {L : Type u} (period : L → ℂ) (hperiod : ∀ lambda, period lambda ≠ 0)
    (x : CriticalPeriodTrace L) (lambda : L) :
    (criticalPeriodWeight (period lambda))⁻¹ *
        criticalPeriodTraceRealization period x lambda = x lambda := by
  rw [criticalPeriodTraceRealization, ← mul_assoc, inv_mul_cancel₀
    (criticalPeriodWeight_ne_zero (hperiod lambda)), one_mul]

def criticalPeriodPhase (lambda : ℂ) : ℂ :=
  criticalPeriodWeight lambda / ‖criticalPeriodWeight lambda‖

theorem norm_criticalPeriodPhase {lambda : ℂ} (hlambda : lambda ≠ 0) :
    ‖criticalPeriodPhase lambda‖ = 1 := by
  rw [criticalPeriodPhase, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (criticalPeriodWeight_ne_zero hlambda))

end

end GaloisForLFunctions
