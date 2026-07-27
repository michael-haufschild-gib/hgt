import GaloisForLFunctions.HTGeometry.StretchedExponentialMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.RapidConvexCurvatureResonanceHypertranscendence

/-!
# Taylor magnitude of the explicit hypertranscendence witnesses

Both magnitude criteria — stretched exponential and log-Weibull — consume an eventual identity
between the norms of the Taylor coefficients and the prescribed profile.  The explicit phase families
satisfy it, but only inside the proofs of their own hypertranscendence, so the premise instance
cannot be cited.  Naming it makes both criteria applicable to the families by any downstream
argument.

* `norm_taylorPS_coeff_stretchedExponentialPhaseFunction` and its eventual and nonvanishing forms;
* `norm_taylorPS_coeff_logWeibullPhaseFunction`, `eventually_logMagnitude_logWeibullPhaseFunction` —
  the exact premises of the paper-form log-Weibull criterion.
-/

open Filter

namespace GaloisForLFunctions

noncomputable section

variable {B α γ : ℝ} {θ : ℕ → ℝ}

/-! ### The stretched-exponential family -/

theorem norm_taylorPS_coeff_stretchedExponentialPhaseFunction
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) (n : ℕ) :
    ‖PowerSeries.coeff n (taylorPS (stretchedExponentialPhaseFunction B α θ))‖ =
      Real.exp (-(B * stretchedExp α n)) := by
  rw [taylorPS_stretchedExponentialPhaseFunction hB hα0 hα1, norm_stretchedExponentialPhaseCoeff]

theorem eventually_norm_taylorPS_coeff_stretchedExponentialPhaseFunction
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ‖PowerSeries.coeff n (taylorPS (stretchedExponentialPhaseFunction B α θ))‖ =
        Real.exp (-(B * stretchedExp α n)) :=
  Eventually.of_forall (norm_taylorPS_coeff_stretchedExponentialPhaseFunction hB hα0 hα1 θ)

theorem taylorPS_coeff_ne_zero_stretchedExponentialPhaseFunction
    (hB : 0 < B) (hα0 : 0 < α) (hα1 : α < 1) (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (stretchedExponentialPhaseFunction B α θ)) ≠ 0 := by
  rw [taylorPS_stretchedExponentialPhaseFunction hB hα0 hα1]
  exact stretchedExponentialPhaseCoeff_ne_zero B α θ n

/-! ### The log-Weibull family -/

theorem norm_taylorPS_coeff_logWeibullPhaseFunction (hγ : 1 < γ) (θ : ℕ → ℝ) (n : ℕ) :
    ‖PowerSeries.coeff n (taylorPS (logWeibullPhaseFunction γ θ))‖ =
      Real.exp (-logWeibull γ n) := by
  rw [taylorPS_logWeibullPhaseFunction hγ, norm_logWeibullPhaseCoeff]

theorem taylorPS_coeff_ne_zero_logWeibullPhaseFunction (hγ : 1 < γ) (θ : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (taylorPS (logWeibullPhaseFunction γ θ)) ≠ 0 := by
  rw [taylorPS_logWeibullPhaseFunction hγ]
  exact logWeibullPhaseCoeff_ne_zero γ θ n

theorem eventually_taylorPS_coeff_ne_zero_logWeibullPhaseFunction (hγ : 1 < γ) (θ : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop, PowerSeries.coeff n (taylorPS (logWeibullPhaseFunction γ θ)) ≠ 0 :=
  Eventually.of_forall (taylorPS_coeff_ne_zero_logWeibullPhaseFunction hγ θ)

/-- The log-magnitude premise of the paper-form criterion, on the explicit family. -/
theorem eventually_logMagnitude_logWeibullPhaseFunction (hγ : 1 < γ) (θ : ℕ → ℝ) :
    ∀ᶠ n : ℕ in atTop,
      -Real.log ‖PowerSeries.coeff n (taylorPS (logWeibullPhaseFunction γ θ))‖ =
        logWeibull γ n := by
  refine Eventually.of_forall fun n => ?_
  rw [norm_taylorPS_coeff_logWeibullPhaseFunction hγ, Real.log_exp, neg_neg]

end

end GaloisForLFunctions
