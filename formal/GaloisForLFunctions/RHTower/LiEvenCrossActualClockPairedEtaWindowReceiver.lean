import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPairedEtaApproximation
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockNegativeResponse

/-!
# A growing finite eta clock-window sign is sufficient for RH

The hypothesis retains the literal completed finite response on one valid central circle:
every sufficiently long prefix is nonnegative throughout a logarithmically growing positive
clock window. At each fixed clock, the exact source error tends to zero and that clock eventually
lies in the window. Nonnegativity therefore passes to the literal complete response.

The same actual approximation radius gives the conditional RH consequence through the complete
negative-response receiver. The window coefficient needs only be positive; this proof makes no
uniform approximation claim on windows with coefficient at least `r / 4`. No window sign or
converse RH implication is proved here.
-/

open Complex Filter Topology

namespace RHTower

/-- Literal finite-prefix nonnegativity on some logarithmically growing positive-clock window. -/
def liClockPairedEtaFiniteClockWindowNonneg (r : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ t : ℝ,
    0 < t → t ≤ c * Real.log (2 * (N : ℝ) + 1) →
      0 ≤ (liClockPairedEtaFiniteClockResponse N r (t : ℂ)).re

/-- One actual approximation radius passes a growing finite-prefix sign to every nonnegative
literal clock. The window coefficient needs only be positive. -/
theorem exists_liEvenCrossActualClockPairedEtaWindow_nonneg_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      liClockPairedEtaFiniteClockWindowNonneg r →
        ∀ t : ℝ, 0 ≤ t → 0 ≤ liEvenCrossActualClockResponse t := by
  obtain ⟨r₀, hr₀, hr₀small, herror⟩ :=
    exists_liClockPairedEtaFiniteClockResponse_error_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr₀ hsign t ht => ?_⟩
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t
    simp [liEvenCrossActualClockResponse]
  · obtain ⟨c, hc, hsign⟩ := hsign
    have hodd : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    have hwindow : Tendsto (fun N : ℕ => c * Real.log (2 * (N : ℝ) + 1))
        atTop atTop :=
      (Real.tendsto_log_atTop.comp hodd).const_mul_atTop hc
    have hprefix : ∀ᶠ N : ℕ in atTop,
        0 ≤ (liClockPairedEtaFiniteClockResponse N r (t : ℂ)).re := by
      filter_upwards [hsign, hwindow.eventually_ge_atTop t] with N hN hclock
      exact hN t ht hclock
    have hbound : ∀ᶠ N : ℕ in atTop,
        ‖liClockPairedEtaFiniteClockResponse N r (t : ℂ) -
          (liEvenCrossActualClockResponse t : ℂ)‖ ≤
        liClockPairedEtaSourceErrorEnvelope N * Real.sinh (‖(t : ℂ)‖ / r) := by
      filter_upwards [liClockPairedEta_eventually_valueTail_le_one_sixteenth]
        with N hsmall
      simpa only [liEvenCrossActualComplexClockResponse_ofReal] using
        herror r hr hrr₀ N hsmall (t : ℂ)
    have henv : Tendsto (fun N : ℕ => liClockPairedEtaSourceErrorEnvelope N *
        Real.sinh (‖(t : ℂ)‖ / r)) atTop (𝓝 0) := by
      simpa only [zero_mul] using
        liClockPairedEtaSourceErrorEnvelope_tendsto_zero.mul_const
          (Real.sinh (‖(t : ℂ)‖ / r))
    have hcomplex : Tendsto (fun N : ℕ => liClockPairedEtaFiniteClockResponse N r (t : ℂ))
        atTop (𝓝 (liEvenCrossActualClockResponse t : ℂ)) := by
      apply tendsto_iff_dist_tendsto_zero.2
      simpa only [dist_eq_norm] using
        squeeze_zero' (Eventually.of_forall fun N => norm_nonneg
          (liClockPairedEtaFiniteClockResponse N r (t : ℂ) -
            (liEvenCrossActualClockResponse t : ℂ))) hbound henv
    have hreal : Tendsto (fun N : ℕ => (liClockPairedEtaFiniteClockResponse N r (t : ℂ)).re)
        atTop (𝓝 (liEvenCrossActualClockResponse t)) := by
      simpa only [Function.comp_def, Complex.ofReal_re] using
        (Complex.continuous_re.tendsto (liEvenCrossActualClockResponse t : ℂ)).comp hcomplex
    exact ge_of_tendsto hreal hprefix

/-- The same actual approximation radius makes the explicit finite-prefix window sign a
sufficient condition for literal clock nonnegativity and the Riemann hypothesis. -/
theorem exists_liEvenCrossActualClockPairedEtaWindow_rh_radius :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 128 ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      liClockPairedEtaFiniteClockWindowNonneg r →
        (∀ t : ℝ, 0 ≤ t → 0 ≤ liEvenCrossActualClockResponse t) ∧
          RiemannHypothesis := by
  obtain ⟨r₀, hr₀, hr₀small, hnonneg⟩ :=
    exists_liEvenCrossActualClockPairedEtaWindow_nonneg_radius
  refine ⟨r₀, hr₀, hr₀small, fun r hr hrr₀ hsign => ?_⟩
  have hclock := hnonneg r hr hrr₀ hsign
  refine ⟨hclock, riemannHypothesis_of_liEvenCrossActualClock_eventually_nonneg ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact hclock t ht

end RHTower
