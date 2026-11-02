import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileIsPositiveAtLogLogOverlapOnPolynomialSpans

/-!
# Nearly log-log overlap on polynomial conductor spans

The linear-moment theorem gives a full fixed log-log interval. Restricting its
clock retains the same universal exponential rate and profile constants.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory

/-- Restriction of the fixed log-log positivity interval, with constants independent
of the polynomial conductor exponent. -/
theorem exists_universal_nearly_loglog_polynomial_span_coercivity :
    ∃ B : ℝ, 0 < B ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ θ : ℝ, 0 < θ → θ < 1 / 1080 →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
        c ≤ b * Real.log (Real.log (N : ℝ)) /
          Real.sqrt (1 + Real.log (Real.log (Real.log (N : ℝ)))) →
      ∀ x ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N,
        a * Real.exp (-B * c) * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨B, hB, hall⟩ := exists_universal_loglog_polynomial_span_coercivity
  refine ⟨B, hB, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a, b, ha, hb, hspan⟩ := hall φ hφ hsupp hM
  refine ⟨a, b, ha, hb, ?_⟩
  intro θ hθ hθlt
  have htlim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hspan θ hθ hθlt, htlim.eventually_ge_atTop 1] with N hN ht1
  intro c hc hclock x hx
  have ht0 : 0 ≤ Real.log (Real.log (N : ℝ)) := zero_le_one.trans ht1
  have hroot : 1 ≤ Real.sqrt (1 + Real.log (Real.log (Real.log (N : ℝ)))) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt
      (show (1 : ℝ) ≤ 1 + Real.log (Real.log (Real.log (N : ℝ))) by
        linarith only [Real.log_nonneg ht1])
  exact hN c hc (hclock.trans (div_le_self (mul_nonneg hb.le ht0) hroot)) x hx

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
