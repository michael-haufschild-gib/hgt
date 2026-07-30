import GaloisForLFunctions.HTGeometry.UniversalObserverActionLaw

/-!
# The singular observer-time boundary

Weak interaction and long observation form a singular two-parameter corner.
Taking weak coupling first freezes every phase relation; taking long time
first dephases it.  Joint clock--detuning scaling resolves a nontrivial
boundary profile between those incompatible sequential limits.

This is the elementary local model of the observer-action atlas.  It
explains why a perturbative limit at fixed time and a recurrence limit at
fixed dynamics need not describe the same observable world.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Singular observer-time boundary law.** For every positive birth
order, fixed-time weak coupling freezes the character, fixed-coupling long
time dephases it, and every critical inverse-birth clock exposes the exact
sinc boundary profile. -/
theorem observerTime_singularBoundary
    {b : ℕ} (hb : 0 < b) :
    (∀ T : ℝ,
      Tendsto
        (fun g : ℝ => Real.sinc (T * g ^ b))
        (𝓝[>] 0) (𝓝 1)) ∧
    (∀ g : ℝ, 0 < g →
      Tendsto
        (fun T : ℝ => Real.sinc (T * g ^ b))
        atTop (𝓝 0)) ∧
    (∀ τ : ℝ, ∀ g : ℝ, 0 < g →
      Real.sinc ((τ / g ^ b) * g ^ b) =
        Real.sinc τ) := by
  constructor
  · intro T
    have hpow :
        Tendsto (fun g : ℝ => g ^ b)
          (𝓝[>] 0) (𝓝 0) :=
      (tendsto_pow_nhdsGT_zero hb).mono_right inf_le_left
    have harg :
        Tendsto (fun g : ℝ => T * g ^ b)
          (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hpow.const_mul T
    change
      Tendsto
        (Real.sinc ∘ fun g : ℝ => T * g ^ b)
        (𝓝[>] 0) (𝓝 1)
    simpa using
      Real.continuous_sinc.continuousAt.tendsto.comp harg
  constructor
  · intro g hg
    exact
      tendsto_real_sinc_atTop_zero.comp
        (tendsto_id.atTop_mul_const (pow_pos hg b))
  · intro τ g hg
    have hg0 : g ^ b ≠ 0 := pow_ne_zero b (ne_of_gt hg)
    rw [div_mul_cancel₀ τ hg0]

/-- The two sequential observer-time limits are incompatible. -/
theorem observerTime_sequentialLimits_do_not_commute
    {b : ℕ} (hb : 0 < b) :
    (∀ T : ℝ,
      Tendsto
        (fun g : ℝ => Real.sinc (T * g ^ b))
        (𝓝[>] 0) (𝓝 1)) ∧
    (∀ g : ℝ, 0 < g →
      Tendsto
        (fun T : ℝ => Real.sinc (T * g ^ b))
        atTop (𝓝 0)) ∧
    (0 : ℝ) ≠ 1 := by
  exact
    ⟨(observerTime_singularBoundary hb).1,
      (observerTime_singularBoundary hb).2.1,
      zero_ne_one⟩

/-- The critical joint path is genuinely different from the frozen
weak-coupling boundary. -/
theorem observerTime_criticalBoundary_ne_frozen :
    Real.sinc (1 : ℝ) ≠ 1 :=
  real_sinc_ne_one_of_ne_zero one_ne_zero

end

end GaloisForLFunctions.HTGeometry
