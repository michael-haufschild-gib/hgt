import GaloisForLFunctions.HTGeometry.SymmetricTimeAverageCharacterLaw

/-!
# Symmetric time-average wall crossing

The scalar sinc reporter is the exact normalized symmetric time average of a
unitary phase mode. Hence every real mode with an exact positive-ray birth
profile has the same unresolved, crossover, and dephased regimes as its sinc
profile.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Actual symmetric-window wall crossing.** A real phase mode born at
order `b` is unresolved on every shorter inverse-power window, has the
universal sinc profile on its birth window, and is averaged away on every
longer inverse-power window. -/
theorem symmetricPhaseAverage_wallCrossing
    {detuning : ℝ → ℝ} {b : ℕ} {c τ : ℝ}
    (hprofile : HasPositiveBirthProfile detuning b c)
    (hτ : 0 < τ) :
    (∀ r < b,
      Tendsto
        (fun g => symmetricPhaseAverage (τ / g ^ r) (detuning g))
        (𝓝[>] 0) (𝓝 1)) ∧
    Tendsto
      (fun g => symmetricPhaseAverage (τ / g ^ b) (detuning g))
      (𝓝[>] 0) (𝓝 (Real.sinc (τ * c))) ∧
    (∀ r, b < r →
      Tendsto
        (fun g => symmetricPhaseAverage (τ / g ^ r) (detuning g))
        (𝓝[>] 0) (𝓝 0)) := by
  have hwall := spectralCharacterReporter_wallCrossing hprofile hτ
  constructor
  · intro r hr
    have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hwall.1 r hr)
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    have hg0 : g ≠ 0 := ne_of_gt hg
    rw [symmetricPhaseAverage_eq_sinc]
    · apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
      ring
    · exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero r hg0)
  constructor
  · have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hwall.2.1
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    have hg0 : g ≠ 0 := ne_of_gt hg
    rw [symmetricPhaseAverage_eq_sinc]
    · apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
      ring
    · exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero b hg0)
  · intro r hr
    have hc :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (hwall.2.2 r hr)
    apply hc.congr'
    filter_upwards [self_mem_nhdsWithin] with g hg
    change 0 < g at hg
    have hg0 : g ≠ 0 := ne_of_gt hg
    rw [symmetricPhaseAverage_eq_sinc]
    · apply congrArg (fun x : ℝ => (Real.sinc x : ℂ))
      ring
    · exact div_ne_zero (ne_of_gt hτ) (pow_ne_zero r hg0)

end

end GaloisForLFunctions.HTGeometry
