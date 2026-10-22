import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPeriodicPotential

/-!
# The observations decide the clock's fate

Two threads have been carried to the same data: short-time band-limited observations, restarted at
every instant, determine the background (statement 378) and, when it is periodic, one period of them
suffices (379). The Floquet theory reads the clock's long-time fate off the background through the
monodromy.

Putting them together costs nothing, because the monodromy depends on the background and on nothing
else: observationally identical clocks have the **same Floquet spectrum**, hence the same spectral
radius and the same verdict in the trichotomy of statement 335.

So the data an experimenter can collect in a finite window decides not only what the background is but
whether the clock will keep time, decay, or break.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Fate

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- The monodromy depends on the background and on nothing else. -/
theorem kgMonodromy_congr (hW : W₁ = W₂) (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) (T : ℝ) :
    kgMonodromy W₁ b hb0 hW₁b hW₁s T = kgMonodromy W₂ b hb0 hW₂b hW₂s T := by
  subst hW
  rfl

/-- **Observationally identical clocks have the same Floquet spectrum.** -/
theorem spectrum_kgMonodromy_eq_of_exact_observation (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {T₀ : ℝ} (hT0 : 0 < T₀)
    (hobs : ∀ (R s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T₀ →
      kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) (T : ℝ) :
    spectrum ℂ (kgMonodromy W₁ b hb0 hW₁b hW₁s T)
      = spectrum ℂ (kgMonodromy W₂ b hb0 hW₂b hW₂s T) := by
  have hW := eq_of_exact_observation_all_bands hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hT0 hobs
  rw [kgMonodromy_congr hW hb0 hW₁b hW₁s hW₂b hW₂s T]

/-- **The verdict of the trichotomy is the same for observationally identical clocks.** -/
theorem spectralRadius_kgMonodromy_eq_of_exact_observation (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {T₀ : ℝ} (hT0 : 0 < T₀)
    (hobs : ∀ (R s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T₀ →
      kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) (T : ℝ) :
    spectralRadius ℂ (kgMonodromy W₁ b hb0 hW₁b hW₁s T)
      = spectralRadius ℂ (kgMonodromy W₂ b hb0 hW₂b hW₂s T) := by
  have hspec := spectrum_kgMonodromy_eq_of_exact_observation hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip
    hT0 hobs T
  show (⨆ k ∈ spectrum ℂ (kgMonodromy W₁ b hb0 hW₁b hW₁s T), (‖k‖₊ : ℝ≥0∞))
    = ⨆ k ∈ spectrum ℂ (kgMonodromy W₂ b hb0 hW₂b hW₂s T), (‖k‖₊ : ℝ≥0∞)
  rw [hspec]

/-- **One period of observations decides the fate of a periodic clock.** -/
theorem spectralRadius_kgMonodromy_eq_of_exact_observation_period (hb0 : 0 ≤ b)
    (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {P T₀ : ℝ} (hP0 : 0 < P) (hT0 : 0 < T₀)
    (hper₁ : ∀ r : ℝ, W₁ (r + P) = W₁ r) (hper₂ : ∀ r : ℝ, W₂ (r + P) = W₂ r)
    (hobs : ∀ R : ℝ, ∀ s : ℝ, 0 ≤ s → s < P →
      ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T₀ →
        kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
          = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) (T : ℝ) :
    spectralRadius ℂ (kgMonodromy W₁ b hb0 hW₁b hW₁s T)
      = spectralRadius ℂ (kgMonodromy W₂ b hb0 hW₂b hW₂s T) := by
  have hW := eq_of_exact_observation_all_bands_period hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip
    hP0 hT0 hper₁ hper₂ hobs
  rw [kgMonodromy_congr hW hb0 hW₁b hW₁s hW₂b hW₂s T]

end Fate

end GaloisForLFunctions.HTGeometry
