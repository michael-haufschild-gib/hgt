import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonBandReconstruction

/-!
# The background is determined, with no band hypothesis at all

The reconstruction of statement 376 recovers a background *up to its band compression*: what the
short-time experiment sees at cut-off `R` is `P_RWP_R`. Statement 216 says the compressions determine
the operator, so running the experiment at every cut-off leaves nothing behind:

**a moving background is determined exactly by short-time observations of its band models, at every
cut-off and from every instant** — with no band hypothesis on the background itself.

For a periodic background the instants may be restricted to one period, by the reduction of statement
374. The result is the sharpest form the inverse problem takes here: *a periodic background is
determined by one period of short-time experiments performed at every cut-off*.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section FullReconstruction

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **One period of experiments determines the band model of a periodic background.** -/
theorem eq_of_exact_observation_band_period (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) (R : ℝ)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {P T : ℝ} (hP0 : 0 < P) (hT0 : 0 < T)
    (hper₁ : ∀ r : ℝ, W₁ (r + P) = W₁ r) (hper₂ : ∀ r : ℝ, W₂ (r + P) = W₂ r)
    (hobs : ∀ s : ℝ, 0 ≤ s → s < P →
      ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
          = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) :
    kgBandOpT W₁ R = kgBandOpT W₂ R := by
  have hLip' : ∀ σ τ : ℝ,
      ‖(kgBandOpT W₁ R σ - kgBandOpT W₂ R σ) - (kgBandOpT W₁ R τ - kgBandOpT W₂ R τ)‖
        ≤ L * |σ - τ| := fun σ τ =>
    (norm_kgBandOp_sub_sub_le (W₁ σ) (W₂ σ) (W₁ τ) (W₂ τ) R).trans (hLip σ τ)
  have hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (kgBandOpT W₁ R r - kgBandOpT W₂ R r) (kgLowPassOp R v)
        = (kgBandOpT W₁ R r - kgBandOpT W₂ R r) v := fun r v =>
    kgBandOp_lowPass_dom (W₁ r) (W₂ r) R v
  have hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((kgBandOpT W₁ R r - kgBandOpT W₂ R r) v)
        = (kgBandOpT W₁ R r - kgBandOpT W₂ R r) v := fun r v =>
    kgBandOp_lowPass_ran (W₁ r) (W₂ r) R v
  exact eq_of_exact_observation_period hb0 (norm_kgBandOpT_le hb0 hW₁b R)
    (continuous_kgBandOpT_apply hW₁s R) (norm_kgBandOpT_le hb0 hW₂b R)
    (continuous_kgBandOpT_apply hW₂s R) hL0 hLip' hAdom hAran hP0 hT0
    (periodic_kgBandOpT (T := P) hper₁ R) (periodic_kgBandOpT (T := P) hper₂ R) hobs

/-- **Observing every band model determines the background exactly**, with no band hypothesis on the
background itself. -/
theorem eq_of_exact_observation_all_bands (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {T : ℝ} (hT0 : 0 < T)
    (hobs : ∀ (R s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) :
    W₁ = W₂ := by
  funext s
  refine eq_of_kgBandOp_eq fun R => ?_
  have h := eq_of_exact_observation_band hb0 hW₁b hW₁s hW₂b hW₂s R hL0 hLip hT0 (hobs R)
  exact congrFun h s

/-- **A periodic background is determined by one period of experiments at every cut-off.** -/
theorem eq_of_exact_observation_all_bands_period (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y)
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    {P T : ℝ} (hP0 : 0 < P) (hT0 : 0 < T)
    (hper₁ : ∀ r : ℝ, W₁ (r + P) = W₁ r) (hper₂ : ∀ r : ℝ, W₂ (r + P) = W₂ r)
    (hobs : ∀ R : ℝ, ∀ s : ℝ, 0 ≤ s → s < P →
      ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        kgFieldMildT (fun r : ℝ => kgBandOpT W₁ R (r + s)) g k t
          = kgFieldMildT (fun r : ℝ => kgBandOpT W₂ R (r + s)) g k t) :
    W₁ = W₂ := by
  funext s
  refine eq_of_kgBandOp_eq fun R => ?_
  have h := eq_of_exact_observation_band_period hb0 hW₁b hW₁s hW₂b hW₂s R hL0 hLip hP0 hT0
    hper₁ hper₂ (hobs R)
  exact congrFun h s

end FullReconstruction

end GaloisForLFunctions.HTGeometry
