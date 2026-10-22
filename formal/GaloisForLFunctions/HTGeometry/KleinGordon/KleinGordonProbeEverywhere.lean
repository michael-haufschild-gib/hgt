import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTwoWayClock

/-!
# Reconstructing a moving background at every instant

The conditional stability of statement 174 reads the background off the short-time field, and reads it
at the *initial* instant. A background that moves is not determined by one instant, and the evolution
family of statement 152 says what to do: restart the experiment at time `s`, which is the same as
solving the equation of the shifted background `W(· + s)` from time zero.

Every hypothesis of 174 then has to hold for the shifted pair, and each does: a uniform Lipschitz
bound on the difference gives the shifted Lipschitz bound with the same constant, the band conditions
are imposed at every instant, and the observation hypothesis is the natural one — the experimenter may
prepare data at any instant and watch for a time `T`. The conclusion transfers verbatim, so

`‖W₁(s) − W₂(s)‖ ≤ 8η(1+bT)/x² + 8Le^{bT}x`   for **every** `s`,

and at the balance point the cube-root law of statement 176 holds at every instant too: the whole
moving background is reconstructed, with a modulus of continuity that does not degrade with time.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Everywhere

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **Conditional stability at every instant.** Restarting the probe at time `s` reads off the
background there, with the constants of statement 174 and no loss. -/
theorem norm_sub_le_of_lowPassT_everywhere (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    (hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (W₁ r - W₂ r) (kgLowPassOp R v) = (W₁ r - W₂ r) v)
    (hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((W₁ r - W₂ r) v) = (W₁ r - W₂ r) v)
    {η T x : ℝ} (hη0 : 0 ≤ η) (hx0 : 0 < x) (hxT : x ≤ T)
    (hxK : x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) ≤ 1 / 8)
    (hobs : ∀ (s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMildT (fun r : ℝ => W₁ (r + s)) g k t
        - kgFieldMildT (fun r : ℝ => W₂ (r + s)) g k t‖ ≤ η * (‖g‖ + ‖k‖))
    (s : ℝ) :
    ‖W₁ s - W₂ s‖ ≤ 8 * (η * (1 + b * T)) / x ^ (2 : ℕ) + 8 * (L * Real.exp (b * T)) * x := by
  have hV₁b : ∀ r : ℝ, ‖(fun ρ : ℝ => W₁ (ρ + s)) r‖ ≤ b := fun r => hW₁b (r + s)
  have hV₁s : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun ρ : ℝ => W₁ (ρ + s)) r y := fun y =>
    (hW₁s y).comp (continuous_id.add continuous_const)
  have hV₂b : ∀ r : ℝ, ‖(fun ρ : ℝ => W₂ (ρ + s)) r‖ ≤ b := fun r => hW₂b (r + s)
  have hV₂s : ∀ y : Lp ℂ 2 (volume : Measure E),
      Continuous fun r : ℝ => (fun ρ : ℝ => W₂ (ρ + s)) r y := fun y =>
    (hW₂s y).comp (continuous_id.add continuous_const)
  have hLip' : ∀ σ : ℝ, ‖((fun ρ : ℝ => W₁ (ρ + s)) σ - (fun ρ : ℝ => W₂ (ρ + s)) σ)
      - ((fun ρ : ℝ => W₁ (ρ + s)) 0 - (fun ρ : ℝ => W₂ (ρ + s)) 0)‖ ≤ L * |σ| := by
    intro σ
    have h := hLip (σ + s) (0 + s)
    have harg : σ + s - (0 + s) = σ := by ring
    rw [harg] at h
    exact h
  have hAdom' : ∀ v : Lp ℂ 2 (volume : Measure E),
      ((fun ρ : ℝ => W₁ (ρ + s)) 0 - (fun ρ : ℝ => W₂ (ρ + s)) 0) (kgLowPassOp R v)
        = ((fun ρ : ℝ => W₁ (ρ + s)) 0 - (fun ρ : ℝ => W₂ (ρ + s)) 0) v := fun v =>
    hAdom (0 + s) v
  have hAran' : ∀ v : Lp ℂ 2 (volume : Measure E),
      kgLowPassOp R (((fun ρ : ℝ => W₁ (ρ + s)) 0 - (fun ρ : ℝ => W₂ (ρ + s)) 0) v)
        = ((fun ρ : ℝ => W₁ (ρ + s)) 0 - (fun ρ : ℝ => W₂ (ρ + s)) 0) v := fun v =>
    hAran (0 + s) v
  have hmain := norm_sub_zero_le_of_lowPassT hb0 hV₁b hV₁s hV₂b hV₂s hL0 hLip' hAdom' hAran'
    hη0 hx0 hxT hxK (hobs s)
  simpa using hmain

/-- **The cube-root law at every instant.** At the balance point the reconstruction error is three
halves of the drift term, uniformly in the instant probed. -/
theorem norm_sub_le_optimal_everywhere (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    (hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (W₁ r - W₂ r) (kgLowPassOp R v) = (W₁ r - W₂ r) v)
    (hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((W₁ r - W₂ r) v) = (W₁ r - W₂ r) v)
    {η T x : ℝ} (hη0 : 0 ≤ η) (hx0 : 0 < x) (hxT : x ≤ T)
    (hxK : x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) ≤ 1 / 8)
    (hbal : 8 * (L * Real.exp (b * T)) * x ^ (3 : ℕ) = 2 * (8 * (η * (1 + b * T))))
    (hobs : ∀ (s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMildT (fun r : ℝ => W₁ (r + s)) g k t
        - kgFieldMildT (fun r : ℝ => W₂ (r + s)) g k t‖ ≤ η * (‖g‖ + ‖k‖))
    (s : ℝ) :
    ‖W₁ s - W₂ s‖ ≤ 3 / 2 * (8 * (L * Real.exp (b * T)) * x) := by
  have hmain := norm_sub_le_of_lowPassT_everywhere hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hAdom hAran
    hη0 hx0 hxT hxK hobs s
  have hval := inv_sq_add_linear_at_balance (A := 8 * (η * (1 + b * T)))
    (B := 8 * (L * Real.exp (b * T))) hx0 hbal
  rw [← hval]
  exact hmain

end Everywhere

end GaloisForLFunctions.HTGeometry
