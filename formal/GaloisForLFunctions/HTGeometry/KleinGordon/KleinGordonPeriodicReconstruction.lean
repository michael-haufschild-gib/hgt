import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonExactReconstruction

/-!
# One period of experiments determines a periodic background

Statement 371 reconstructs a moving background from observations restarted at *every* instant. When
the background is periodic that is more than one needs: restarting at `s` and at `s + nT` is the same
experiment, because the shifted backgrounds coincide.

Every instant is congruent modulo the period to one in `[0, T)`, by the integer part of `s/T`, so the
observation hypothesis need only be imposed there. A periodic band-limited background is therefore
determined by **one period** of short-time experiments — which is what an experimenter with a
periodically driven apparatus can actually perform.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Periodic

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {T : ℝ}

/-- A periodic background is periodic under every integer multiple of its period. -/
theorem periodic_shift_int (hper : ∀ r : ℝ, W (r + T) = W r) (n : ℤ) (r : ℝ) :
    W (r + (n : ℝ) * T) = W r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have harg : r + (((k : ℤ) + 1 : ℤ) : ℝ) * T = (r + (k : ℝ) * T) + T := by
        push_cast
        ring
      rw [harg, hper]
      push_cast at ih ⊢
      exact ih
  | pred k ih =>
      have h := hper (r + ((-(k : ℤ) - 1 : ℤ) : ℝ) * T)
      have harg : (r + ((-(k : ℤ) - 1 : ℤ) : ℝ) * T) + T = r + ((-(k : ℤ) : ℤ) : ℝ) * T := by
        push_cast
        ring
      rw [harg] at h
      rw [← h]
      push_cast at ih ⊢
      exact ih

/-- The representative of an instant in the first period. -/
theorem periodRep_nonneg (hT : 0 < T) (s : ℝ) : 0 ≤ s - (⌊s / T⌋ : ℝ) * T := by
  have hfl : ((⌊s / T⌋ : ℤ) : ℝ) ≤ s / T := Int.floor_le _
  have hmul := mul_le_mul_of_nonneg_right hfl hT.le
  rw [div_mul_cancel₀ _ hT.ne'] at hmul
  linarith

theorem periodRep_lt (hT : 0 < T) (s : ℝ) : s - (⌊s / T⌋ : ℝ) * T < T := by
  have hfl : s / T < ((⌊s / T⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have hmul := mul_lt_mul_of_pos_right hfl hT
  rw [div_mul_cancel₀ _ hT.ne'] at hmul
  nlinarith

/-- **Restarting at an instant is restarting at its representative in the first period.** -/
theorem shift_eq_periodRep (hper : ∀ r : ℝ, W (r + T) = W r) (s : ℝ) :
    (fun r : ℝ => W (r + s)) = fun r : ℝ => W (r + (s - (⌊s / T⌋ : ℝ) * T)) := by
  funext r
  have harg : r + s = (r + (s - (⌊s / T⌋ : ℝ) * T)) + (⌊s / T⌋ : ℝ) * T := by ring
  rw [harg]
  exact periodic_shift_int hper ⌊s / T⌋ _

end Periodic

/-! ## Reconstruction from one period -/

section Reconstruction

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **One period of experiments determines a periodic band-limited background.** -/
theorem eq_of_exact_observation_period (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    (hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (W₁ r - W₂ r) (kgLowPassOp R v) = (W₁ r - W₂ r) v)
    (hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((W₁ r - W₂ r) v) = (W₁ r - W₂ r) v)
    {P T : ℝ} (hP0 : 0 < P) (hT0 : 0 < T)
    (hper₁ : ∀ r : ℝ, W₁ (r + P) = W₁ r) (hper₂ : ∀ r : ℝ, W₂ (r + P) = W₂ r)
    (hobs : ∀ s : ℝ, 0 ≤ s → s < P →
      ∀ (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
        kgFieldMildT (fun r : ℝ => W₁ (r + s)) g k t
          = kgFieldMildT (fun r : ℝ => W₂ (r + s)) g k t) :
    W₁ = W₂ := by
  refine eq_of_exact_observation_everywhere hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hAdom hAran
    hT0 fun s g k t ht => ?_
  rw [shift_eq_periodRep hper₁ s, shift_eq_periodRep hper₂ s]
  exact hobs (s - (⌊s / P⌋ : ℝ) * P) (periodRep_nonneg hP0 s) (periodRep_lt hP0 s) g k t ht

end Reconstruction

end GaloisForLFunctions.HTGeometry
