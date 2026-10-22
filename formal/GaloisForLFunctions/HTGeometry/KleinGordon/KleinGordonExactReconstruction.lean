import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonProbeEverywhere

/-!
# Exact observations determine a moving background exactly

The estimate of statement 368 has two error sources: the observational noise `η`, divided by the
square of the probing time, and the background's own drift during the probe, multiplied by it. With
exact observations the first term vanishes for every admissible probing time, and the second can be
made as small as one likes by probing briefly — the admissibility conditions `0 < x ≤ T` and
`x²((1+R²)/2 + be^{bT}) ≤ 1/8` are all satisfied by every sufficiently short probe.

So the bound collapses to zero and the two backgrounds agree, at the instant probed and therefore at
every instant:

**a band-limited moving background is determined exactly by exact observations of the short-time
field.**

This is the quantitative route to the injectivity of statements 152–154, and it carries a modulus:
the same argument with `η > 0` is the cube-root law of statement 369.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-! ## A probe short enough to make the drift term small -/

/-- **For every tolerance there is an admissible probing time whose drift term is below it.** -/
theorem exists_small_probe_time {b L R T ε : ℝ} (hb0 : 0 ≤ b) (hL0 : 0 ≤ L) (hT0 : 0 < T)
    (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ x ≤ T ∧ x ^ (2 : ℕ) * ((1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T)) ≤ 1 / 8
      ∧ 8 * (L * Real.exp (b * T)) * x ≤ ε := by
  set K : ℝ := (1 + R ^ (2 : ℕ)) / 2 + b * Real.exp (b * T) with hK
  have hK0 : 0 < K := by
    rw [hK]
    have h1 : (0 : ℝ) < (1 + R ^ (2 : ℕ)) / 2 := by positivity
    have h2 : (0 : ℝ) ≤ b * Real.exp (b * T) := by positivity
    linarith
  set M : ℝ := 8 * (L * Real.exp (b * T)) with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hs0 : 0 < Real.sqrt (1 / (8 * K)) := Real.sqrt_pos.mpr (by positivity)
  have he0 : 0 < ε / (M + 1) := by positivity
  set x : ℝ := min T (min (Real.sqrt (1 / (8 * K))) (ε / (M + 1))) with hx
  have hx0 : 0 < x := by
    rw [hx]
    exact lt_min hT0 (lt_min hs0 he0)
  refine ⟨x, hx0, min_le_left _ _, ?_, ?_⟩
  · have hxs : x ≤ Real.sqrt (1 / (8 * K)) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hsq : x ^ (2 : ℕ) ≤ 1 / (8 * K) := by
      have hh : x ^ (2 : ℕ) ≤ (Real.sqrt (1 / (8 * K))) ^ (2 : ℕ) := by gcongr
      rwa [Real.sq_sqrt (by positivity)] at hh
    have hstep : x ^ (2 : ℕ) * K ≤ (1 / (8 * K)) * K := mul_le_mul_of_nonneg_right hsq hK0.le
    calc x ^ (2 : ℕ) * K ≤ (1 / (8 * K)) * K := hstep
      _ = 1 / 8 := by field_simp
  · have hxe : x ≤ ε / (M + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
    have h1 : M * x ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left hxe hM0
    have h2 : M * (ε / (M + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < M + 1)]
      nlinarith [hε.le, hM0]
    linarith

/-! ## Exact reconstruction -/

section Exact

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W₁ W₂ : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b L : ℝ}

/-- **Exact observations determine a band-limited moving background exactly.** -/
theorem eq_of_exact_observation_everywhere (hb0 : 0 ≤ b) (hW₁b : ∀ r : ℝ, ‖W₁ r‖ ≤ b)
    (hW₁s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₁ r y)
    (hW₂b : ∀ r : ℝ, ‖W₂ r‖ ≤ b)
    (hW₂s : ∀ y : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => W₂ r y) {R : ℝ}
    (hL0 : 0 ≤ L)
    (hLip : ∀ σ τ : ℝ, ‖(W₁ σ - W₂ σ) - (W₁ τ - W₂ τ)‖ ≤ L * |σ - τ|)
    (hAdom : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      (W₁ r - W₂ r) (kgLowPassOp R v) = (W₁ r - W₂ r) v)
    (hAran : ∀ (r : ℝ) (v : Lp ℂ 2 (volume : Measure E)),
      kgLowPassOp R ((W₁ r - W₂ r) v) = (W₁ r - W₂ r) v)
    {T : ℝ} (hT0 : 0 < T)
    (hobs : ∀ (s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      kgFieldMildT (fun r : ℝ => W₁ (r + s)) g k t
        = kgFieldMildT (fun r : ℝ => W₂ (r + s)) g k t) :
    W₁ = W₂ := by
  have hobs' : ∀ (s : ℝ) (g k : Lp ℂ 2 (volume : Measure E)) (t : ℝ), |t| ≤ T →
      ‖kgFieldMildT (fun r : ℝ => W₁ (r + s)) g k t
        - kgFieldMildT (fun r : ℝ => W₂ (r + s)) g k t‖ ≤ 0 * (‖g‖ + ‖k‖) := by
    intro s g k t ht
    rw [hobs s g k t ht, sub_self, norm_zero, zero_mul]
  funext s
  have hle : ∀ ε : ℝ, 0 < ε → ‖W₁ s - W₂ s‖ ≤ ε := by
    intro ε hε
    obtain ⟨x, hx0, hxT, hxK, hdrift⟩ := exists_small_probe_time (R := R) hb0 hL0 hT0 hε
    have hmain := norm_sub_le_of_lowPassT_everywhere hb0 hW₁b hW₁s hW₂b hW₂s hL0 hLip hAdom hAran
      (η := 0) le_rfl hx0 hxT hxK hobs' s
    have hfirst : 8 * ((0 : ℝ) * (1 + b * T)) / x ^ (2 : ℕ) = 0 := by
      rw [zero_mul, mul_zero, zero_div]
    rw [hfirst, zero_add] at hmain
    exact hmain.trans hdrift
  have hzero : ‖W₁ s - W₂ s‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖W₁ s - W₂ s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have h := hle (‖W₁ s - W₂ s‖ / 2) (by linarith)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end Exact

end GaloisForLFunctions.HTGeometry
