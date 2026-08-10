import GaloisForLFunctions.RHTower.Sieve.GhsTotalErrorBound

/-!
# The mean value per unit, with the unconditional part isolated

Dividing the eventual bound by `N` and inserting `ghsTotalError_le` separates the three
unconditional terms from the Halász term:

```text
‖∑_{m ≤ N} f(m)‖/N
  ≤ ghsRecursionError N/(N log N)
      + (K+2)·(ghsErrConstTotal + 96 log log N)/log N
      + (K+2)·(1/2π)·dampedSize σ δ z N·(N+½)^σ·ghsBlockConstOf σ ghsShapeConst/(N log N) .
```

The first two tend to zero — `tendsto_ghsRecursionError_div` and
`tendsto_ghsTotalError_majorant` — so the mean value is `o(1)` exactly when the third does, which
is the multiplicative-distance condition and nothing else.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Filter Asymptotics Finset Topology

/-- The constant part of the total error. -/
def ghsErrConstTotal : ℝ := ghsErrorConst + ghsTopConst + 32 * Real.log 2

/-- **The mean value per unit.** -/
theorem eventually_norm_sum_Icc_div_le
    {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hcm : ∀ p q : ℕ, f (p * q) = f p * f q)
    (hf : ∀ i : ℕ, ‖f i‖ ≤ 1) :
    ∀ᶠ N : ℕ in atTop, ∀ (z : ℕ) (σ δ : ℝ), 1 < σ → 1 ≤ z → 0 ≤ δ →
      ((N : ℝ) + 1 / 2) ^ σ ≤ 3 * (N : ℝ) →
      (∀ y : ℝ, |y| ≤ ((ghsHeight N : ℕ) : ℝ) →
        δ ≤ Real.sqrt (mulDistSqPair f (charFn y) (Nat.primesLE z))) →
      ‖∑ m ∈ Finset.Icc 1 N, f m‖ / (N : ℝ)
        ≤ ghsRecursionError N / ((N : ℝ) * Real.log N)
          + ((ghsScaleCount N + 2 : ℕ) : ℝ)
              * (ghsErrConstTotal + 96 * Real.log (Real.log N)) / Real.log N
          + ((ghsScaleCount N + 2 : ℕ) : ℝ)
              * ((1 / (2 * Real.pi))
                  * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ
                      * ghsBlockConstOf σ ghsShapeConst)) / ((N : ℝ) * Real.log N) := by
  filter_upwards [eventually_norm_sum_Icc_le_ghs hf1 hmul hcm hf,
    eventually_ghsHeight_admissible, Filter.eventually_ge_atTop 65536] with N hbound hadm hN65
  obtain ⟨hN16, hlog, hexp, hPN, hNP, hroot⟩ := hadm
  intro z σ δ hσ hz hδ hx hunif
  have hb := hbound z σ δ hσ hz hδ hunif
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : (65536 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN65
    linarith
  have hL0 : (0 : ℝ) < Real.log N := by linarith
  set K : ℝ := ((ghsScaleCount N + 2 : ℕ) : ℝ) with hKdef
  set T : ℝ := ghsTotalError N (ghsHeight N) (ghsScaleCount N) σ with hTdef
  set H : ℝ := (1 / (2 * Real.pi))
      * (dampedSize σ δ z N * ((N : ℝ) + 1 / 2) ^ σ * ghsBlockConstOf σ ghsShapeConst)
    with hHdef
  set R : ℝ := ghsRecursionError N with hRdef
  -- divide the eventual bound by `N`
  have hstep : ‖∑ m ∈ Finset.Icc 1 N, f m‖ / (N : ℝ)
      ≤ ((R + K * (T + H)) / Real.log N) / (N : ℝ) :=
    div_le_div_of_nonneg_right hb hN0.le
  refine le_trans hstep ?_
  -- the identity
  have hid : ((R + K * (T + H)) / Real.log N) / (N : ℝ)
      = R / ((N : ℝ) * Real.log N) + K * T / ((N : ℝ) * Real.log N)
        + K * H / ((N : ℝ) * Real.log N) := by
    field_simp
    ring
  rw [hid]
  -- the middle term
  have hT := ghsTotalError_le hlog hN65 hroot hPN hx
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  have hmid : K * T / ((N : ℝ) * Real.log N)
      ≤ K * (ghsErrConstTotal + 96 * Real.log (Real.log N)) / Real.log N := by
    have hnum : K * T ≤ K * ((N : ℝ) * (ghsErrConstTotal + 96 * Real.log (Real.log N))) := by
      refine mul_le_mul_of_nonneg_left ?_ hK0
      rw [hTdef, ghsErrConstTotal]
      linarith [hT]
    have hdiv : K * T / ((N : ℝ) * Real.log N)
        ≤ K * ((N : ℝ) * (ghsErrConstTotal + 96 * Real.log (Real.log N)))
            / ((N : ℝ) * Real.log N) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    refine le_trans hdiv (le_of_eq ?_)
    field_simp
  linarith [hmid]

/-- **The unconditional part of the mean value vanishes.** -/
theorem tendsto_ghs_unconditional_part :
    Tendsto (fun N : ℕ => ghsRecursionError N / ((N : ℝ) * Real.log N)
        + ((ghsScaleCount N + 2 : ℕ) : ℝ)
            * (ghsErrConstTotal + 96 * Real.log (Real.log N)) / Real.log N)
      atTop (𝓝 0) := by
  have h1 := tendsto_ghsRecursionError_div
  have h2 := tendsto_ghsTotalError_majorant ghsErrConstTotal
  have := h1.add h2
  simpa using this

end RHTower.Sieve

end
