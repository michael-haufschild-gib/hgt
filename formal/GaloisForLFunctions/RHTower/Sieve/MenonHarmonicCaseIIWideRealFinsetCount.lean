import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideLogPowCount
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRealFinsetHalaszMontgomery

/-!
# Wide-smoothed Case-II count on literal finite frequency sets
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Large harmonic-prime values on a literal finite separated set satisfy the explicit
wide-smoothed Case-II cardinality bound. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_realFinset :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ}
          {E : Finset ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ x ∈ E, ∀ y ∈ E, x ≠ y → 2 * Δ ≤ |x - y|) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ x ∈ E, T + V ≤ x ∧ x ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-8 : ℝ) < Q →
        (∀ x ∈ E,
          (((B + menonWideIntervalTransitionEnvelope X H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-x / (2 * Real.pi))‖) →
        let D : ℕ :=
          3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
        let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * W ^ 2 *
              (1 + Real.log (W * (X : ℝ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (E.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcount⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_logPow
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount] with a haCount
  intro L X Y cells T0 t H B sigma V Δ T E hX haY hXL hT0 hscale ha hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hsep hT hΔT hband h2T
  dsimp only
  intro hQ hlarge
  have htwoDelta : 0 < 2 * Δ := by positivity
  let P := matomakiTeravainenFiniteSeparatedOrdinates E (2 * Δ) htwoDelta hsep
  let tau : ℕ → ℝ := RHTower.cglFiniteSeparatedOrdinatesTimeline P
  let w : ℕ → ℝ := fun r => -(tau r) / (2 * Real.pi)
  have hphase : ∀ r : ℕ, -(2 * Real.pi * w r) = tau r := by
    intro r
    dsimp only [w]
    field_simp [Real.pi_ne_zero]
  have hgap : ∀ r : ℕ, -(2 * Real.pi * w r) + 2 * Δ ≤
      -(2 * Real.pi * w (r + 1)) := by
    intro r
    rw [hphase r, hphase (r + 1)]
    exact RHTower.cglFiniteSeparatedOrdinatesTimeline_step P r
  have hactiveBand : ∀ r ∈ Finset.range E.card,
      T + V ≤ -(2 * Real.pi * w r) ∧ -(2 * Real.pi * w r) ≤ 2 * T - V := by
    intro r hr
    rw [hphase r]
    exact hband _ (matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      E (2 * Δ) htwoDelta hsep (Finset.mem_range.mp hr))
  have hactiveLarge : ∀ r ∈ Finset.range E.card,
      (((B + menonWideIntervalTransitionEnvelope X H) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) (w r)‖ := by
    intro r hr
    have hmem := matomakiTeravainenFiniteSeparatedOrdinates_timeline_mem
      E (2 * Δ) htwoDelta hsep (Finset.mem_range.mp hr)
    simpa only [w, tau] using hlarge _ hmem
  simpa only [Finset.card_range] using
    haCount hX haY hXL hT0 hscale ha hL hLX hXa hH hYX hsigma hB hV hΔ hcells hgrid
      hgap hT hΔT hactiveBand h2T hQ hactiveLarge

end

end RHTower.Sieve
