import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideLargeValueCount
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAbsorptionSchedule

/-!
# Paper-scale wide-smoothed Case-II count

The order-sixteen medium-Mobius estimate is absorbed at `(log a)^(-8)` exactly as in the sharp
chain.  Wide smoothing changes only the kernel and transition envelopes upstream.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Wide-smoothed harmonic-prime large values satisfy the explicit Case-II count whenever the
selected threshold dominates `(log a)^(-8)`. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_logPow :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X Y cells : ℕ} {T0 t H B sigma V Δ T : ℝ}
          {S : Finset ℕ} {w : ℕ → ℝ},
        1 ≤ X → a < Y → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        L ≤ X → (X : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) →
        0 < H → (Y : ℝ) + H ≤ (X : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r : ℕ, -(2 * Real.pi * w r) + 2 * Δ ≤ -(2 * Real.pi * w (r + 1))) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ r ∈ S, T + V ≤ -(2 * Real.pi * w r) ∧
          -(2 * Real.pi * w r) ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 X H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        (Real.log (a : ℝ)) ^ (-8 : ℝ) < Q →
        (∀ r ∈ S,
          (((B + menonWideIntervalTransitionEnvelope X H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y) (w r)‖) →
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
        (S.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcount⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide 16
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcount,
    eventually_menonHeathBrownCaseIIAbsorptionEnvelope_lt_logPow_of_polynomial_support]
      with a haCount haAbsorb
  intro L X Y cells T0 t H B sigma V Δ T S w hX haY hXL hT0 hscale ha hL hLX hXa
    hH hYX hsigma hB hV hΔ hcells hgrid hbaseGap hT hΔT hbaseBand h2T
  dsimp only
  intro hQ hlarge
  have haReal : (1 : ℝ) < (a : ℝ) := by
    calc
      (1 : ℝ) < 64 ^ (8 : ℕ) := by norm_num
      _ ≤ (a : ℝ) := ha
  have hlogPow : 0 < (Real.log (a : ℝ)) ^ (-8 : ℝ) :=
    Real.rpow_pos_of_pos (Real.log_pos haReal) _
  exact haCount hX haY hXL hT0 hscale ha hL hH hYX hsigma hB hV hΔ hcells hgrid
    hbaseGap hT hΔT hbaseBand h2T (hlogPow.trans hQ) (by norm_num)
      ((haAbsorb hL hX hLX hXa).trans hQ) hlarge

end

end RHTower.Sieve
