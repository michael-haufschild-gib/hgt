import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownVariableUpperAggregate

/-!
# Explicit Case-II count for large harmonic-prime values

Reverse reciprocal Abel and reverse logarithmic Abel select a sharp von Mangoldt prefix for each
large harmonic-prime value.  Its endpoint varies with the ordinate, but the ambient sharp-kernel
majorant lets all prefixes enter the same finite Case-II coloring without an endpoint cost.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Large values of one actual harmonic prime block satisfy the explicit Case-II cardinality
bound.  Both reverse Abel selections and their variable sharp endpoints are internal. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII
    (A : ℝ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X cells : ℕ} {T0 t B sigma V Δ T : ℝ}
          {S : Finset ℕ} {w : ℕ → ℝ},
        1 ≤ X → a < X → X < (L + 1) ^ (3 : ℕ) → 1 < T0 →
        ((2 ^ (6 : ℕ) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ (8 : ℕ) ≤ (a : ℝ) → 1 ≤ L →
        (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ) →
        1 < sigma → 0 ≤ B → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r : ℕ, -(2 * Real.pi * w r) + 2 * Δ ≤ -(2 * Real.pi * w (r + 1))) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ r ∈ S, T + V ≤ -(2 * Real.pi * w r) ∧
          -(2 * Real.pi * w r) ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonSharpIntervalAmbientKernelMajorant C0 X sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        0 < Q →
        0 ≤ A →
        menonHeathBrownCaseIIAbsorptionEnvelope A L X a < Q →
        (∀ r ∈ S,
          ((B + primePowerDefectIoc a X) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a X) (w r)‖) →
        let D : ℕ :=
          3 * (Nat.log 2 X + 1) ^ (3 : ℕ) * (Nat.log 2 L + 1) ^ (3 : ℕ)
        let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * W ^ (2 : ℕ) *
              (1 + Real.log (W * (X : ℝ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (S.card : ℝ) * Vexp ^ (2 : ℕ) ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, haggregate⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHeathBrownCaseII_variableUpper A
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [haggregate] with a haAggregate
  intro L X cells T0 t B sigma V Δ T S w hX haX hXL hT0 hscale ha hL hcut
    hsigma hB hV hΔ hcells hgrid hbaseGap hT hΔT hbaseBand h2T
  dsimp only
  intro hQ hA habsorb hlarge
  have haOne : 1 ≤ a := by
    have haReal : (1 : ℝ) ≤ (a : ℝ) := (by norm_num : (1 : ℝ) ≤ 64 ^ (8 : ℕ)).trans ha
    exact_mod_cast haReal
  have hprefix : ∀ r : ℕ, r ∈ S →
      ∃ m ∈ Finset.Ioc a X,
        B < ‖∑ n ∈ Finset.Ioc a m,
          vonMangoldtTwist (-(2 * Real.pi * w r)) n‖ := by
    intro r hr
    exact exists_norm_vonMangoldtTwist_Ioc_gt_of_harmonicPrimeBlockPoly_gt
      haOne haX (fun p => mem_primesRange) (w r) hB (hlarge r hr)
  choose selectedUpper hupper hupperLarge using hprefix
  let upper : ℕ → ℕ := fun r => if hr : r ∈ S then selectedUpper r hr else a
  let tau : ℕ → ℝ := fun r => -(2 * Real.pi * w r)
  have hupperLo : ∀ r ∈ S, a ≤ upper r := by
    intro r hr
    simpa only [upper, dif_pos hr] using (Finset.mem_Ioc.mp (hupper r hr)).1.le
  have hupperHi : ∀ r ∈ S, upper r ≤ X := by
    intro r hr
    simpa only [upper, dif_pos hr] using (Finset.mem_Ioc.mp (hupper r hr)).2
  have hsharp : ∀ r ∈ S, B < ‖(2 * Real.pi : ℝ) •
      (∑ n ∈ Finset.Ioc a (upper r), vonMangoldtTwist (tau r) n)‖ := by
    intro r hr
    have hraw := hupperLarge r hr
    rw [show upper r = selectedUpper r hr by simp only [upper, dif_pos hr]]
    rw [norm_smul]
    have hscalar : (1 : ℝ) ≤ ‖(2 * Real.pi : ℝ)‖ := by
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      nlinarith [Real.pi_gt_three]
    exact hraw.trans_le (le_mul_of_one_le_left (norm_nonneg _) hscalar)
  obtain ⟨_, _, _, hbound⟩ :=
    haAggregate hX hXL hT0 hscale ha hL hcut hsigma hV hΔ hcells hgrid
      hupperLo hupperHi (by simpa only [tau] using hbaseGap) hT hΔT
      (by simpa only [tau] using hbaseBand) h2T (by simpa using hQ) hA habsorb hsharp
  exact hbound

end

end RHTower.Sieve
