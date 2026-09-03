import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIAbsorption

/-!
# Variable-upper sharp intervals in the explicit Case-II aggregate

The frequency-dependent endpoint selected by reverse Abel summation adds no color.  The paper's
physical Perron band also supplies the cubic-frequency premise required by the exhaustive receiver.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Variable sharp upper endpoints feed the explicit Case-II aggregate with no endpoint-color
cost.  The physical Perron band discharges the receiver's cubic-frequency premise internally. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHeathBrownCaseII_variableUpper
    (A : ℝ) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {L X cells : ℕ} {T0 t B sigma V Δ T : ℝ}
          {S : Finset ℕ} {upper : ℕ → ℕ} {tau : ℕ → ℝ},
        1 ≤ X → X < (L + 1) ^ 3 → 1 < T0 →
        ((2 ^ 6 : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ 8 ≤ (a : ℝ) → 1 ≤ L →
        (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ) →
        1 < sigma → 0 ≤ V → 1 ≤ Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r ∈ S, a ≤ upper r) →
        (∀ r ∈ S, upper r ≤ X) →
        (∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1)) →
        1 ≤ T → Δ / 2 ≤ T →
        (∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonSharpIntervalAmbientKernelMajorant C0 X sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        0 < Q →
        0 ≤ A →
        menonHeathBrownCaseIIAbsorptionEnvelope A L X a < Q →
        (∀ r ∈ S, B < ‖(2 * Real.pi : ℝ) •
          (∑ n ∈ Finset.Ioc a (upper r), vonMangoldtTwist (tau r) n)‖) →
        ∃ color : ℕ → MenonHeathBrownCaseIILabel L X cells,
          ∃ selectedY : ℕ → ℝ,
            (∀ r ∈ S,
              IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
                (selectedY r) (color r)) ∧
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
  obtain ⟨C0, hC0, hcolor⟩ :=
    exists_absolute_menonHeathBrownCaseIISelection_variableUpper_coloring
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [eventually_card_mul_sq_le_menonHeathBrownCaseII_explicit A] with a haggregate
  intro L X cells T0 t B sigma V Δ T S upper tau hX hXL hT0 hscale ha hL hcut
    hsigma hV hΔ hcells hgrid hupperLo hupperHi hbaseGap hT hΔT hbaseBand h2T
  dsimp only
  intro hQ hA habsorb hlarge
  let C : ℝ := menonSharpIntervalAmbientKernelMajorant C0 X sigma
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
      ((cells : ℝ) * Δ * C)
  obtain ⟨color, selectedY, hselection⟩ := hcolor L X a cells T0 t B sigma V Δ S
    upper tau hXL hT0 hscale ha hL hcut hsigma hV (lt_of_lt_of_le zero_lt_one hΔ)
    hcells hgrid hupperLo hupperHi (by simpa only [C, Q] using hQ) hlarge
  refine ⟨color, selectedY, hselection, ?_⟩
  have hfrequency : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      ∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
        |selectedY r + tau r| ≤ (a : ℝ) ^ (3 : ℕ) := by
    intro label _ r hr
    have hband := menonHeathBrownCaseIISelectedOrdinate_mem_band
      (lt_of_lt_of_le zero_lt_one hΔ) hgrid hselection hbaseBand label r
        (Finset.mem_filter.mp hr).1
    rw [menonHeathBrownCaseIISelectedOrdinate_eq_on_fibre hr] at hband
    have hnonneg : 0 ≤ selectedY r + tau r := by linarith [hT, hband.1]
    rw [abs_of_nonneg hnonneg]
    exact (by linarith [hband.2] : selectedY r + tau r ≤ 2 * T).trans h2T
  have habsorb' : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
            (Real.log (((2 ^ heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))) ^ (-A) *
              maynardLongPolylogEnvelope X) < Q := by
    intro label hnonempty
    obtain ⟨r, hr⟩ := hnonempty
    exact menonHeathBrownCaseII_absorption_of_envelope hA ha hsigma.le
      (isMenonHeathBrownCaseIISelection_on_colorFibre hselection label hr)
      (by simpa only [Q] using habsorb)
  exact haggregate hL hX hsigma.le hΔ hgrid hselection hbaseGap hT hΔT hbaseBand
    hfrequency habsorb' (by simpa only [Q] using hQ)

end

end RHTower.Sieve
