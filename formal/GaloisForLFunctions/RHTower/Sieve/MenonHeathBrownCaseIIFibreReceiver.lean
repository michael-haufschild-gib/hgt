import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIFrequencySplit
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownMediumMobiusExclusion

/-!
# Exhaustive receiver for every nonempty Menon Case-II color

The medium Mobius alternative is impossible after the exact logarithmic absorption.  A long
selection is already zeta/logarithm, and the remaining medium factor kinds are classified by the
literal three-constructor type.  The height split then sends every nonempty color to one of the
three exact Montgomery receivers.
-/

noncomputable section

namespace RHTower.Sieve

open Filter Finset

/-- After the medium-Mobius scalar saving is absorbed, every nonempty color satisfies a literal
zeta over-height, logarithm over-height, or fixed-order derivative receiver. -/
theorem eventually_menonHeathBrownCaseII_nonempty_fibre_receiver
    (A : ℝ) :
    ∀ᶠ q0 : ℕ in atTop,
      ∀ {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
        {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
        {selectedY tau : ℕ → ℝ},
      1 ≤ a → 1 ≤ L → 1 ≤ X → 1 ≤ sigma →
      0 < Δ → 2 * V = (cells : ℝ) * Δ →
      (∀ r ∈ S,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          (selectedY r) (color r)) →
      (∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1)) →
      0 < T → Δ / 2 ≤ T →
      (∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V) →
      ∀ (label : MenonHeathBrownCaseIILabel L X cells),
      heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor = q0 →
      (∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
        |selectedY r + tau r| ≤ (a : ℝ) ^ (3 : ℕ)) →
      (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
          (((groupedDyadicLower
            (heathBrownBoxFactorExponent
              label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
            (Real.log (((2 ^ q0 : ℕ) : ℝ))) ^ (-A) *
              maynardLongPolylogEnvelope X) < Q →
      0 < menonHeathBrownCaseIICoreThreshold L X Q →
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
        heathBrownBoxFactorKind 3 label.box.m label.factor = .log) ∧
      ((heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
          MenonHeathBrownCaseIIZetaOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
          MenonHeathBrownCaseIILogOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        MenonHeathBrownCaseIIDerivativeTwentySixBound
          L X cells S color sigma Δ Q T label) := by
  filter_upwards [eventually_menonHeathBrownCaseII_zetaLog_receiver,
    eventually_heathBrownCaseII_selectedFactor_ne_moebius A] with q0 hreceiver hmoebius
  intro L X a cells T0 t sigma V Δ Q T S color selectedY tau ha hL hX hsigma hΔ hgrid
    hselection hbaseGap hT hΔT hbaseBand label hexponent hfrequency habsorb
    hthreshold hnonempty
  obtain ⟨r0, hr0⟩ := hnonempty
  have hselected0 := isMenonHeathBrownCaseIISelection_on_colorFibre
    hselection label hr0
  have hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log := by
    cases hlong : label.isLong with
    | false =>
        have hfactorFrequency := abs_selectedFrequency_le_factor_pow_twentyFour_of_medium
          hselected0 hlong (hfrequency r0 hr0)
        have hfactorFrequency' :
            |selectedY r0 + tau r0| ≤ (((2 ^ q0 : ℕ) : ℝ)) ^ (24 : ℕ) := by
          simpa only [hexponent] using hfactorFrequency
        cases hfactorKind : heathBrownBoxFactorKind 3 label.box.m label.factor with
        | moebius =>
            have hqL : 2 ^ q0 ≤ L := by
              simpa only [hexponent] using
                label.box.moebius_factor_pow_le_cutoff hL label.factor hfactorKind
            have hne := hmoebius L X a cells T0 t sigma (tau r0) V Δ Q
              (selectedY r0) label hX hsigma hexponent hqL hfactorFrequency' habsorb hselected0
            exact (hne hfactorKind).elim
        | zeta => exact Or.inl rfl
        | log => exact Or.inr rfl
    | true =>
        have hbranch := hselected0.2.2.2.2.2
        simp only [hlong, ↓reduceIte] at hbranch
        exact hbranch.2.2
  have hfactorFrequency : ∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
      let lam := menonHeathBrownCaseIISelectedOrdinate
        S color selectedY tau V Δ label r
      |lam| ≤ (((2 ^ q0 : ℕ) : ℝ)) ^ (24 : ℕ) := by
    intro r hr
    have hselected := isMenonHeathBrownCaseIISelection_on_colorFibre
      hselection label hr
    have hfreq := abs_selectedFrequency_le_factor_pow_twentyFour
      ha hselected (hfrequency r hr)
    rw [menonHeathBrownCaseIISelectedOrdinate_eq_on_fibre hr]
    simpa only [add_comm, hexponent] using hfreq
  exact ⟨hkind, hreceiver hX (le_trans (by norm_num) hsigma) hΔ hgrid hselection hbaseGap hT
    hΔT hbaseBand label hexponent hkind hfactorFrequency hthreshold⟩

end RHTower.Sieve
