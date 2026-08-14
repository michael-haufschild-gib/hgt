import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTAllAmplitudeCount

/-!
# Fixed-cutoff Route-T selected-cell count

The Perron defect is built from one literal Möbius cutoff. Earlier selected-cell capstones chose
that cutoff internally and therefore required large-value and reserve hypotheses for every
admissible cutoff. This module exposes the dependency-closed fixed-cutoff theorem: once a
canonical cutoff has been chosen, the same cutoff flows through coloring, all amplitude regions,
and endpoint exclusion.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- **Fixed-cutoff all-amplitude capstone.** One canonical cutoff and its literal aggregate
suffice; no universal quantification over alternative cutoffs remains. -/
theorem exists_eventually_routeT_selectedCell_fixedCutoff_all_amplitude :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha V delta : ℝ},
      1 ≤ X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 3 / 4 ≤ alpha →
      0 < V → 0 < delta → delta ≤ 2 * T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - c) ≤ V) →
      ((S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (mu * (1 - alpha) -
            routeTSelectedCellAmplitudeReserve A T alpha) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            routeTSelectedCellAmplitudeReserve A T alpha)) := by
  obtain ⟨A, _C, _C', _delta0, _hC, _hC', _hdelta0, hboxExclude⟩ :=
    exists_eventually_routeT_endpoint_box_amplitude_exclusion
  refine ⟨A, ?_⟩
  filter_upwards [hboxExclude,
    eventually_exists_maynardWindowRelevantSelectedCell_coloring,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring A,
    eventually_gt_atTop (1 : ℝ)] with T hbox hcolorT hlowT hmiddleT hglobal hT
  intro L X K mu N0 c alpha V delta hX hL hXL hXscale hcut hmuLo hmuHi hc
    halphaLo hV hdelta hdeltaHi S hS lam hband hgap hdiam haggregate hreserve
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hcut i hi
  obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
    c alpha V N0 (by linarith) halphaLo hV S lam hband hmobius
      haggregate hreserve
  by_cases hlow : alpha ≤ 19 / 25
  · refine Or.inr ?_
    simpa only [routeTSelectedCellAmplitudeReserve, if_pos hlow] using
      hlowT hX hL hXscale hcut hmuLo hmuHi (by linarith) halphaLo hlow
        hdelta hdeltaHi S hS lam hgap hband color hcolor
  · have halphaMiddleLo : 19 / 25 ≤ alpha := le_of_not_ge hlow
    by_cases hmiddle : alpha ≤ 997 / 1000
    · simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_pos hmiddle] using
        hmiddleT hX hL hXscale hcut hmuLo hmuHi hc halphaMiddleLo hmiddle
          hdelta S hS lam hgap hband color hcolor
    · have halphaHigh : 997 / 1000 < alpha := lt_of_not_ge hmiddle
      by_cases halphaEndpoint : alpha ≤ 1 - routeTEndpointGlobalDeficit A T
      · simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_neg hmiddle] using
          hglobal hX hL hXscale hcut hmuLo hmuHi hc halphaHigh
            halphaEndpoint hdelta S hS lam hgap hdiam color hcolor
      · have hcut' : (L : ℝ) ≤ T ^ (mu / 60) := by
          convert hcut using 1 <;> ring_nf
        have hSempty : S = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hSne
          obtain ⟨r, hr⟩ := hSne
          rcases hcolor r hr with
            ⟨helig, _hrel, hcore, _hune, _husub, _hbetaLo, _hbetaHi,
              _hlength, _hlarge, _hbranch⟩
          have hbound := hbox X hX mu hmuLo hmuHi hXscale L hL hcut'
            (color r).1 helig c (lam r) alpha (by linarith)
              (hband r hr).1 (hband r hr).2 hcore
          exact halphaEndpoint hbound
        left
        rw [hSempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
          (Real.rpow_nonneg (by linarith) _)

end RHTower.Sieve
