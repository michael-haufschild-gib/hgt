import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalCount
import GaloisForLFunctions.RHTower.Sieve.RouteTEndpointAmplitudeExclusion

/-!
# Complete Route-T high-amplitude selected-cell count

The canonical degree-`60` cutoff makes every Möbius atom sub-height while preserving the exact
Heath--Brown identity range.  Literal window-relevant selection then feeds the global optimizer
count below the moving endpoint.  Above that endpoint, the selected box itself contradicts the
already-proved all-kind endpoint amplitude exclusion, so the ordinate set is empty.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- **Canonical high-amplitude Route-T count.**  No coloring, box, or endpoint premise remains in
the conclusion; the only inputs are the literal window aggregate and its exact selection reserve. -/
theorem exists_eventually_routeT_selectedCell_high_amplitude_first_or_second :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {X K : ℕ} {mu N0 c alpha V delta : ℝ},
      1 ≤ X → (X : ℝ) ≤ T ^ mu →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 997 / 1000 < alpha →
      0 < V → 0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ r ∈ S,
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxWindowRelevant N0 X 60 box →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤ V) →
      ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
        (L : ℝ) ≤ T ^ (mu / 60) ∧
        ((S.card : ℝ) ≤
            maynardHarmonicFactor K delta *
              T ^ (mu * (1 - alpha) - routeTEndpointGlobalDeficit A T / 200) ∨
          (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTEndpointGlobalDeficit A T / 200)) := by
  obtain ⟨A, _C, _C', _delta0, _hC, _hC', _hdelta0, hboxExclude⟩ :=
    exists_eventually_routeT_endpoint_box_amplitude_exclusion
  refine ⟨A, ?_⟩
  filter_upwards [hboxExclude,
    eventually_exists_maynardWindowRelevantSelectedCell_coloring,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring A,
    eventually_gt_atTop (1 : ℝ)] with T hbox hcolorT hglobal hT
  intro X K mu N0 c alpha V delta hX hXscale hmuLo hmuHi hc halphaLo hV
    hdelta S hS lam hband hgap hdiam haggregate hreserve
  have ht0 : 0 < mu / 120 := by linarith
  have hX120 : (X : ℝ) ≤ T ^ (120 * (mu / 120)) := by
    convert hXscale using 1 <;> ring
  obtain ⟨L, hL, hXL, hcut⟩ :=
    exists_maynardMoebiusCutoff_sixty hT ht0.le hX120
  have hcut' : (L : ℝ) ≤ T ^ (mu / 60) := by
    convert hcut using 1 <;> ring
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hcut i hi
  obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
    c alpha V N0 (by linarith) (by linarith) hV S lam hband hmobius
      (haggregate L hL hXL) (hreserve L hL hXL)
  refine ⟨L, hL, hXL, hcut', ?_⟩
  by_cases halphaEndpoint : alpha ≤ 1 - routeTEndpointGlobalDeficit A T
  · exact hglobal hX hL hXscale hcut hmuLo hmuHi hc halphaLo
      halphaEndpoint hdelta S hS lam hgap hdiam color hcolor
  · have hSempty : S = ∅ := by
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
