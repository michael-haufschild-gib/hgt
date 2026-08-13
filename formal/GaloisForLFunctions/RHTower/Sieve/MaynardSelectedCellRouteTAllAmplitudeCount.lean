import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTCount
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalMontgomery
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalMiddleHuxley

/-!
# Complete Route-T selected-cell count across all amplitudes

The amplitude axis is covered by three literal mechanisms with no seam:

* exact two-term Montgomery cancellation through `19/25`;
* global-or-windowed Huxley, including the overweight spill, through `997/1000`;
* optimizer-scale Huxley plus endpoint exclusion above `997/1000`.

Each region preserves an explicit positive receiver reserve.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Region-adapted power reserve left after analytic and finite-color costs. -/
def routeTSelectedCellAmplitudeReserve (A T alpha : ℝ) : ℝ :=
  if alpha ≤ 19 / 25 then 1 / 200
  else if alpha ≤ 997 / 1000 then maynardLongGlobalAmplitudeDeficit / 4000
  else routeTEndpointGlobalDeficit A T / 200

theorem routeTSelectedCellAmplitudeReserve_pos
    {A T alpha : ℝ} (hT : 1 < T) :
    0 < routeTSelectedCellAmplitudeReserve A T alpha := by
  unfold routeTSelectedCellAmplitudeReserve
  split_ifs
  · norm_num
  · positivity [maynardLongGlobalAmplitudeDeficit_pos]
  · positivity [routeTEndpointGlobalDeficit_pos A (le_trans (by norm_num) hT.le)]

/-- **All-amplitude selected-cell capstone.**  Every literal window-relevant large-ordinate set
satisfies one of Route T's two Maynard count receivers with a strictly positive power reserve.
The canonical Möbius cutoff and complete selected-cell coloring are internal to the theorem. -/
theorem exists_eventually_routeT_selectedCell_all_amplitude_first_or_second :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {X K : ℕ} {mu N0 c alpha V delta : ℝ},
      1 ≤ X → (X : ℝ) ≤ T ^ mu →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 3 / 4 ≤ alpha →
      0 < V → 0 < delta → delta ≤ 2 * T →
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
        ((S.card : ℝ) ≤ maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha) ∨
          (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha)) := by
  obtain ⟨A, hhigh⟩ :=
    exists_eventually_routeT_selectedCell_high_amplitude_first_or_second
  refine ⟨A, ?_⟩
  filter_upwards [hhigh,
    eventually_exists_maynardWindowRelevantSelectedCell_coloring,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle,
    eventually_gt_atTop (1 : ℝ)] with T hhighT hcolorT hlowT hmiddleT hT
  intro X K mu N0 c alpha V delta hX hXscale hmuLo hmuHi hc halphaLo hV
    hdelta hdeltaHi S hS lam hband hgap hdiam haggregate hreserve
  by_cases hlow : alpha ≤ 19 / 25
  · have ht0 : 0 < mu / 120 := by linarith
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
      c alpha V N0 (by linarith) halphaLo hV S lam hband hmobius
        (haggregate L hL hXL) (hreserve L hL hXL)
    refine ⟨L, hL, hXL, hcut', Or.inr ?_⟩
    simpa only [routeTSelectedCellAmplitudeReserve, if_pos hlow] using
      hlowT hX hL hXscale hcut hmuLo hmuHi (by linarith) halphaLo hlow
        hdelta hdeltaHi S hS lam hgap hband color hcolor
  · have halphaMiddleLo : 19 / 25 ≤ alpha := le_of_not_ge hlow
    by_cases hmiddle : alpha ≤ 997 / 1000
    · have ht0 : 0 < mu / 120 := by linarith
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
        c alpha V N0 (by linarith) halphaLo hV S lam hband hmobius
          (haggregate L hL hXL) (hreserve L hL hXL)
      refine ⟨L, hL, hXL, hcut', ?_⟩
      simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_pos hmiddle] using
        hmiddleT hX hL hXscale hcut hmuLo hmuHi hc halphaMiddleLo hmiddle
          hdelta S hS lam hgap hband color hcolor
    · have halphaHigh : 997 / 1000 < alpha := lt_of_not_ge hmiddle
      obtain ⟨L, hL, hXL, hcut, hcount⟩ :=
        hhighT hX hXscale hmuLo hmuHi hc halphaHigh hV hdelta S hS lam
          hband hgap hdiam haggregate hreserve
      refine ⟨L, hL, hXL, hcut, ?_⟩
      simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_neg hmiddle] using hcount

end RHTower.Sieve
