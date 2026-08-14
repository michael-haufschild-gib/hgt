import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleOverweight

/-!
# Complete middle-strip count for one selected-cell fibre

The adjacent-power and overweight analyses now cover the literal selected exponent partition
`beta < 1` / `1 <= beta`.  Both retain a fixed receiver reserve for the later finite-label sum.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Every nonempty fixed-label fibre in the middle strip satisfies one Route-T receiver, with
`d/2000` still unspent for the global coloring entropy. -/
theorem eventually_maynardWindowRelevantSelectedCell_middle_fibre_first_or_second :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60),
      ∀ (S : Finset ℕ), S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (mu * (1 - alpha) - maynardLongGlobalAmplitudeDeficit / 2000) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            maynardLongGlobalAmplitudeDeficit / 2000) := by
  filter_upwards [eventually_maynardWindowRelevantSelectedCell_middle_adjacent_count,
    eventually_maynardWindowRelevantSelectedCell_middle_overweight_count,
    eventually_gt_atTop (1 : ℝ)] with T hadj hover hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaHi hdelta
    label S hSne hS lam hgap hband hselection
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  have hmuEight : mu ≤ 8 := by linarith
  by_cases hbetaOne : beta < 1
  · have hraw := hadj hmuLo hmuEight hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaOne) S hSne hS lam hgap hband hselection
    rcases routeT_middle_shifted_adjacent_with_cost_first_or_second
        hmuLo hmuHi halphaLo halphaHi with hfirst | hsecond
    · left
      have hexp :
          2 * (1 - maynardMiddleReferenceAmplitude alpha) /
              maynardMiddleReferenceAmplitude alpha + d / 100000 ≤
            mu * (1 - alpha) - d / 2000 := by
        dsimp only [d] at hfirst ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      exact hraw.trans (mul_le_mul_of_nonneg_left hpow hHF0)
    · right
      have hexp :
          2 * (1 - maynardMiddleReferenceAmplitude alpha) /
              maynardMiddleReferenceAmplitude alpha + d / 100000 ≤
            1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000 := by
        dsimp only [d] at hsecond ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      exact hraw.trans (mul_le_mul_of_nonneg_left hpow hHF0)
  · have hbetaLo : 1 ≤ beta := le_of_not_gt hbetaOne
    have hraw := hover hmuLo hmuEight hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaLo) S hSne hS lam hgap hband hselection
    obtain ⟨r0, hr0⟩ := hSne
    rcases hselection r0 hr0 with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, hbetaUpper,
        _hlength, _hlarge, hbranch⟩
    have hbetaHi : beta ≤ 1 + mu / 60 := by
      have hbetaUpper' : beta < 1 + 2 * (mu / 120) := by
        simpa only [beta] using hbetaUpper
      linarith
    have halpha983 : alpha ≤ 983 / 1000 := by
      rcases hbranch with hsmall | hmoderate | hoverweight
      · have hsmall' : beta ≤ 5 / 12 := by
          simpa only [IsMaynardSelectedCellBranch, beta] using hsmall
        linarith
      · have hmoderate' : beta < 1 := by
          simpa only [IsMaynardSelectedCellBranch, beta] using hmoderate.2.1
        exact (hbetaOne hmoderate').elim
      · simpa only [IsMaynardSelectedCellBranch, beta] using hoverweight.2.1
    rcases routeT_overweight_literal_cap_with_reserve_first_or_second
        hmuLo hmuHi (by linarith : 3 / 4 ≤ alpha) halpha983 hbetaHi with
      hfirst | hsecond
    · left
      have hexp : beta * (2 - 2 * alpha) + d / 100000 ≤
          mu * (1 - alpha) - d / 2000 := by
        dsimp only [d] at hfirst ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      have hraw' : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (beta * (2 - 2 * alpha) + d / 100000) := by
        simpa only [beta, d] using hraw
      exact hraw'.trans (mul_le_mul_of_nonneg_left hpow hHF0)
    · right
      have hexp : beta * (2 - 2 * alpha) + d / 100000 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000 := by
        dsimp only [d] at hsecond ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      have hraw' : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (beta * (2 - 2 * alpha) + d / 100000) := by
        simpa only [beta, d] using hraw
      exact hraw'.trans (mul_le_mul_of_nonneg_left hpow hHF0)

end RHTower.Sieve
