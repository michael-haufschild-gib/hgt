import GaloisForLFunctions.RHTower.Sieve.MaynardTransitionStripPhysicalCount
import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryAmplitude

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Every exact physical amplitude band above the canonical trivial-count base is receiver-ready:
transition Montgomery handles the new lower strip and the existing all-amplitude capstone handles
the complementary upper strip. -/
theorem eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative_above_trivialBoundary
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ (60 : ℕ) →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V →
      (K : ℝ) ≤ T →
      ∀ (U : Finset ℕ), U ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ U, T ≤ c m ∧ c m ≤ 2 * T) →
      let a : ℝ → ℂ := fun y =>
        heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
      let B := maynardUnitCellAmplitudeBand U a c V
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ mu)
            (routeTAdaptiveCellAmplitude L X 60 N0 V) ∧
        IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ mu)
            (routeTAdaptiveCellAmplitude L X 60 N0 V) := by
  filter_upwards [
    eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative_transition q,
    eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative q
  ] with T htransition hupper
  intro L X K mu N0 V hX hL hXL hXscale hLscale hmuLo hmuHi hD hV
    hthreshold hK U hU c hc hordinate
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate
      L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
  let B : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N0 V
  have hB : B ⊆ Finset.range (2 * K) :=
    (maynardUnitCellAmplitudeBand_subset U a c V).trans hU
  have hband : ∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T := by
    intro m hm
    exact hordinate m (maynardUnitCellAmplitudeBand_subset U a c V hm)
  have haggregate : ∀ m ∈ B,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (c m : ℝ) * Complex.I)‖ := by
    intro m hm
    exact maynardUnitCellAmplitudeBand_lower
      (U := U) (A := a) (c := c) hm
  have hreserve : ∀ box : HeathBrownBoxChoice L X 60,
      IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
      IsHeathBrownBoxWindowRelevant N0 X 60 box →
      heathBrownEligibleBoxCost L X 60 *
        (groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
            (alpha - 1) ≤ V := by
    intro box _helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  have halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hD hthreshold
  by_cases halphaHi : alpha ≤ 19 / 25
  · simpa only [a, B, alpha] using
      (htransition hX.le hL hXscale hLscale hmuLo hmuHi halphaLo halphaHi
        hV hK B hB c hc hband haggregate hreserve)
  · have halphaThreeQuarter : 3 / 4 ≤ alpha := by
      have : 19 / 25 < alpha := lt_of_not_ge halphaHi
      norm_num at this ⊢
      linarith
    simpa only [a, B, alpha] using
      (hupper hX.le hL hXL hXscale hLscale hmuLo hmuHi halphaThreeQuarter
        hV hK B hB c hc hband haggregate hreserve)

end RHTower.Sieve
