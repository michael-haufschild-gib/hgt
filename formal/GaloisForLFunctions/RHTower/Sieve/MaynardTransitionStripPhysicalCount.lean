import GaloisForLFunctions.RHTower.Sieve.MaynardTransitionStripCount
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSelectedCount

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- At the exact transition strip, both parity fibres of a physical unit-cell family obey
the reserved second selected-cell count directly. -/
theorem eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_second_transition :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < V →
      ∀ (B : Finset ℕ), B ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T) →
      (∀ m ∈ B,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (c m : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      ((maynardEvenCellFibre B K).card : ℝ) ≤
          maynardHarmonicFactor K 1 *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) ∧
        ((maynardOddCellFibre B K).card : ℝ) ≤
          maynardHarmonicFactor K 1 *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_to_trivialBoundary,
    eventually_card_le_maynard_second_of_selected_cell_coloring_transition,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcolorT hcountT hT
  intro L X K mu N0 alpha V hX hL hXscale hLscale hmuLo hmuHi
    halphaLo halphaHi hV B hB c hc hband haggregate hreserve
  let S0 : Finset ℕ := maynardEvenCellFibre B K
  let S1 : Finset ℕ := maynardOddCellFibre B K
  let lam0 : ℕ → ℝ := fun i => c (2 * i)
  let lam1 : ℕ → ℝ := fun i => c (2 * i + 1)
  have hS0 : S0 ⊆ Finset.range K := Finset.filter_subset _ _
  have hS1 : S1 ⊆ Finset.range K := Finset.filter_subset _ _
  have hmem0 : ∀ i ∈ S0, 2 * i ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmem1 : ∀ i ∈ S1, 2 * i + 1 ∈ B := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hband0 : ∀ i ∈ S0, T ≤ lam0 i ∧ lam0 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i) (hmem0 i hi)
  have hband1 : ∀ i ∈ S1, T ≤ lam1 i ∧ lam1 i ≤ 2 * T := by
    intro i hi
    exact hband (2 * i + 1) (hmem1 i hi)
  have hgap0 : ∀ i, lam0 i + 1 ≤ lam0 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 0 i
  have hgap1 : ∀ i, lam1 i + 1 ≤ lam1 (i + 1) := by
    intro i
    exact unitCellRepresentative_parity_gap hc 1 i
  have haggregate0 : ∀ i ∈ S0,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam0 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i) (hmem0 i hi)
  have haggregate1 : ∀ i ∈ S1,
      V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam1 i : ℝ) * Complex.I)‖ := by
    intro i hi
    exact haggregate (2 * i + 1) (hmem1 i hi)
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hLscale i hi
  have count : ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + 1 ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
        L X 60 T (mu / 120) N0
          ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K 1 *
        T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
    intro S hS lam hgap hbandS haggregateS
    obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
      1 alpha V N0 (by norm_num) halphaLo hV S lam hbandS hmobius
        haggregateS hreserve
    exact hcountT hX hL hXscale hLscale hmuLo hmuHi (by norm_num)
      halphaLo halphaHi (by norm_num) (by linarith) S hS lam hgap hbandS
        color hcolor
  constructor
  · simpa only [S0] using count S0 hS0 lam0 hgap0 hband0 haggregate0
  · simpa only [S1] using count S1 hS1 lam1 hgap1 hband1 haggregate1

/-- The transition-strip parity counts land in Route T's second receiver after absorbing the
harmonic spacing factor into half of the fixed Montgomery reserve. -/
theorem eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative_transition
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < V → (K : ℝ) ≤ T →
      ∀ (B : Finset ℕ), B ⊆ Finset.range (2 * K) →
      ∀ (c : ℕ → ℝ),
      (∀ m : ℕ, c m ∈ Set.Icc (m : ℝ) ((m : ℝ) + 1)) →
      (∀ m ∈ B, T ≤ c m ∧ c m ≤ 2 * T) →
      (∀ m ∈ B,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (c m : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      IsRouteTMaynardTwoAlternative q
          ((maynardEvenCellFibre B K).card : ℝ) T (T ^ mu) alpha ∧
        IsRouteTMaynardTwoAlternative q
          ((maynardOddCellFibre B K).card : ℝ) T (T ^ mu) alpha := by
  filter_upwards [
    eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_second_transition,
    eventually_maynardHarmonicFixedLogCost_absorbed
      (r := 1 / 400) (by norm_num) 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcount hcost hT
  intro L X K mu N0 alpha V hX hL hXscale hLscale hmuLo hmuHi
    halphaLo halphaHi hV hK B hB c hc hband haggregate hreserve
  obtain ⟨hraw0, hraw1⟩ := hcount hX hL hXscale hLscale hmuLo hmuHi
    halphaLo halphaHi hV B hB c hc hband haggregate hreserve
  have normalize : ∀ {R : ℝ},
      R ≤ maynardHarmonicFactor K 1 *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) →
      IsRouteTMaynardTwoAlternative q R T (T ^ mu) alpha := by
    intro R hraw
    apply routeT_two_alternative_of_reserved_height_count
      hT rfl (by norm_num : (0 : ℝ) < 1 / 200)
    right
    have hcost' : maynardHarmonicFactor K 1 * (Real.log T) ^ 0 ≤
        T ^ ((1 / 200 : ℝ) / 2) := by
      simpa only [show (1 / 200 : ℝ) / 2 = 1 / 400 by norm_num] using
        hcost K 1 hK (by norm_num)
    have hmargin := maynard_count_receiver_margin_general (q := 0) hT.le hraw hcost'
    simpa using hmargin
  constructor
  · exact normalize hraw0
  · exact normalize hraw1

/-- Every physical left-window amplitude band whose adaptive exponent lies in the transition
strip satisfies both receiver-normalized parity alternatives. No `3/4` amplitude floor remains. -/
theorem eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative_transition
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V : ℝ},
      1 < X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      (1 + routeTGapMomentNu) / 2 ≤
        routeTAdaptiveCellAmplitude L X 60 N0 V →
      routeTAdaptiveCellAmplitude L X 60 N0 V ≤ 19 / 25 →
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
    eventually_routeT_selectedCell_fixedCutoff_unitCellFamily_twoAlternative_transition q
  ] with T hreceiver
  intro L X K mu N0 V hX hL hXscale hLscale hmuLo hmuHi hD hV
    halphaLo halphaHi hK U hU c hc hordinate
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate
      L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
  let B : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
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
            (routeTAdaptiveCellAmplitude L X 60 N0 V - 1) ≤ V := by
    intro box _helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  simpa only [a, B] using
    (hreceiver hX.le hL hXscale hLscale hmuLo hmuHi halphaLo halphaHi
      hV hK B hB c hc hband haggregate hreserve)

end RHTower.Sieve
