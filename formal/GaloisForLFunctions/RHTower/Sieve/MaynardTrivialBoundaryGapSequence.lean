import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryBandCoverage
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTFixedCutoffCount

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Transition-strip receiver for one already-spaced selected ordinate sequence. -/
theorem eventually_routeT_selectedCell_fixedCutoff_gapSequence_twoAlternative_transition
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < V → 1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ box : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
        IsHeathBrownBoxWindowRelevant N0 X 60 box →
        heathBrownEligibleBoxCost L X 60 *
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
              (alpha - 1) ≤ V) →
      IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu) alpha := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_to_trivialBoundary,
    eventually_card_le_maynard_second_of_selected_cell_coloring_transition,
    eventually_maynardHarmonicFixedLogCost_absorbed
      (r := 1 / 400) (by norm_num) 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcolorT hcountT hcost hT
  intro L X K mu N0 alpha V delta hX hL hXscale hLscale hmuLo hmuHi
    halphaLo halphaHi hV hdelta hdeltaHi hK S hS lam hband hgap haggregate hreserve
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hLscale i hi
  obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
    1 alpha V N0 (by norm_num) halphaLo hV S lam hband hmobius
      haggregate hreserve
  have hraw := hcountT hX hL hXscale hLscale hmuLo hmuHi (by norm_num)
    halphaLo halphaHi (by positivity : 0 < delta) hdeltaHi S hS lam hgap hband
      color hcolor
  have hcost' : maynardHarmonicFactor K delta * (Real.log T) ^ 0 ≤
      T ^ ((1 / 200 : ℝ) / 2) := by
    simpa only [show (1 / 200 : ℝ) / 2 = 1 / 400 by norm_num] using
      hcost K delta hK hdelta
  apply routeT_two_alternative_of_reserved_height_count
    hT rfl (by norm_num : (0 : ℝ) < 1 / 200)
  right
  simpa using
    (maynard_count_receiver_margin_general (q := 0) hT.le hraw hcost')

/-- Full trivial-boundary receiver for one spaced selected ordinate sequence. -/
theorem eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_above_trivialBoundary
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V delta : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V →
      1 ≤ delta → delta ≤ 2 * T → (K : ℝ) ≤ T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
          L X 60 T (mu / 120) N0
            ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu)
        (routeTAdaptiveCellAmplitude L X 60 N0 V) := by
  obtain ⟨A, hupper⟩ :=
    exists_eventually_routeT_selectedCell_fixedCutoff_all_amplitude
  filter_upwards [
    eventually_routeT_selectedCell_fixedCutoff_gapSequence_twoAlternative_transition q,
    hupper,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A q,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with
      T htransition hupperT hcostQ hcost0 hT
  intro L X K mu N0 V delta hX hL hXL hXscale hLscale hmuLo hmuHi hD
    hV hthreshold hdelta hdeltaHi hK S hS lam hband hgap hdiam haggregate
  let alpha : ℝ := routeTAdaptiveCellAmplitude L X 60 N0 V
  have halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha := by
    dsimp only [alpha]
    exact routeT_trivialCountBoundary_le_adaptive_of_threshold_le
      L X 60 (by norm_num) hX hD hthreshold
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
  by_cases halphaHi : alpha ≤ 19 / 25
  · simpa only [alpha] using
      (htransition hX.le hL hXscale hLscale hmuLo hmuHi halphaLo halphaHi
        hV hdelta hdeltaHi hK S hS lam hband hgap haggregate hreserve)
  · have halphaThreeQuarter : 3 / 4 ≤ alpha := by
      have : 19 / 25 < alpha := lt_of_not_ge halphaHi
      norm_num at this ⊢
      linarith
    have hraw := hupperT hX.le hL hXL hXscale hLscale hmuLo hmuHi
      (by norm_num : (1 : ℝ) / 2 ≤ 1) halphaThreeQuarter hV
      (by positivity : 0 < delta) hdeltaHi S hS lam hband hgap hdiam
        haggregate hreserve
    have normalize :
        ((S.card : ℝ) ≤ maynardHarmonicFactor K delta *
              T ^ (mu * (1 - alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha) ∨
          (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
              T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
                routeTSelectedCellAmplitudeReserve A T alpha)) →
        IsRouteTMaynardTwoAlternative q (S.card : ℝ) T (T ^ mu) alpha := by
      intro hcount
      apply routeT_two_alternative_of_reserved_height_count
        hT rfl (routeTSelectedCellAmplitudeReserve_pos (A := A) hT)
      rcases hcount with hfirst | hsecond
      · left
        exact maynard_count_receiver_margin_general hT.le hfirst
          (hcostQ alpha K delta hK hdelta)
      · right
        have hsecond' := maynard_count_receiver_margin_general
          (q := 0) hT.le hsecond (hcost0 alpha K delta hK hdelta)
        simpa using hsecond'
    simpa only [alpha] using normalize hraw

private theorem cast_two_mul_add_one_le_two_mul
    {j n : ℕ} (h : j < n) :
    (((2 * j : ℕ) : ℝ) + 1) ≤ (2 * n : ℕ) := by
  norm_cast
  omega

private theorem cast_two_mul_add_one_add_one_le_two_mul
    {j n : ℕ} (h : j < n) :
    (((2 * j + 1 : ℕ) : ℝ) + 1) ≤ (2 * n : ℕ) := by
  norm_cast
  omega

/-- Exact even-cell discretization of a central ordinate shell feeds the trivial-boundary
receiver without integer endpoint trimming or a unit-cell reindexing hypothesis. -/
theorem eventually_exists_routeT_adjacentDefect_central_gapSequence_receiver_above_trivialBoundary
    (receiverQ : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X n Q : ℕ} {mu N0 H R delta B : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < H → 0 < R → H ≤ R →
      1 ≤ delta → delta ≤ 2 → 0 < B → 0 < Q →
      T + ((2 * n : ℕ) : ℝ) * delta ≤ 2 * T →
      (∀ y ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta),
        |y| ≤ N0 / (2 * R)) →
      B ≤ ‖∫ y in T..(T + ((2 * n : ℕ) : ℝ) * delta),
        heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (mu / 120) N0
            ((1 : ℂ) + (y : ℝ) * Complex.I) *
          (routeTNormalizedSmoothWindowMellin N0 R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N0 H
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ →
      heathBrownWindowRelevantFixedPolylogBound L X 60 N0 1 ≤
        (((2 ^ Q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) →
      (n : ℝ) * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤
        B / (16 * delta) →
      ∃ lam : ℕ → ℝ, ∃ S : Finset ℕ, ∃ q : ℕ,
        (∀ i, lam i + delta ≤ lam (i + 1)) ∧
        S ⊆ Finset.range n ∧ q < Q ∧
        (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) ∧
        (∀ r ∈ S, (((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) ≤
            ‖heathBrownWindowRelevantEligibleDyadicAggregate
              L X 60 T (mu / 120) N0
                ((1 : ℂ) + (lam r : ℝ) * Complex.I)‖) ∧
        B / (16 * delta * (Q : ℝ)) ≤
          (((2 ^ q : ℕ) : ℝ) *
            routeTTrivialBoundaryAmplitudeThreshold L X 60 N0) *
              (S.card : ℝ) ∧
        IsRouteTMaynardTwoAlternative receiverQ (S.card : ℝ) T (T ^ mu)
          (routeTAdaptiveCellAmplitude L X 60 N0
            (((2 ^ q : ℕ) : ℝ) *
              routeTTrivialBoundaryAmplitudeThreshold L X 60 N0)) := by
  filter_upwards [
    eventually_routeT_leftWindowRelevant_gapSequence_twoAlternative_above_trivialBoundary
      receiverQ,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hreceiver hT
  intro L X n Q mu N0 H R delta B hX hL hXL hXscale hLscale hmuLo hmuHi
    hD hH hR hHR hdelta hdeltaTwo hB hQ hshellTop hcentral hdefect hcap hsmall
  let v : ℝ := routeTTrivialBoundaryAmplitudeThreshold L X 60 N0
  have hv : 0 < v := by
    dsimp only [v]
    exact routeTTrivialBoundaryAmplitudeThreshold_pos L X 60 (by norm_num) hD
  obtain ⟨lam, S, q, hgap, hS, hq, hmem, hlarge, hmass⟩ :=
    exists_gap_sequence_dyadic_superlevel_of_adjacent_defect_central
      L X 60 T (mu / 120) hX.le (by
        have hden : 0 < (2 ^ (2 * 60) : ℝ) := by positivity
        exact hden.trans ((one_lt_div hden).mp hD))
      hH hR hHR (by positivity : 0 < delta) hB hv hQ hcentral hdefect
      (by simpa only [v] using hcap) (by simpa only [v] using hsmall)
  have hdelta0 : 0 ≤ delta := zero_le_one.trans hdelta
  have hmemShell : ∀ j < n,
      lam j ∈ Set.Icc T (T + ((2 * n : ℕ) : ℝ) * delta) := by
    intro j hj
    rcases hmem j hj with heven | hodd
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans heven.1
      · have hcast := cast_two_mul_add_one_le_two_mul hj
        exact heven.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
    · constructor
      · have hcoeff : (0 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        exact (le_add_of_nonneg_right (mul_nonneg hcoeff hdelta0)).trans hodd.1
      · have hcast := cast_two_mul_add_one_add_one_le_two_mul hj
        exact hodd.2.trans (by
          simpa only [add_comm] using add_le_add_left
            (mul_le_mul_of_nonneg_right hcast hdelta0) T)
  have hband : ∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    have hrn := Finset.mem_range.mp (hS hr)
    have hm := hmemShell r hrn
    exact ⟨hm.1, hm.2.trans hshellTop⟩
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hnT : (n : ℝ) ≤ T := by
    have hnleTwoN : (n : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * n by omega)
    have htwoN0 : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hscale : ((2 * n : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) * delta := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hdelta htwoN0
    have hmul : ((2 * n : ℕ) : ℝ) * delta ≤ T := by linarith
    exact hnleTwoN.trans (hscale.trans hmul)
  have hdeltaTop : delta ≤ 2 * T := by
    calc
      delta ≤ 2 := hdeltaTwo
      _ = 2 * 1 := by ring
      _ ≤ 2 * T := mul_le_mul_of_nonneg_left hT.le (by norm_num)
  let V : ℝ := (((2 ^ q : ℕ) : ℝ) * v)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hthreshold : routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 ≤ V := by
    have hp : (1 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    dsimp only [V, v]
    calc
      routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 =
          1 * routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 := by ring
      _ ≤ ((2 ^ q : ℕ) : ℝ) *
          routeTTrivialBoundaryAmplitudeThreshold L X 60 N0 :=
        mul_le_mul_of_nonneg_right hp hv.le
  have halt := hreceiver hX hL hXL hXscale hLscale hmuLo hmuHi hD hV
    hthreshold hdelta hdeltaTop hnT S hS lam hband hgap hdiam
      (by simpa only [V, v] using hlarge)
  refine ⟨lam, S, q, hgap, hS, hq, hband, ?_, ?_, ?_⟩
  · simpa only [v] using hlarge
  · simpa only [v] using hmass
  · simpa only [V, v] using halt

end RHTower.Sieve
