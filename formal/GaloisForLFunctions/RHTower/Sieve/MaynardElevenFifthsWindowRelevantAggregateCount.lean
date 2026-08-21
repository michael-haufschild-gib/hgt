import GaloisForLFunctions.RHTower.Sieve.MaynardElevenFifthsSelectedCellExclusion

/-!
# Complete Route-T aggregate count through height ratio `11/5`

The exact box-cost reserve cancels the finite aggregate selector multiplicity before selected-cell
extraction.  Consequently the arbitrary-height canonical-box theorem lifts to the literal
window-relevant aggregate without any new exponent loss.  The resulting all-amplitude count
internalizes box selection, finite coloring, endpoint exclusion, and the canonical Möbius cutoff.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- At the canonical physical cutoff, aggregate largeness and the exact box-cost reserve select
one complete Route-T cell through the natural height ceiling `mu <= 11/5`. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_label_of_aggregate_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ c y alpha V : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          3 / 4 ≤ alpha → 0 < V →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) (X / (2 ^ 120 : ℝ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant (X / (2 ^ 120 : ℝ)) X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ label : HeathBrownSelectionLabel L X 60,
            IsMaynardWindowRelevantSelectedCell
              L X T mu (X / (2 ^ 120 : ℝ)) c y alpha label := by
  filter_upwards [
    eventually_maynard_lowOrdinate_box_subHeight_mass_of_high_amplitude,
    eventually_maynard_lowOrdinate_box_overHeight_small_elevenFifths,
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_mass_elevenFifths
  ] with T hmassT hsmallT hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V hc hylo hyhi
    halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hterm⟩ :=
    exists_large_windowRelevant_eligible_heathBrownBox
      L X 60 (by norm_num) T (mu / 120) (X / (2 ^ 120 : ℝ))
        ((c : ℂ) + (y : ℝ) * Complex.I) hV haggregate
  have hterm' : V ≤ heathBrownEligibleBoxCost L X 60 *
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
        ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
    dsimp [heathBrownBoxTerm] at hterm
    rw [norm_heathBrownDyadicTermProduct_eq_choose_mul_core] at hterm
    have hchoose : (Nat.choose 60 box.m : ℝ) ≤ (2 ^ 60 : ℝ) := by
      exact_mod_cast Nat.choose_le_two_pow 60 box.m
    calc
      V ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          ((Nat.choose 60 box.m : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := hterm
      _ ≤ (Fintype.card (HeathBrownBoxChoice L X 60) : ℝ) *
          ((2 ^ 60 : ℝ) *
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖) := by gcongr
      _ = heathBrownEligibleBoxCost L X 60 *
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ := by
        dsimp only [heathBrownEligibleBoxCost]
        ring
  have hscaled := (hreserve box helig hrel).trans hterm'
  have hcost := heathBrownEligibleBoxCost_pos L X 60 (by norm_num)
  have hcore :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
          (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ :=
    (mul_le_mul_iff_right₀ hcost).mp hscaled
  have hmu0 : 0 < mu := by linarith
  have halphaBoundary : 1 - (89 / 100 : ℝ) / mu < alpha := by
    have hratio : (1 / 4 : ℝ) < (89 / 100 : ℝ) / mu := by
      rw [lt_div_iff₀ hmu0]
      linarith
    linarith
  have hmass := hmassT X hX mu hmuLo (by linarith : mu ≤ 8) hXscale
    L hL box helig hrel (hmobius box) c y alpha hc hylo hyhi
      halphaBoundary hcore
  have hsmall := hsmallT X hX mu hmuHi hXscale L hL box hrel
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  obtain ⟨label, _hlabelBox, hcell⟩ :=
    hpoint hL hX hmuLo hmuHi hXscale box helig hrel (hmobius box)
      hmass hsmall hc hylo hyhi halpha hcore
  exact ⟨label, hcell⟩

/-- Aggregate selector and 11/5 arbitrary-box extraction commute with finite coloring: no extra
box exponent is lost beyond the reserve already present in the aggregate hypothesis. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_aggregate_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ c alpha V : ℝ, 0 ≤ c → 3 / 4 ≤ alpha → 0 < V →
        ∀ S : Finset ℕ, ∀ y : ℕ → ℝ,
          (∀ r ∈ S, T ≤ y r ∧ y r ≤ 2 * T) →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          (∀ r ∈ S, V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) (X / (2 ^ 120 : ℝ))
              ((c : ℂ) + (y r : ℝ) * Complex.I)‖) →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant (X / (2 ^ 120 : ℝ)) X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
            ∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
              L X T mu (X / (2 ^ 120 : ℝ)) c (y r) alpha (color r) := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_aggregate_elevenFifths
  ] with T hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL c alpha V hc halpha hV
    S y hy hmobius haggregate hreserve
  classical
  have hchoose : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        IsMaynardWindowRelevantSelectedCell
          L X T mu (X / (2 ^ 120 : ℝ)) c (y r) alpha label := by
    intro r hr
    exact hpoint X hX mu hmuLo hmuHi hXscale L hL c (y r) alpha V hc
      (hy r hr).1 (hy r hr).2 halpha hV hmobius (haggregate r hr) hreserve
  choose selected hselected using hchoose
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

/-- Complete all-amplitude Route-T count for the literal canonical window-relevant aggregate
through `mu <= 11/5`. Box selection, arbitrary-height atom excision, endpoint exclusion, and
finite-label entropy are all internal. -/
theorem exists_eventually_routeT_windowRelevantAggregate_all_amplitude_first_or_second_elevenFifths :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {X K : ℕ} {mu c alpha V delta : ℝ},
      1 ≤ X → (X : ℝ) ≤ T ^ mu →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
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
            L X 60 T (mu / 120) (X / (2 ^ 120 : ℝ))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
      (∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxWindowRelevant (X / (2 ^ 120 : ℝ)) X 60 box →
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
  obtain ⟨A, _C, _C', _delta0, _hC, _hC', _hdelta0, hboxExclude⟩ :=
    exists_eventually_routeT_endpoint_box_amplitude_exclusion_elevenFifths
  refine ⟨A, ?_⟩
  filter_upwards [hboxExclude,
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_aggregate_elevenFifths,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_elevenFifths A,
    eventually_gt_atTop (1 : ℝ)] with T hbox hcolorT hlowT hmiddleT hglobal hT
  intro X K mu c alpha V delta hX hXscale hmuLo hmuHi hc halphaLo hV
    hdelta hdeltaHi S hS lam hband hgap hdiam haggregate hreserve
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
    c alpha V (by linarith) halphaLo hV S lam hband hmobius
      (haggregate L hL hXL) (hreserve L hL hXL)
  refine ⟨L, hL, hXL, hcut', ?_⟩
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
      · have hSempty : S = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hSne
          obtain ⟨r, hr⟩ := hSne
          have hcell := hcolor r hr
          have hbound := hbox X hX mu hmuLo hmuHi hXscale L hL hcut'
            (color r).1 hcell.1 c (lam r) alpha (by linarith)
              (hband r hr).1 (hband r hr).2 hcell.2.2.1
          exact halphaEndpoint hbound
        left
        rw [hSempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
          (Real.rpow_nonneg (by linarith) _)

end RHTower.Sieve
