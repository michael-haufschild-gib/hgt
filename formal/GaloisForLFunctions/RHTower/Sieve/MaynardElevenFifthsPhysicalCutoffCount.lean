import GaloisForLFunctions.RHTower.Sieve.MaynardElevenFifthsWindowRelevantAggregateCount
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockSelectedCount

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

/-!
# Route T selected-cell counting through 11/5 at a physical cutoff

The low-ordinate analytic estimates naturally use the canonical cutoff `X / 2^120`, whereas
the prime-free packet retains a larger physical cutoff.  Window relevance is contravariantly
monotone in that cutoff, so the analytic estimates may be transported downward without changing
the cutoff appearing in the selected cell.  This closes the cutoff mismatch before the parity
and amplitude-band receiver stages.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Window relevance is contravariantly monotone in its physical lower cutoff. -/
theorem isHeathBrownBoxWindowRelevant_of_le_elevenFifths
    {L X k : ℕ} {Nsmall Nlarge : ℝ} {box : HeathBrownBoxChoice L X k}
    (hcut : Nsmall ≤ Nlarge)
    (hrel : IsHeathBrownBoxWindowRelevant Nlarge X k box) :
    IsHeathBrownBoxWindowRelevant Nsmall X k box :=
  ⟨hrel.1, hcut.trans_lt hrel.2⟩

/-- Aggregate selection at a physical cutoff above the canonical analytic low cutoff still admits
complete 11/5 selected-cell extraction, and the output retains the original physical cutoff. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_label_of_physicalAggregate_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ N0 c y alpha V : ℝ, (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
          0 ≤ c → T ≤ y → y ≤ 2 * T → 3 / 4 ≤ alpha → 0 < V →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant N0 X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ label : HeathBrownSelectionLabel L X 60,
            IsMaynardWindowRelevantSelectedCell
              L X T mu N0 c y alpha label := by
  filter_upwards [
    eventually_maynard_lowOrdinate_box_subHeight_mass_of_high_amplitude,
    eventually_maynard_lowOrdinate_box_overHeight_small_elevenFifths,
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_mass_elevenFifths
  ] with T hmassT hsmallT hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL N0 c y alpha V hlowCutoff
    hc hylo hyhi halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hterm⟩ :=
    exists_large_windowRelevant_eligible_heathBrownBox
      L X 60 (by norm_num) T (mu / 120) N0
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
  have hrelLow : IsHeathBrownBoxWindowRelevant
      ((X : ℝ) / (2 ^ 120 : ℝ)) X 60 box :=
    isHeathBrownBoxWindowRelevant_of_le_elevenFifths hlowCutoff hrel
  have hmu0 : 0 < mu := by linarith
  have halphaBoundary : 1 - (89 / 100 : ℝ) / mu < alpha := by
    have hratio : (1 / 4 : ℝ) < (89 / 100 : ℝ) / mu := by
      rw [lt_div_iff₀ hmu0]
      linarith
    linarith
  have hmass := hmassT X hX mu hmuLo (by linarith : mu ≤ 8) hXscale
    L hL box helig hrelLow (hmobius box) c y alpha hc hylo hyhi
      halphaBoundary hcore
  have hsmall := hsmallT X hX mu hmuHi hXscale L hL box hrelLow
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  obtain ⟨label, _hlabelBox, hcell⟩ :=
    hpoint hL hX hmuLo hmuHi hXscale box helig hrel (hmobius box)
      hmass hsmall hc hylo hyhi halpha hcore
  exact ⟨label, hcell⟩

/-- Finite coloring at the original physical cutoff, using low-cutoff estimates only internally. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_physicalAggregate_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ N0 c alpha V : ℝ, (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
          0 ≤ c → 3 / 4 ≤ alpha → 0 < V →
        ∀ S : Finset ℕ, ∀ y : ℕ → ℝ,
          (∀ r ∈ S, T ≤ y r ∧ y r ≤ 2 * T) →
          (∀ box : HeathBrownBoxChoice L X 60,
            ∀ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownBoxFactorKind 60 box.m i = .moebius →
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                    2 * (mu / 120)) →
          (∀ r ∈ S, V ≤ ‖heathBrownWindowRelevantEligibleDyadicAggregate
            L X 60 T (mu / 120) N0
              ((c : ℂ) + (y r : ℝ) * Complex.I)‖) →
          (∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            IsHeathBrownBoxWindowRelevant N0 X 60 box →
              heathBrownEligibleBoxCost L X 60 *
                (groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                    (alpha - c) ≤ V) →
          ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
            ∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
              L X T mu N0 c (y r) alpha (color r) := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_physicalAggregate_elevenFifths
  ] with T hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL N0 c alpha V hlowCutoff hc
    halpha hV S y hy hmobius haggregate hreserve
  classical
  have hchoose : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        IsMaynardWindowRelevantSelectedCell L X T mu N0 c (y r) alpha label := by
    intro r hr
    exact hpoint X hX mu hmuLo hmuHi hXscale L hL N0 c (y r) alpha V
      hlowCutoff hc (hy r hr).1 (hy r hr).2 halpha hV hmobius
        (haggregate r hr) hreserve
  choose selected hselected using hchoose
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

/-- Fixed-cutoff all-amplitude capstone through `mu <= 11/5` at every physical cutoff above the
canonical analytic low cutoff. -/
theorem exists_eventually_routeT_selectedCell_physicalFixedCutoff_all_amplitude_elevenFifths :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha V delta : ℝ},
      1 ≤ X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
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
    exists_eventually_routeT_endpoint_box_amplitude_exclusion_elevenFifths
  refine ⟨A, ?_⟩
  filter_upwards [hboxExclude,
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_physicalAggregate_elevenFifths,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_elevenFifths A,
    eventually_gt_atTop (1 : ℝ)] with T hbox hcolorT hlowT hmiddleT hglobal hT
  intro L X K mu N0 c alpha V delta hX hL hXL hXscale hcut hmuLo hmuHi
    hlowCutoff hc halphaLo hV hdelta hdeltaHi S hS lam hband hgap hdiam
    haggregate hreserve
  have hmobius : ∀ box : HeathBrownBoxChoice L X 60,
      ∀ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownBoxFactorKind 60 box.m i = .moebius →
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
              2 * (mu / 120) := by
    intro box i hi
    exact box.moebius_factor_dyadicLogExponent_le hT hL hcut i hi
  obtain ⟨color, hcolor⟩ := hcolorT X hX mu hmuLo hmuHi hXscale L hL
    N0 c alpha V hlowCutoff (by linarith) halphaLo hV S lam hband hmobius
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

/-- Receiver-normalized parity transport at a physical cutoff through `mu <= 11/5`. Each parity
fibre retains its own Maynard alternative, so the later large-error step can force the second one
without mixing fibres. -/
theorem eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_twoAlternative_elevenFifths
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
      3 / 4 ≤ alpha → 0 < V → (K : ℝ) ≤ T →
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
  obtain ⟨A, hcount⟩ :=
    exists_eventually_routeT_selectedCell_physicalFixedCutoff_all_amplitude_elevenFifths
  filter_upwards [hcount,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A q,
    eventually_routeTSelectedCellAmplitudeReceiverCost_absorbed A 0,
    eventually_gt_atTop (1 : ℝ)] with T hcountT hcostQ hcost0 hT
  intro L X K mu N0 alpha V hX hL hXL hXscale hcut hmuLo hmuHi
    hlowCutoff halpha hV hK B hB c hc hband haggregate hreserve
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
  have hdiam0 : ∀ r ∈ S0, ∀ s ∈ S0, |lam0 s - lam0 r| ≤ T := by
    intro r hr s hs
    have hrb := hband0 r hr
    have hsb := hband0 s hs
    rw [abs_le]
    constructor <;> linarith
  have hdiam1 : ∀ r ∈ S1, ∀ s ∈ S1, |lam1 s - lam1 r| ≤ T := by
    intro r hr s hs
    have hrb := hband1 r hr
    have hsb := hband1 s hs
    rw [abs_le]
    constructor <;> linarith
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
  have hraw0 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi hlowCutoff
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S0 hS0 lam0 hband0 hgap0 hdiam0 haggregate0 hreserve
  have hraw1 := hcountT hX hL hXL hXscale hcut hmuLo hmuHi hlowCutoff
    (by norm_num : (1 : ℝ) / 2 ≤ 1) halpha hV
    (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ 2 * T)
    S1 hS1 lam1 hband1 hgap1 hdiam1 haggregate1 hreserve
  have hreservePos : 0 < routeTSelectedCellAmplitudeReserve A T alpha :=
    routeTSelectedCellAmplitudeReserve_pos hT
  have normalize :
      ∀ {R : ℝ},
      (R ≤ maynardHarmonicFactor K 1 *
            T ^ (mu * (1 - alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha) ∨
        R ≤ maynardHarmonicFactor K 1 *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
              routeTSelectedCellAmplitudeReserve A T alpha)) →
      IsRouteTMaynardTwoAlternative q R T (T ^ mu) alpha := by
    intro R hraw
    apply routeT_two_alternative_of_reserved_height_count hT rfl hreservePos
    rcases hraw with hfirst | hsecond
    · left
      exact maynard_count_receiver_margin_general hT.le hfirst
        (hcostQ alpha K 1 hK (by norm_num))
    · right
      have hsecond' := maynard_count_receiver_margin_general
        (q := 0) hT.le hsecond (hcost0 alpha K 1 hK (by norm_num))
      simpa using hsecond'
  constructor
  · simpa only [S0] using normalize hraw0
  · simpa only [S1] using normalize hraw1

/-- Exact amplitude bands of the physical left-window packet satisfy both receiver-normalized
parity alternatives through `mu <= 11/5`, at the original packet cutoff. -/
theorem eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative_elevenFifths
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 V : ℝ},
      1 < X → 1 ≤ L → X < (L + 1) ^ 60 →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
      1 < N0 / (2 ^ (2 * 60) : ℝ) →
      0 < V →
      heathBrownEligibleBoxCost L X 60 *
          (N0 / (2 ^ (2 * 60) : ℝ)) ^ (-(1 : ℝ) / 4) ≤ V →
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
    eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_twoAlternative_elevenFifths q
  ] with T hreceiver
  intro L X K mu N0 V hX hL hXL hXscale hcut hmuLo hmuHi hlowCutoff
    hD hV hlow hK U hU c hc hordinate
  let a : ℝ → ℂ := fun y =>
    heathBrownWindowRelevantEligibleDyadicAggregate
      L X 60 T (mu / 120) N0 ((1 : ℂ) + (y : ℝ) * Complex.I)
  let B : Finset ℕ := maynardUnitCellAmplitudeBand U a c V
  have hB : B ⊆ Finset.range (2 * K) :=
    (maynardUnitCellAmplitudeBand_subset U a c V).trans hU
  have halpha : 3 / 4 ≤ routeTAdaptiveCellAmplitude L X 60 N0 V :=
    routeTAdaptiveCellAmplitude_threeQuarter_le L X 60
      (by norm_num) hX hD hV hlow
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
    intro box helig hwin
    exact routeTAdaptiveCellAmplitude_windowRelevant_reserve
      L X 60 (by norm_num) hX hD hV box hwin
  simpa only [a, B] using
    (hreceiver hX.le hL hXL hXscale hcut hmuLo hmuHi hlowCutoff
      halpha hV hK B hB c hc hband haggregate hreserve)

end RHTower.Sieve
