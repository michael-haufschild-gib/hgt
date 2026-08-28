import GaloisForLFunctions.RHTower.Sieve.MaynardElevenFifthsPhysicalCutoffCount
import GaloisForLFunctions.RHTower.Sieve.MaynardTrivialBoundaryAmplitude

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

/-- Through `mu ≤ 11/5`, the over-height deficit reaches the exact Route-T trivial-count
boundary; every over-height atom is below its own `N^(alpha-c)` threshold. -/
theorem eventually_maynard_lowOrdinate_box_overHeight_small_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxWindowRelevant (X / (2 ^ 120 : ℝ)) X 60 box →
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownBoxFactorKind 60 box.m i = .moebius →
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                  2 * (mu / 120)) →
          ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
            (1 + routeTGapMomentNu) / 2 ≤ alpha →
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
              (alpha - c) ≤
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          ∀ i : PositiveHeathBrownBoxFactorIndex box,
            1 ≤ dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) →
            ‖heathBrownBoxFactorValue L X 60 box
                ((c : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
                (alpha - c) := by
  filter_upwards [eventually_maynard_lowOrdinate_overHeight_zeta_weighted_deficit,
    eventually_maynard_lowOrdinate_overHeight_log_weighted_deficit,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hT
  intro X hX mu hmuHi hXscale L hL box hwindow hmobius
    c y alpha hc hylo hyhi halpha hlarge i hi
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qi : ℕ := heathBrownBoxFactorExponent box.a box.b box.q i
  let Z : HeathBrownBoxFactorIndex 60 box.m → ℂ := fun j =>
    heathBrownBoxFactorValue L X 60 box s j
  have hD0 : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 <
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
            (alpha - c) := Real.rpow_pos_of_pos hD0 _
    exact hthreshold.trans_le (by simpa [s] using hlarge)
  have hprodZ : (∏ j, Z j) =
      heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s := by
    simpa [Z, heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
      L X 60 box.m box.a box.b box.q s
  have hZi : Z i ≠ 0 := by
    intro hzero
    have hpzero : ∏ j, Z j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (i : HeathBrownBoxFactorIndex 60 box.m)) hzero
    rw [hprodZ] at hpzero
    rw [hpzero, norm_zero] at hcorePos
    exact (lt_irrefl 0) hcorePos
  have hV : 0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
    exact norm_pos_iff.mpr (by simpa [Z] using hZi)
  have hkind : heathBrownBoxFactorKind 60 box.m i = .zeta ∨
      heathBrownBoxFactorKind 60 box.m i = .log := by
    cases hk : heathBrownBoxFactorKind 60 box.m i with
    | moebius =>
        have hshort := hmobius i hk
        have : 2 * (mu / 120) < 1 := by linarith
        exact (not_lt_of_ge hi (hshort.trans_lt this)).elim
    | zeta => exact Or.inl rfl
    | log => exact Or.inr rfl
  have hqiX := box.factorExponent_le_log_X_of_zeta_or_log i hkind
  have hTN : T ≤ (((2 ^ qi : ℕ) : ℝ)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hi
    have hr := rpow_dyadicLogExponent hT qi
    simpa [Real.rpow_one, qi] using hpow.trans_eq hr
  let w : ℝ := dyadicLogExponent T qi
  have hw : 1 ≤ w := by simpa [w, qi] using hi
  have hwTotal : w ≤ heathBrownBoxTotalExponent L X 60 T box := by
    rw [← sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    exact Finset.single_le_sum
      (f := fun j : PositiveHeathBrownBoxFactorIndex box =>
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j))
      (s := Finset.univ)
      (fun j _ => dyadicLogExponent_nonneg hT
        (heathBrownBoxFactorExponent box.a box.b box.q j))
      (Finset.mem_univ i)
  have htotalMu : heathBrownBoxTotalExponent L X 60 T box ≤ mu :=
    windowRelevant_heathBrownBox_totalExponent_le hT hXscale box hwindow
  have hwMu : w ≤ mu := hwTotal.trans htotalMu
  have hweighted : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ * w ≤ w - 9 / 10 := by
    rcases hkind with hkind | hkind
    · have hz := hzeta X hX mu (by linarith : mu ≤ 8) hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, w, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hz (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
    · have hl := hlogFactor X hX mu (by linarith : mu ≤ 8) hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, w, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hl (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
  have hN : (1 : ℝ) < (((2 ^ qi : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 < 2 ^ qi by
      exact pow_lt_pow_right₀ (by norm_num) i.property)
  have hampAlpha : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤ alpha := by
    have hbudget : (1 - alpha) * w ≤ 9 / 10 := by
      by_cases halphaOne : alpha ≤ 1
      · have halphaLower : 149 / 200 < alpha := by
          dsimp only [routeTGapMomentNu] at halpha
          linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
        have hmul : (1 - alpha) * w ≤ (51 / 200 : ℝ) * mu :=
          mul_le_mul (by linarith) hwMu (zero_le_one.trans hw) (by norm_num)
        nlinarith
      · have hw0 : 0 ≤ w := zero_le_one.trans hw
        have : (1 - alpha) * w ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hw0
        linarith
    have hscaled : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X 60 box s i‖ * w ≤ alpha * w := by
      exact hweighted.trans (by linarith)
    exact (mul_le_mul_iff_right₀ (lt_of_lt_of_le zero_lt_one hw)).mp
      (by simpa [mul_comm] using hscaled)
  have hid := rpow_maynardAmplitude_sub_abscissa (c := c) hN hV
  have hbound : ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤
      (((2 ^ qi : ℕ) : ℝ)) ^ (alpha - c) := calc
    ‖heathBrownBoxFactorValue L X 60 box s i‖ =
        (((2 ^ qi : ℕ) : ℝ)) ^
          (maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
            ‖heathBrownBoxFactorValue L X 60 box s i‖ - c) := hid.symm
    _ ≤ (((2 ^ qi : ℕ) : ℝ)) ^ (alpha - c) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (sub_le_sub_right hampAlpha c)
  simpa [s, qi] using hbound

theorem eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_mass_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L X : ℕ} {mu N0 c y alpha : ℝ},
        1 ≤ L → 1 ≤ X → 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          IsHeathBrownBoxWindowRelevant N0 X 60 box →
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            heathBrownBoxFactorKind 60 box.m i = .moebius →
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q i) ≤
                  2 * (mu / 120)) →
          mu / 120 ≤ ∑ i ∈ (Finset.univ.filter
              fun i : PositiveHeathBrownBoxFactorIndex box =>
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) →
          (∀ i : PositiveHeathBrownBoxFactorIndex box,
            1 ≤ dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) →
            ‖heathBrownBoxFactorValue L X 60 box
                ((c : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
                (alpha - c)) →
          0 ≤ c → T ≤ y → y ≤ 2 * T →
          (1 + routeTGapMomentNu) / 2 ≤ alpha →
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
              (alpha - c) ≤
            ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
          ∃ label : HeathBrownSelectionLabel L X 60,
            label.1 = box ∧
            IsMaynardWindowRelevantSelectedCell
              L X T mu N0 c y alpha label := by
  filter_upwards [
    eventually_maynard_perronRelevant_moderate_global_amplitude_le_997_elevenFifths,
    eventually_maynard_perronRelevant_overweight_global_amplitude_le_nineEightyThree_div_thousand_elevenFifths,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hmoderate hoverweight hT
  intro L X mu N0 c y alpha hL hX hmuLo hmuHi hXscale box helig hrel
    hmobius hmass hsmall hc hylo hyupper halpha hcore
  obtain ⟨u, hune, husub, hbetaLo, hbetaHi, hlength, hlarge,
      hlocal, hheight⟩ :=
    exists_heathBrown_box_subHeight_group_of_mass
      L X 60 box hL hX hT (by linarith : 0 < mu / 120)
        ((c : ℂ) + (y : ℝ) * Complex.I) hmass hsmall hcore
  let beta : ℝ := ∑ i ∈ u, dyadicLogExponent T
    (heathBrownBoxFactorExponent box.a box.b box.q i)
  have hlocalKind (hbeta : 5 / 12 < beta) : ∃ j ∈ u,
      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
        heathBrownBoxFactorKind 60 box.m j = .log) ∧
      beta - 2 * (mu / 120) < dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j) := by
    obtain ⟨j, hju, hjweight⟩ := hlocal
    refine ⟨j, hju, ?_, by simpa [beta] using hjweight⟩
    cases hkind : heathBrownBoxFactorKind 60 box.m j with
    | moebius =>
        have hjupper := hmobius j hkind
        dsimp only [beta] at hbeta
        exfalso
        linarith
    | zeta => exact Or.inl rfl
    | log => exact Or.inr rfl
  have hheightKind : beta < 1 ∨ ∃ j ∈ u,
      (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
        heathBrownBoxFactorKind 60 box.m j = .log) ∧
      1 - 2 * (mu / 120) < dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j) := by
    rcases hheight with hregular | ⟨j, hju, hjweight⟩
    · exact Or.inl hregular
    · right
      refine ⟨j, hju, ?_, hjweight⟩
      cases hkind : heathBrownBoxFactorKind 60 box.m j with
      | moebius =>
          have hjupper := hmobius j hkind
          exfalso
          linarith
      | zeta => exact Or.inl rfl
      | log => exact Or.inr rfl
  have hbranch :
      beta ≤ 5 / 12 ∨
        (5 / 12 < beta ∧ beta < 1 ∧ alpha ≤ 997 / 1000 ∧
          ∃ j ∈ u,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) ∧
            beta - 2 * (mu / 120) < dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q j)) ∨
        (1 ≤ beta ∧ alpha ≤ 983 / 1000 ∧
          ∃ j ∈ u,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) ∧
            1 - 2 * (mu / 120) < dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q j)) := by
    by_cases hsmallBeta : beta ≤ 5 / 12
    · exact Or.inl hsmallBeta
    · have hbeta : 5 / 12 < beta := lt_of_not_ge hsmallBeta
      by_cases hregular : beta < 1
      · obtain ⟨j, hju, hkind, hjweight⟩ := hlocalKind hbeta
        have halpha997 := hmoderate X hX mu hmuLo hmuHi hXscale
          L hL 60 box helig hrel.1 c y alpha beta hc hylo hyupper
            hbeta j hkind hjweight hcore
        exact Or.inr (Or.inl
          ⟨hbeta, hregular, halpha997, j, hju, hkind, hjweight⟩)
      · have hbetaOne : 1 ≤ beta := le_of_not_gt hregular
        rcases hheightKind with hfalse | ⟨j, hju, hkind, hjweight⟩
        · exact (not_lt_of_ge hbetaOne hfalse).elim
        · have halpha983 := hoverweight X hX mu hmuLo hmuHi hXscale
            L hL 60 box helig hrel.1 c y alpha hc hylo hyupper
              j hkind hjweight hcore
          exact Or.inr (Or.inr
            ⟨hbetaOne, halpha983, j, hju, hkind, hjweight⟩)
  let label : HeathBrownSelectionLabel L X 60 := ⟨box, u⟩
  refine ⟨label, rfl, ?_⟩
  dsimp only [IsMaynardWindowRelevantSelectedCell]
  refine ⟨helig, hrel, hcore, hune, husub, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [maynardSubHeightSelectedExponent, label, beta] using hbetaLo
  · simpa [maynardSubHeightSelectedExponent, label, beta] using hbetaHi
  · simpa [maynardSubHeightSelectedExponent, label, beta,
      heathBrownSelectedExponent] using hlength
  · simpa [label, heathBrownSelectedExponent, heathBrownSelectedKind,
      HeathBrownSelectedFactor] using hlarge
  · simpa [IsMaynardSelectedCellBranch, maynardSubHeightSelectedExponent,
      label, beta] using hbranch


/-- Aggregate selection at a physical cutoff above the canonical analytic low cutoff still admits
complete 11/5 selected-cell extraction, and the output retains the original physical cutoff. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_label_of_physicalAggregate_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ N0 c y alpha V : ℝ, (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
          0 ≤ c → T ≤ y → y ≤ 2 * T → (1 + routeTGapMomentNu) / 2 ≤ alpha → 0 < V →
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
    eventually_maynard_lowOrdinate_box_overHeight_small_elevenFifths_trivialBoundary,
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_mass_elevenFifths_trivialBoundary
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
  have halphaStrict : (149 / 200 : ℝ) < alpha := by
    dsimp only [routeTGapMomentNu] at halpha
    linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
  have halphaBoundary : 1 - (89 / 100 : ℝ) / mu < alpha := by
    have hratio : (51 / 200 : ℝ) < (89 / 100 : ℝ) / mu := by
      rw [lt_div_iff₀ hmu0]
      nlinarith
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
theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_physicalAggregate_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ N0 c alpha V : ℝ, (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
          0 ≤ c → (1 + routeTGapMomentNu) / 2 ≤ alpha → 0 < V →
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
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_physicalAggregate_elevenFifths_trivialBoundary
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

theorem montgomery_two_term_envelope_trivialBoundary
    {W HF B U V A : ℝ} {e : ℕ}
    (hW : 1 ≤ W) (hHF : 1 ≤ HF) (hB : 1 ≤ B)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hA : A ≤ 3 * HF * B) :
    W * A * B ^ e * (3 * U + W * (4 * B) * V) ≤
      HF * (12 * W ^ 2 * B ^ (e + 2)) * (U + V) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hHF0 : 0 ≤ HF := zero_le_one.trans hHF
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have htail0 : 0 ≤ 3 * U + W * (4 * B) * V :=
    add_nonneg (mul_nonneg (by norm_num) hU)
      (mul_nonneg (mul_nonneg hW0 (mul_nonneg (by norm_num) hB0)) hV)
  have hreplace :
      W * A * B ^ e * (3 * U + W * (4 * B) * V) ≤
        W * (3 * HF * B) * B ^ e * (3 * U + W * (4 * B) * V) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA hW0) (pow_nonneg hB0 e)) htail0
  have hpow : B ^ (e + 1) ≤ B ^ (e + 2) :=
    pow_le_pow_right₀ hB (by omega)
  have hWsqCore : W ≤ W ^ 2 := by
    calc
      W = W * 1 := by ring
      _ ≤ W * W := mul_le_mul_of_nonneg_left hW hW0
      _ = W ^ 2 := by ring
  have hWsq : 9 * W ≤ 12 * W ^ 2 := by
    calc
      9 * W ≤ 12 * W := mul_le_mul_of_nonneg_right (by norm_num) hW0
      _ ≤ 12 * W ^ 2 := mul_le_mul_of_nonneg_left hWsqCore (by norm_num)
  have hcoef : 9 * W * HF * B ^ (e + 1) ≤
      12 * W ^ 2 * HF * B ^ (e + 2) := by
    calc
      9 * W * HF * B ^ (e + 1) ≤
          12 * W ^ 2 * HF * B ^ (e + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hWsq hHF0) (pow_nonneg hB0 _)
      _ ≤ 12 * W ^ 2 * HF * B ^ (e + 2) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg W)) hHF0)
  calc
    W * A * B ^ e * (3 * U + W * (4 * B) * V) ≤
        W * (3 * HF * B) * B ^ e * (3 * U + W * (4 * B) * V) := hreplace
    _ = (9 * W * HF * B ^ (e + 1)) * U +
        (12 * W ^ 2 * HF * B ^ (e + 2)) * V := by
      rw [pow_succ, show e + 2 = (e + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (12 * W ^ 2 * HF * B ^ (e + 2)) * U +
        (12 * W ^ 2 * HF * B ^ (e + 2)) * V :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hU) le_rfl
    _ = HF * (12 * W ^ 2 * B ^ (e + 2)) * (U + V) := by ring

theorem twelve_mul_le_half_of_twentyFour_mul_le_trivialBoundary
    {x y z : ℝ} (h : 24 * x * y ≤ z) :
    12 * x * y ≤ (1 / 2 : ℝ) * z := by
  calc
    12 * x * y = (1 / 2 : ℝ) * (24 * x * y) := by ring
    _ ≤ (1 / 2 : ℝ) * z := mul_le_mul_of_nonneg_left h (by norm_num)

theorem mul_rpow_of_eq_rpow_trivialBoundary_trivialBoundary
    {T Y r a : ℝ} (hT : 0 < T) (hY : Y = T ^ r) :
    T * Y ^ a = T ^ (1 + r * a) := by
  rw [hY, ← Real.rpow_mul hT.le]
  calc
    T * T ^ (r * a) = T ^ (1 : ℝ) * T ^ (r * a) := by rw [Real.rpow_one]
    _ = T ^ (1 + r * a) := (Real.rpow_add hT _ _).symm

theorem rpow_of_eq_rpow_trivialBoundary
    {T Y r a : ℝ} (hT : 0 ≤ T) (hY : Y = T ^ r) :
    Y ^ a = T ^ (r * a) := by
  rw [hY]
  exact (Real.rpow_mul hT r a).symm

theorem two_fourHundredths_absorb_into_oneHundredth_trivialBoundary
    {x target : ℝ} (h : x + 1 / 100 ≤ target) :
    1 / 400 + 1 / 400 + x ≤ target - 1 / 200 := by
  linarith

/-- **Literal lower-strip selected-cell count.**  First crossing of `T^(4/5)`, exact two-term
Montgomery cancellation, and one fixed-polylog absorption put every selected-cell fibre with
`the trivial-count boundary ≤ alpha ≤ 19/25` directly inside Route T's second alternative.  The theorem already
allows an external `T^(1/400)` multiplier for the later finite-label sum. -/
theorem eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      0 ≤ c → (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < delta → delta ≤ 2 * T →
      ∀ M : ℝ, 0 ≤ M → M ≤ T ^ (1 / 400 : ℝ) →
      ∀ (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ),
      S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      M * (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
  filter_upwards [eventually_maynardMontgomery_fibre_cost_absorbed,
    eventually_gt_atTop (1 : ℝ)] with T hcost hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaHi
    hdelta hdeltaHi M hM0 hM label S hSne hS lam hgap hband hselection
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hSne' := hSne
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hrel, _hcore, _hlabel, _husub, hbetaLo, hbetaHi,
      hlength, _hlarge, _hbranch⟩
  have hbetaLo' : mu / 120 ≤ beta := by
    simpa only [beta] using hbetaLo
  obtain ⟨ell, hell, hell90, hcross, hover, hMont⟩ :=
    exists_maynardWindowRelevantSelectedCell_fibre_tuned_montgomery_elevenFifths
      L X hT hc hmuLo hmuHi label S hSne' lam hdelta hdeltaHi hgap hband hselection
  let r : ℝ := (ell : ℝ) * beta
  let N : ℕ :=
    (groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell
  let Y : ℝ := (N : ℝ)
  let W : ℝ := maynardMontgomeryRaisedWidthConstant
  let e : ℕ := 2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
    (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
  let B0 : ℝ := 1 + Real.log (W * Y)
  let HF : ℝ := maynardHarmonicFactor K delta
  let U : ℝ := T * Y ^ (1 - 2 * alpha)
  let V : ℝ := Y ^ (2 - 2 * alpha)
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hYeq : Y = T ^ r := by
    have hAeq : (groupedDyadicLower
        (heathBrownSelectedExponent label) : ℝ) = T ^ beta := by
      simpa only [beta] using hlength
    dsimp only [Y, N, r]
    rw [Nat.cast_pow, hAeq, ← Real.rpow_natCast,
      ← Real.rpow_mul hT0.le]
    congr 1
    ring
  have hbetaHi' : beta < 1 + mu / 60 := by
    dsimp only [beta]
    nlinarith [hbetaHi]
  have hrLo : 4 / 5 ≤ r := by simpa only [r, beta] using hcross
  have hrHi : r < 4 / 5 + beta := by simpa only [r, beta] using hover
  have hrTwo : r < 2 := by
    have hbeta : beta < 311 / 300 := by linarith
    linarith
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hY1 : 1 ≤ Y := by
    simpa only [Y] using (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN1)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hYscale : Y ≤ T ^ (2 : ℕ) := by
    rw [hYeq]
    have hp := Real.rpow_le_rpow_of_exponent_le hT.le hrTwo.le
    simpa [Real.rpow_two] using hp
  have hNscale : (N : ℝ) ≤ T ^ (2 : ℕ) := by
    simpa only [Y] using hYscale
  have hW1 : 1 ≤ W := by
    simpa only [W] using maynardMontgomeryRaisedWidthConstant_one_le
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hWY1 : 1 ≤ W * Y := one_le_mul_of_one_le_of_one_le hW1 hY1
  have hB01 : 1 ≤ B0 := by
    dsimp only [B0]
    exact le_add_of_nonneg_right (Real.log_nonneg hWY1)
  have hB00 : 0 ≤ B0 := zero_le_one.trans hB01
  have hHFpos : 0 < HF := by
    simpa only [HF] using maynardHarmonicFactor_pos K hdelta
  have hHF1 : 1 ≤ HF := by
    dsimp only [HF, maynardHarmonicFactor]
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
    have hcoeff0 : 0 ≤ 12 * Real.pi / delta := by positivity
    nlinarith [mul_nonneg hcoeff0 hsum0]
  have hK1 : 1 ≤ K := by
    have hiK := Finset.mem_range.mp (hS hr0)
    omega
  have hsum1 : 1 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by
    have hzero : 0 ∈ Finset.range K := Finset.mem_range.mpr (by omega)
    have hterm0 : ∀ i ∈ Finset.range K, (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
      intro i _
      exact one_div_nonneg.mpr (by
        have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
        linarith)
    have hone := Finset.single_le_sum hterm0 hzero
    simpa only [Nat.cast_zero, zero_add, div_one] using hone
  have honeDivHF : 1 / delta ≤ HF := by
    have hpi : (1 : ℝ) ≤ 12 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hnum : (1 : ℝ) ≤ 12 * Real.pi *
        ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hsum1)]
    have hdiv : 1 / delta ≤ (12 * Real.pi / delta) *
        ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [mul_nonneg (inv_nonneg.mpr hdelta.le) (sub_nonneg.mpr hnum)]
    dsimp only [HF, maynardHarmonicFactor]
    linarith
  have hdeltaLog : 1 / delta + 2 * Real.log (W * Y) ≤ 3 * HF * B0 := by
    have hfirst : 1 / delta ≤ HF * B0 := by
      exact honeDivHF.trans (by
        calc
          HF = HF * 1 := (mul_one HF).symm
          _ ≤ HF * B0 := mul_le_mul_of_nonneg_left hB01 hHFpos.le)
    have hsecond : 2 * Real.log (W * Y) ≤ 2 * HF * B0 := by
      have hlogB : Real.log (W * Y) ≤ B0 := by
        dsimp only [B0]
        exact le_add_of_nonneg_left (by norm_num)
      have hBHF : B0 ≤ HF * B0 := by
        calc
          B0 = 1 * B0 := (one_mul B0).symm
          _ ≤ HF * B0 := mul_le_mul_of_nonneg_right hHF1 hB00
      calc
        2 * Real.log (W * Y) ≤ 2 * B0 :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
        _ ≤ 2 * (HF * B0) := mul_le_mul_of_nonneg_left hBHF (by norm_num)
        _ = 2 * HF * B0 := by ring
    calc
      1 / delta + 2 * Real.log (W * Y) ≤ HF * B0 + 2 * HF * B0 :=
        add_le_add hfirst hsecond
      _ = 3 * HF * B0 := by ring
  have heBound : e ≤ maynardMontgomeryFixedPolylogExponentBound := by
    dsimp only [e]
    exact heathBrownSelected_montgomeryFixedPolylogExponent_le label hell90
  have hraw := card_le_of_selected_montgomery_two_term_fixed_polylog_raw
    hT0 hdelta label S ell hell hell90 hMont
  have hraw' : (S.card : ℝ) ≤
      W * (1 / delta + 2 * Real.log (W * Y)) * B0 ^ e *
        (3 * U + W * (4 * B0) * V) := by
    simpa only [W, Y, N, e, B0, U, V, mul_assoc] using hraw
  have hU0 : 0 ≤ U := by
    dsimp only [U]
    exact mul_nonneg hT0.le (Real.rpow_nonneg hYpos.le _)
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    exact Real.rpow_nonneg hYpos.le _
  have hrawEnvelope : (S.card : ℝ) ≤
      HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V) := by
    exact hraw'.trans
      (montgomery_two_term_envelope_trivialBoundary hW1 hHF1 hB01 hU0 hV0 hdeltaLog)
  have hcostFull := hcost N e hN1 hNscale heBound
  have hcostHalf : 12 * W ^ 2 * B0 ^ (e + 2) ≤
      (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
    dsimp only [W, B0, Y]
    exact twelve_mul_le_half_of_twentyFour_mul_le_trivialBoundary hcostFull
  let target : ℝ := 1 + mu * (1 + routeTGapMomentNu - 2 * alpha)
  have halphaRoute : (1 + routeTGapMomentNu) / 2 ≤ alpha := halphaLo
  obtain ⟨hwidthExp, hheightExp⟩ :=
    routeT_wide_tunedMontgomery_exponents_with_polylog_le_second_elevenFifths
      hmuLo hmuHi halphaRoute halphaHi
      hbetaLo' hbetaHi' hrLo hrHi
  have hUeq : U = T ^ (1 + r * (1 - 2 * alpha)) := by
    dsimp only [U]
    exact mul_rpow_of_eq_rpow_trivialBoundary_trivialBoundary hT0 hYeq
  have hVeq : V = T ^ (r * (2 - 2 * alpha)) := by
    dsimp only [V]
    exact rpow_of_eq_rpow_trivialBoundary hT0.le hYeq
  have hUfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * U ≤
      T ^ (target - 1 / 200) := by
    rw [hUeq, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    exact two_fourHundredths_absorb_into_oneHundredth_trivialBoundary hheightExp
  have hVfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * V ≤
      T ^ (target - 1 / 200) := by
    rw [hVeq, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    exact two_fourHundredths_absorb_into_oneHundredth_trivialBoundary hwidthExp
  have hsum0 : 0 ≤ U + V := add_nonneg hU0 hV0
  calc
    M * (S.card : ℝ) ≤
        M * (HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V)) :=
      mul_le_mul_of_nonneg_left hrawEnvelope hM0
    _ ≤ T ^ (1 / 400 : ℝ) *
        (HF * ((1 / 2 : ℝ) * T ^ (1 / 400 : ℝ)) * (U + V)) := by
      have hinner0 : 0 ≤ HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V) :=
        mul_nonneg
          (mul_nonneg hHFpos.le
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg W))
              (pow_nonneg hB00 _))) hsum0
      have houter := mul_le_mul_of_nonneg_right hM hinner0
      have hinner : HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V) ≤
          HF * ((1 / 2 : ℝ) * T ^ (1 / 400 : ℝ)) * (U + V) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcostHalf hHFpos.le) hsum0
      exact houter.trans (mul_le_mul_of_nonneg_left hinner
        (Real.rpow_nonneg hT0.le _))
    _ = HF * (1 / 2 : ℝ) *
        ((T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * U) +
          (T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * V)) := by ring
    _ ≤ HF * (1 / 2 : ℝ) *
        (T ^ (target - 1 / 200) + T ^ (target - 1 / 200)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hUfinal hVfinal)
        (mul_nonneg hHFpos.le (by norm_num))
    _ = maynardHarmonicFactor K delta *
        T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
      dsimp only [HF, target]
      ring

/-- **Global lower-strip Route-T second alternative.** -/
theorem eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      0 ≤ c → (1 + routeTGapMomentNu) / 2 ≤ alpha → alpha ≤ 19 / 25 →
      0 < delta → delta ≤ 2 * T →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude_elevenFifths_trivialBoundary,
    eventually_maynardUpperSeamLabelCost_absorbed_four_hundred,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaHi hdelta hdeltaHi S hS lam hgap hband color hcolor
  classical
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - 1 / 200)
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hnlabelsPos : 0 < nlabels := by
    dsimp only [nlabels]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound_eight
    hT0 hlogT (by linarith : mu ≤ 8) (by rfl : mu / 120 = mu / 120)
      hX hL hXscale hLscale
  have hlabelRaw : nlabels ≤
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 := by
    simpa only [nlabels, maynardUpperSeamLabelPolylogConstant] using hlabel
  have hnlabels : nlabels ≤ T ^ (1 / 400 : ℝ) :=
    hlabelRaw.trans hlabelCost
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hbound : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B := by
    intro label
    let Sf : Finset ℕ := S.filter fun r => color r = label
    by_cases hSf : Sf.Nonempty
    · have hSfS : Sf ⊆ S := Finset.filter_subset _ _
      have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
      have hSfBand : ∀ r ∈ Sf, T ≤ lam r ∧ lam r ≤ 2 * T := by
        intro r hr
        exact hband r (hSfS hr)
      have hSfSelection : ∀ r ∈ Sf,
          IsMaynardWindowRelevantSelectedCell
            L X T mu N0 c (lam r) alpha label := by
        intro r hr
        have hrS := hSfS hr
        have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
        simpa only [hrcolor] using hcolor r hrS
      simpa only [Sf, B] using
        hfibre hmuLo hmuHi hc halphaLo halphaHi hdelta hdeltaHi
          nlabels hnlabelsPos.le hnlabels label Sf hSf hSfRange lam hgap
          hSfBand hSfSelection
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      simpa only [Sf, hzero, Nat.cast_zero, mul_zero] using hB0
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B := by
    rw [hcardCast, mul_sum]
    calc
      ∑ label : HeathBrownSelectionLabel L X 60,
          nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
          ∑ _label : HeathBrownSelectionLabel L X 60, B :=
        Finset.sum_le_sum fun label _ => hbound label
      _ = nlabels * B := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [B] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum


/-- At the exact transition strip, both parity fibres of a physical unit-cell family obey
the reserved second selected-cell count directly. -/
theorem eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_second_elevenFifths_trivialBoundary :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
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
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_physicalAggregate_elevenFifths_trivialBoundary,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths_trivialBoundary,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcolorT hcountT hT
  intro L X K mu N0 alpha V hX hL hXscale hLscale hmuLo hmuHi
    hlowCutoff halphaLo halphaHi hV B hB c hc hband haggregate hreserve
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
      N0 1 alpha V hlowCutoff (by norm_num) halphaLo hV S lam hbandS hmobius
        haggregateS hreserve
    exact hcountT hX hL hXscale hLscale hmuLo hmuHi (by norm_num)
      halphaLo halphaHi (by norm_num) (by linarith) S hS lam hgap hbandS
        color hcolor
  constructor
  · simpa only [S0] using count S0 hS0 lam0 hgap0 hband0 haggregate0
  · simpa only [S1] using count S1 hS1 lam1 hgap1 hband1 haggregate1

/-- The transition-strip parity counts land in Route T's second receiver after absorbing the
harmonic spacing factor into half of the fixed Montgomery reserve. -/
theorem eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_twoAlternative_elevenFifths_trivialBoundary
    (q : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 alpha V : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      (X : ℝ) / (2 ^ 120 : ℝ) ≤ N0 →
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
    eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_second_elevenFifths_trivialBoundary,
    eventually_maynardHarmonicFixedLogCost_absorbed
      (r := 1 / 400) (by norm_num) 0,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcount hcost hT
  intro L X K mu N0 alpha V hX hL hXscale hLscale hmuLo hmuHi
    hlowCutoff halphaLo halphaHi hV hK B hB c hc hband haggregate hreserve
  obtain ⟨hraw0, hraw1⟩ := hcount hX hL hXscale hLscale hmuLo hmuHi
    hlowCutoff halphaLo halphaHi hV B hB c hc hband haggregate hreserve
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


/-- Every exact physical amplitude band above the canonical trivial-count base is receiver-ready:
transition Montgomery handles the new lower strip and the existing all-amplitude capstone handles
the complementary upper strip. -/
theorem eventually_routeT_leftWindowRelevant_amplitudeBand_twoAlternative_above_trivialBoundary_elevenFifths
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
    eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_twoAlternative_elevenFifths_trivialBoundary q,
    eventually_routeT_selectedCell_physicalFixedCutoff_unitCellFamily_twoAlternative_elevenFifths q
  ] with T htransition hupper
  intro L X K mu N0 V hX hL hXL hXscale hLscale hmuLo hmuHi
    hlowCutoff hD hV
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
      (htransition hX.le hL hXscale hLscale hmuLo hmuHi hlowCutoff halphaLo halphaHi
        hV hK B hB c hc hband haggregate hreserve)
  · have halphaThreeQuarter : 3 / 4 ≤ alpha := by
      have : 19 / 25 < alpha := lt_of_not_ge halphaHi
      norm_num at this ⊢
      linarith
    simpa only [a, B, alpha] using
      (hupper hX.le hL hXL hXscale hLscale hmuLo hmuHi hlowCutoff halphaThreeQuarter
        hV hK B hB c hc hband haggregate hreserve)


end RHTower.Sieve
