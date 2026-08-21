import GaloisForLFunctions.RHTower.Sieve.MaynardSubHeightColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalMontgomery

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open Filter

/-- The actual Route-T trivial-count boundary still lies far above the sub-height
Kuzmin--Landau exclusion threshold. -/
theorem routeT_trivialCountBoundary_above_subHeight_exclusion
    {mu : ℝ} (hmu : mu ≤ 19 / 9) :
    1 - ((1 - mu / 120) * (81 / 190 : ℝ) - 1 / 100) <
      (1 + routeTGapMomentNu) / 2 := by
  have hdpos : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  dsimp only [routeTGapMomentNu]
  nlinarith

/-- Every over-height zeta/log factor lies below the aggregate threshold already at
the Route-T trivial-count boundary. -/
theorem routeT_overHeight_deficit_le_trivialCountBoundary :
    (1 - 81 / 190 : ℝ) ≤ (1 + routeTGapMomentNu) / 2 := by
  have hdpos : 0 < maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : maynardLongGlobalAmplitudeDeficit < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  dsimp only [routeTGapMomentNu]
  nlinarith

/-- Sub-height mass selection remains unconditional throughout the complete transition strip
beginning at the exact trivial-count boundary. -/
theorem eventually_maynard_perronRelevant_box_subHeight_mass_to_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
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
          mu / 120 ≤ ∑ i ∈ (Finset.univ.filter
              fun i : PositiveHeathBrownBoxFactorIndex box =>
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) := by
  filter_upwards [eventually_maynard_overHeight_zeta_amplitude_deficit,
    eventually_maynard_overHeight_log_amplitude_deficit,
    eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le
      (by norm_num : (0 : ℝ) < 1 / 9000),
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hslack hT
  intro X hX mu hmuLo hmuHi hXscale L hL box helig hmobius
    c y alpha hc hylo hyhi halpha hlarge
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  have hqlog : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa [s] using hlarge)
  let Z : HeathBrownBoxFactorIndex 60 box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X 60 box s i
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
  have hprodZ : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s := by
    simpa [Z, heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
      L X 60 box.m box.a box.b box.q s
  have hfactorPos : ∀ i : HeathBrownBoxFactorIndex 60 box.m, 0 < ‖Z i‖ := by
    intro i
    have hZi : Z i ≠ 0 := by
      intro hzero
      have hpzero : ∏ j, Z j = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      rw [hprodZ] at hpzero
      rw [hpzero, norm_zero] at hcorePos
      exact (lt_irrefl 0) hcorePos
    exact norm_pos_iff.mpr hZi
  have hover : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤
        1 - 81 / 190 := by
    intro i hi
    let qi : ℕ := heathBrownBoxFactorExponent box.a box.b box.q i
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
    have hV : 0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
      simpa [Z] using hfactorPos i
    rcases hkind with hkind | hkind
    · have hz := hzeta X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hz (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
    · have hl := hlogFactor X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hl (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
  let total : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have htotal : mu / 120 ≤ total := by
    simpa [IsHeathBrownBoxEligible, total] using helig
  have htotalMin : (1 / 90 : ℝ) ≤ total := by linarith
  have hD : D = T ^ total := by
    dsimp [D, total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent hT
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex 60 box.m)))
  have hlogD : Real.log D = total * Real.log T := by
    rw [hD, Real.log_rpow (lt_trans zero_lt_one hT)]
  have hlogT0 : 0 ≤ Real.log T := (Real.log_pos hT).le
  have hslackRaw := hslack X hX mu hmuHi hXscale L 60 box hqlog
  have hslackMass :
      ∑ i : HeathBrownBoxFactorIndex 60 box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        (1 / 100 : ℝ) * Real.log D := by
    calc
      _ ≤ (1 / 9000 : ℝ) * Real.log T := hslackRaw
      _ ≤ (1 / 100 : ℝ) * (total * Real.log T) := by
        have hmul := mul_le_mul_of_nonneg_right htotalMin hlogT0
        nlinarith
      _ = (1 / 100 : ℝ) * Real.log D := by rw [hlogD]
  have htotalPositive : mu / 120 ≤
      ∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) := by
    rw [sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    exact htotal
  apply maynard_heathBrownBox_subHeight_mass
    (Delta := (81 / 190 : ℝ)) (E := (1 / 100 : ℝ)) box hL hX hT
    (by linarith : 0 < mu / 120) hc htotalPositive
    (by norm_num : (0 : ℝ) ≤ 81 / 190) (by simpa [s] using hover)
    (by simpa [D] using hslackMass) hlarge
  exact (routeT_trivialCountBoundary_above_subHeight_exclusion hmuHi).trans_le halpha

/-- The multiplicative over-height excision law also starts at the exact trivial-count boundary. -/
theorem eventually_maynard_perronRelevant_box_overHeight_small_to_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ box : HeathBrownBoxChoice L X 60,
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
  filter_upwards [eventually_maynard_overHeight_zeta_amplitude_deficit,
    eventually_maynard_overHeight_log_amplitude_deficit,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hzeta hlogFactor hT
  intro X hX mu hmuHi hXscale L hL box hmobius
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
  have hamp : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤ 1 - 81 / 190 := by
    rcases hkind with hkind | hkind
    · have hz := hzeta X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hz (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
    · have hl := hlogFactor X hX mu hmuHi hXscale qi
        (by simpa [qi] using hqiX) c y hc hylo hyhi
        (by simpa [qi] using hTN)
      simpa [s, qi, heathBrownBoxFactorValue, heathBrownFactorBase, hkind] using
        hl (by simpa [s, qi, heathBrownBoxFactorValue,
          heathBrownFactorBase, hkind] using hV)
  have hN : (1 : ℝ) < (((2 ^ qi : ℕ) : ℝ)) := by
    exact_mod_cast (show 1 < 2 ^ qi by
      exact pow_lt_pow_right₀ (by norm_num) i.property)
  have hampAlpha : maynardAmplitude c (((2 ^ qi : ℕ) : ℝ))
      ‖heathBrownBoxFactorValue L X 60 box s i‖ ≤ alpha := by
    exact hamp.trans (routeT_overHeight_deficit_le_trivialCountBoundary.trans halpha)
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

/-- Every aggregate value in the transition strip selects one literal sub-height group; no
special role is played by the historical `3/4` wrapper boundary. -/
theorem eventually_exists_windowRelevant_subHeight_group_to_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L →
        ∀ c y alpha V N0 : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          (1 + routeTGapMomentNu) / 2 ≤ alpha → 0 < V →
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
          ∃ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box ∧
            IsHeathBrownBoxWindowRelevant N0 X 60 box ∧
            (groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ^
                (alpha - c) ≤
              ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
            ∃ u : Finset (HeathBrownBoxFactorIndex 60 box.m), u.Nonempty ∧
              (∀ i ∈ u,
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) ∧
              let beta := ∑ i ∈ u,
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q i)
              mu / 120 ≤ beta ∧ beta < 1 + 2 * (mu / 120) ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} =>
                    heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) =
                    T ^ beta ∧
                ((groupedDyadicLower
                  (fun i : {i // i ∈ u} =>
                    heathBrownBoxFactorExponent box.a box.b box.q i) : ℕ) : ℝ) ^
                      (alpha - c) ≤
                  ‖∏ i : {i // i ∈ u}, LSeries
                    (complexCoeff (arithmeticDyadicBlock
                      (heathBrownFactorBase L X
                        (heathBrownBoxFactorKind 60 box.m i))
                      (heathBrownBoxFactorExponent box.a box.b box.q i)))
                        ((c : ℂ) + (y : ℝ) * Complex.I)‖ ∧
                (∃ j ∈ u, beta - 2 * (mu / 120) < dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ∧
                (beta < 1 ∨ ∃ j ∈ u,
                  (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
                    heathBrownBoxFactorKind 60 box.m j = .log) ∧
                  1 - 2 * (mu / 120) < dyadicLogExponent T
                    (heathBrownBoxFactorExponent box.a box.b box.q j)) := by
  filter_upwards [
    eventually_maynard_perronRelevant_box_subHeight_mass_to_trivialBoundary,
    eventually_maynard_perronRelevant_box_overHeight_small_to_trivialBoundary,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hmassT hsmallT hT
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyhi
    halpha hV hmobius haggregate hreserve
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
  have hmass := hmassT X hX mu hmuLo hmuHi hXscale L hL box helig
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  have hsmall := hsmallT X hX mu hmuHi hXscale L hL box
    (hmobius box) c y alpha hc hylo hyhi halpha hcore
  obtain ⟨u, hune, husub, hulower, huupper, hulength, hularge,
      hulocal, huwitness⟩ :=
    exists_heathBrown_box_subHeight_group_of_mass
      L X 60 box hL hX hT
        (by linarith : 0 < mu / 120)
        ((c : ℂ) + (y : ℝ) * Complex.I) hmass hsmall hcore
  have huwitness' :
      (∑ i ∈ u, dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)) < 1 ∨
        ∃ j ∈ u,
          (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
            heathBrownBoxFactorKind 60 box.m j = .log) ∧
          1 - 2 * (mu / 120) < dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q j) := by
    rcases huwitness with hregular | ⟨j, hju, hjweight⟩
    · exact Or.inl hregular
    · right
      refine ⟨j, hju, ?_, hjweight⟩
      cases hkind : heathBrownBoxFactorKind 60 box.m j with
      | moebius =>
          have hjupper := hmobius box j hkind
          exfalso
          linarith
      | zeta => exact Or.inl rfl
      | log => exact Or.inr rfl
  exact ⟨box, helig, hrel, hcore, u, hune, husub, hulower, huupper,
    hulength, hularge, hulocal, huwitness'⟩

/-- Complete selected-cell extraction extends to the exact Route-T transition boundary. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_label_to_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ c y alpha V N0 : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          (1 + routeTGapMomentNu) / 2 ≤ alpha → 0 < V →
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
            IsMaynardWindowRelevantSelectedCell L X T mu N0 c y alpha label := by
  filter_upwards [eventually_exists_windowRelevant_subHeight_group_to_trivialBoundary,
    eventually_maynard_perronRelevant_moderate_global_amplitude_le_997,
    eventually_maynard_perronRelevant_overweight_global_amplitude_le_nineEightyThree_div_thousand]
      with T hselect hmoderate hoverweight
  intro X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
    halpha hV hmobius haggregate hreserve
  obtain ⟨box, helig, hrel, hcore, u, hune, husub, hbetaLo, hbetaHi,
      hlength, hlarge, hlocal, hheight⟩ :=
    hselect X hX mu hmuLo hmuHi hXscale L hL c y alpha V N0 hc hylo hyupper
      halpha hV hmobius haggregate hreserve
  let beta := ∑ i ∈ u, dyadicLogExponent T
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
        have hjupper := hmobius box j hkind
        exfalso
        dsimp only [beta] at hbeta
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
    by_cases hsmall : beta ≤ 5 / 12
    · exact Or.inl hsmall
    · have hbeta : 5 / 12 < beta := lt_of_not_ge hsmall
      by_cases hregular : beta < 1
      · obtain ⟨j, hju, hkind, hjweight⟩ := hlocalKind hbeta
        have halpha997 := hmoderate X hX mu hmuLo hmuHi hXscale L hL 60 box
          helig hrel.1 c y alpha beta hc hylo hyupper hbeta j hkind hjweight hcore
        exact Or.inr (Or.inl
          ⟨hbeta, hregular, halpha997, j, hju, hkind, hjweight⟩)
      · have hbetaOne : 1 ≤ beta := le_of_not_gt hregular
        rcases hheight with hfalse | ⟨j, hju, hkind, hjweight⟩
        · exact (hregular hfalse).elim
        · have halpha983 := hoverweight X hX mu hmuLo hmuHi hXscale L hL 60 box
            helig hrel.1 c y alpha hc hylo hyupper j hkind hjweight hcore
          exact Or.inr (Or.inr
            ⟨hbetaOne, halpha983, j, hju, hkind, hjweight⟩)
  let label : HeathBrownSelectionLabel L X 60 := ⟨box, u⟩
  refine ⟨label, ?_⟩
  dsimp only [IsMaynardWindowRelevantSelectedCell]
  refine ⟨helig, hrel, hcore, hune, husub, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [maynardSubHeightSelectedExponent, label, beta] using hbetaLo
  · simpa [maynardSubHeightSelectedExponent, label, beta] using hbetaHi
  · simpa [maynardSubHeightSelectedExponent, label,
      heathBrownSelectedExponent, beta] using hlength
  · simpa [label, heathBrownSelectedExponent, heathBrownSelectedKind,
      HeathBrownSelectedFactor] using hlarge
  · simpa [IsMaynardSelectedCellBranch, maynardSubHeightSelectedExponent,
      label, beta] using hbranch

/-- Uniform selected-cell coloring throughout the exact transition strip. -/
theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_to_trivialBoundary :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu → ∀ L : ℕ, 1 ≤ L →
        ∀ c alpha V N0 : ℝ, 0 ≤ c →
          (1 + routeTGapMomentNu) / 2 ≤ alpha → 0 < V →
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
    eventually_exists_maynardWindowRelevantSelectedCell_label_to_trivialBoundary]
      with T hpoint
  intro X hX mu hmuLo hmuHi hXscale L hL c alpha V N0 hc halpha hV
    S y hy hmobius haggregate hreserve
  classical
  have hchoose : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        IsMaynardWindowRelevantSelectedCell
          L X T mu N0 c (y r) alpha label := by
    intro r hr
    exact hpoint X hX mu hmuLo hmuHi hXscale L hL c (y r) alpha V N0 hc
      (hy r hr).1 (hy r hr).2 halpha hV hmobius (haggregate r hr) hreserve
  choose selected hselected using hchoose
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

private theorem routeT_transition_harmonic_log_envelope
    {K : ℕ} {delta W Y : ℝ}
    (hdelta : 0 < delta) (hK : 1 ≤ K) (hW : 1 ≤ W) (hY : 1 ≤ Y) :
    1 / delta + 2 * Real.log (W * Y) ≤
      3 * maynardHarmonicFactor K delta * (1 + Real.log (W * Y)) := by
  let H : ℝ := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let HF : ℝ := maynardHarmonicFactor K delta
  let B : ℝ := 1 + Real.log (W * Y)
  have hWY : 1 ≤ W * Y := one_le_mul_of_one_le_of_one_le hW hY
  have hlog : 0 ≤ Real.log (W * Y) := Real.log_nonneg hWY
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hH : 1 ≤ H := by
    have hzero : 0 ∈ Finset.range K := Finset.mem_range.mpr hK
    have hterm : ∀ i ∈ Finset.range K, (0 : ℝ) ≤ 1 / ((i : ℝ) + 1) := by
      intro i _
      exact one_div_nonneg.mpr (by positivity)
    have hone := Finset.single_le_sum hterm hzero
    simpa only [H, Nat.cast_zero, zero_add, div_one] using hone
  have hHFpos : 0 < HF := by
    simpa only [HF] using maynardHarmonicFactor_pos K hdelta
  have hHF : 1 ≤ HF := by
    have hcoeff : 0 ≤ 12 * Real.pi / delta := by positivity
    have htail : 0 ≤ (12 * Real.pi / delta) * H :=
      mul_nonneg hcoeff (zero_le_one.trans hH)
    simpa only [HF, maynardHarmonicFactor, H] using
      (show (1 : ℝ) ≤ 1 + (12 * Real.pi / delta) * H from
        le_add_of_nonneg_right htail)
  have honeDiv : 1 / delta ≤ HF := by
    have hpi : (1 : ℝ) ≤ 12 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hnum : (1 : ℝ) ≤ 12 * Real.pi * H := by
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 12 * Real.pi * H := mul_le_mul hpi hH (by norm_num) (by positivity)
    have hdiv : 1 / delta ≤ (12 * Real.pi / delta) * H := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        1 * delta⁻¹ ≤ (12 * Real.pi * H) * delta⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hdelta.le)
        _ = 12 * Real.pi * delta⁻¹ * H := by ring
    dsimp only [HF, maynardHarmonicFactor, H]
    linarith
  have hfirst : 1 / delta ≤ HF * B := by
    exact honeDiv.trans (by
      calc
        HF = HF * 1 := by ring
        _ ≤ HF * B := mul_le_mul_of_nonneg_left hB hHFpos.le)
  have hsecond : 2 * Real.log (W * Y) ≤ 2 * HF * B := by
    have hlogB : Real.log (W * Y) ≤ B := by dsimp only [B]; linarith
    have hlogHF : Real.log (W * Y) ≤ HF * B := hlogB.trans (by
      calc
        B = 1 * B := by ring
        _ ≤ HF * B := mul_le_mul_of_nonneg_right hHF (zero_le_one.trans hB))
    linarith
  dsimp only [HF, B] at hfirst hsecond ⊢
  linarith

private theorem routeT_transition_montgomery_raw_envelope
    {K e : ℕ} {delta W B U V A : ℝ}
    (hdelta : 0 < delta) (hW : 1 ≤ W) (hB : 1 ≤ B)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hlog : 1 / delta + 2 * (B - 1) ≤
      3 * maynardHarmonicFactor K delta * B)
    (hraw : A ≤ W * (1 / delta + 2 * (B - 1)) * B ^ e *
      (3 * U + W * (4 * B) * V)) :
    A ≤ maynardHarmonicFactor K delta *
      (12 * W ^ 2 * B ^ (e + 2)) * (U + V) := by
  let HF : ℝ := maynardHarmonicFactor K delta
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hHF0 : 0 ≤ HF := (maynardHarmonicFactor_pos K hdelta).le
  have htail : 0 ≤ 3 * U + W * (4 * B) * V :=
    add_nonneg (mul_nonneg (by norm_num) hU)
      (mul_nonneg (mul_nonneg hW0 (mul_nonneg (by norm_num) hB0)) hV)
  have hreplace :
      W * (1 / delta + 2 * (B - 1)) * B ^ e *
          (3 * U + W * (4 * B) * V) ≤
        W * (3 * HF * B) * B ^ e *
          (3 * U + W * (4 * B) * V) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog hW0) (pow_nonneg hB0 e)) htail
  have hpow : B ^ (e + 1) ≤ B ^ (e + 2) :=
    pow_le_pow_right₀ hB (by omega)
  have hWsq : 9 * W ≤ 12 * W ^ 2 := by
    have hcore : W ≤ W ^ 2 := by
      calc
        W = W * 1 := by ring
        _ ≤ W * W := mul_le_mul_of_nonneg_left hW hW0
        _ = W ^ 2 := by ring
    calc
      9 * W ≤ 12 * W := mul_le_mul_of_nonneg_right (by norm_num) hW0
      _ ≤ 12 * W ^ 2 := mul_le_mul_of_nonneg_left hcore (by norm_num)
  have hcoef : 9 * W * HF * B ^ (e + 1) ≤
      12 * W ^ 2 * HF * B ^ (e + 2) := by
    calc
      9 * W * HF * B ^ (e + 1) ≤ 12 * W ^ 2 * HF * B ^ (e + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hWsq hHF0) (pow_nonneg hB0 _)
      _ ≤ 12 * W ^ 2 * HF * B ^ (e + 2) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg W)) hHF0)
  calc
    A ≤ W * (1 / delta + 2 * (B - 1)) * B ^ e *
        (3 * U + W * (4 * B) * V) := hraw
    _ ≤ W * (3 * HF * B) * B ^ e *
        (3 * U + W * (4 * B) * V) := hreplace
    _ = (9 * W * HF * B ^ (e + 1)) * U +
        (12 * W ^ 2 * HF * B ^ (e + 2)) * V := by
      rw [pow_succ, show e + 2 = (e + 1) + 1 by omega, pow_succ]
      ring
    _ ≤ (12 * W ^ 2 * HF * B ^ (e + 2)) * U +
        (12 * W ^ 2 * HF * B ^ (e + 2)) * V :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef hU) le_rfl
    _ = maynardHarmonicFactor K delta *
        (12 * W ^ 2 * B ^ (e + 2)) * (U + V) := by
      dsimp only [HF]
      ring

private theorem routeT_transition_scaled_envelope_to_second
    {K : ℕ} {delta T M A C U V target : ℝ}
    (hT : 0 < T) (hdelta : 0 < delta) (hM0 : 0 ≤ M)
    (hM : M ≤ T ^ (1 / 400 : ℝ))
    (hA : A ≤ maynardHarmonicFactor K delta * C * (U + V))
    (hC0 : 0 ≤ C) (hC : C ≤ (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ))
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hUfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * U ≤
      T ^ (target - 1 / 200))
    (hVfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * V ≤
      T ^ (target - 1 / 200)) :
    M * A ≤ maynardHarmonicFactor K delta * T ^ (target - 1 / 200) := by
  let HF : ℝ := maynardHarmonicFactor K delta
  have hHF0 : 0 ≤ HF := (maynardHarmonicFactor_pos K hdelta).le
  have hsum : 0 ≤ U + V := add_nonneg hU hV
  calc
    M * A ≤ M * (HF * C * (U + V)) := mul_le_mul_of_nonneg_left hA hM0
    _ ≤ T ^ (1 / 400 : ℝ) *
        (HF * ((1 / 2 : ℝ) * T ^ (1 / 400 : ℝ)) * (U + V)) := by
      have hinner0 : 0 ≤ HF * C * (U + V) :=
        mul_nonneg (mul_nonneg hHF0 hC0) hsum
      have houter := mul_le_mul_of_nonneg_right hM hinner0
      have hinner : HF * C * (U + V) ≤
          HF * ((1 / 2 : ℝ) * T ^ (1 / 400 : ℝ)) * (U + V) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC hHF0) hsum
      exact houter.trans
        (mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hT.le _))
    _ = HF * (1 / 2 : ℝ) *
        ((T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * U) +
          (T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * V)) := by ring
    _ ≤ HF * (1 / 2 : ℝ) *
        (T ^ (target - 1 / 200) + T ^ (target - 1 / 200)) :=
      mul_le_mul_of_nonneg_left (add_le_add hUfinal hVfinal)
        (mul_nonneg hHF0 (by norm_num))
    _ = maynardHarmonicFactor K delta * T ^ (target - 1 / 200) := by
      dsimp only [HF]
      ring

/-- Tuned Montgomery reaches the second receiver on the entire nontrivial transition strip,
including amplitudes strictly below `3/4`. -/
theorem eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_transition :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
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
    Filter.eventually_gt_atTop (1 : ℝ)] with T hcost hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaHi
    hdelta hdeltaHi M hM0 hM label S hSne hS lam hgap hband hselection
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hSne' := hSne
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hrel, _hcore, _hlabel, _husub, hbetaLo, hbetaHi,
      hlength, _hlarge, _hbranch⟩
  obtain ⟨ell, hell, hell90, hcross, hover, hMont⟩ :=
    exists_maynardWindowRelevantSelectedCell_fibre_tuned_montgomery
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
    have hbeta : beta < 559 / 540 := by linarith
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
  have hWY1 : 1 ≤ W * Y := one_le_mul_of_one_le_of_one_le hW1 hY1
  have hB01 : 1 ≤ B0 := by
    dsimp only [B0]
    linarith [Real.log_nonneg hWY1]
  have hK1 : 1 ≤ K := by
    have hiK := Finset.mem_range.mp (hS hr0)
    omega
  have hdeltaLog : 1 / delta + 2 * (B0 - 1) ≤ 3 * HF * B0 := by
    simpa only [B0, add_sub_cancel_left, HF] using
      routeT_transition_harmonic_log_envelope hdelta hK1 hW1 hY1
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
    positivity
  have hV0 : 0 ≤ V := by
    dsimp only [V]
    positivity
  have hrawEnvelope : (S.card : ℝ) ≤
      HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V) := by
    apply routeT_transition_montgomery_raw_envelope hdelta hW1 hB01 hU0 hV0 hdeltaLog
    simpa only [B0, add_sub_cancel_left] using hraw'
  have hcostFull := hcost N e hN1 hNscale heBound
  have hcostHalf : 12 * W ^ 2 * B0 ^ (e + 2) ≤
      (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
    simpa only [W, B0, Y] using (show
      12 * maynardMontgomeryRaisedWidthConstant ^ 2 *
          (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^
            (e + 2) ≤
        (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) by nlinarith [hcostFull])
  let target : ℝ := 1 + mu * (1 + routeTGapMomentNu - 2 * alpha)
  obtain ⟨hwidthExp, hheightExp⟩ :=
    routeT_wide_tunedMontgomery_exponents_with_polylog_le_second
      hmuLo hmuHi halphaLo halphaHi
      (by simpa only [beta] using hbetaLo) hbetaHi' hrLo hrHi
  have hUeq : U = T ^ (1 + r * (1 - 2 * alpha)) := by
    have hYpow : Y ^ (1 - 2 * alpha) = T ^ (r * (1 - 2 * alpha)) := by
      calc
        Y ^ (1 - 2 * alpha) = (T ^ r) ^ (1 - 2 * alpha) := by rw [hYeq]
        _ = T ^ (r * (1 - 2 * alpha)) :=
          (Real.rpow_mul hT0.le r (1 - 2 * alpha)).symm
    calc
      U = T * Y ^ (1 - 2 * alpha) := by rfl
      _ = T * T ^ (r * (1 - 2 * alpha)) := by rw [hYpow]
      _ = T ^ (1 : ℝ) * T ^ (r * (1 - 2 * alpha)) := by rw [Real.rpow_one]
      _ = T ^ (1 + r * (1 - 2 * alpha)) := (Real.rpow_add hT0 _ _).symm
  have hVeq : V = T ^ (r * (2 - 2 * alpha)) := by
    have hYpow : Y ^ (2 - 2 * alpha) = T ^ (r * (2 - 2 * alpha)) := by
      calc
        Y ^ (2 - 2 * alpha) = (T ^ r) ^ (2 - 2 * alpha) := by rw [hYeq]
        _ = T ^ (r * (2 - 2 * alpha)) :=
          (Real.rpow_mul hT0.le r (2 - 2 * alpha)).symm
    calc
      V = Y ^ (2 - 2 * alpha) := by rfl
      _ = T ^ (r * (2 - 2 * alpha)) := hYpow
  have hbudget : (1 / 400 : ℝ) + 1 / 400 ≤ 1 / 100 := by norm_num
  have hUfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * U ≤
      T ^ (target - 1 / 200) := by
    rw [hUeq, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    dsimp only [target]
    linarith
  have hVfinal : T ^ (1 / 400 : ℝ) * T ^ (1 / 400 : ℝ) * V ≤
      T ^ (target - 1 / 200) := by
    rw [hVeq, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    dsimp only [target]
    linarith
  simpa only [HF, target] using
    routeT_transition_scaled_envelope_to_second hT0 hdelta hM0 hM hrawEnvelope
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg W))
        (pow_nonneg (zero_le_one.trans hB01) _))
      hcostHalf hU0 hV0 hUfinal hVfinal

/-- Finite selected-label entropy can be paid throughout the transition strip, so the
fibrewise Montgomery estimate globalizes at the exact trivial-count boundary. -/
theorem eventually_card_le_maynard_second_of_selected_cell_coloring_transition :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
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
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_transition,
    eventually_maynardLabelCost_absorbed_four_hundred,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
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
  have hlabel := heathBrownSelectionLabel_sixty_polylog_bound
    hT0 hlogT hmuHi (by rfl : mu / 120 = mu / 120)
      hX hL hXscale hLscale
  have hlabelRaw : nlabels ≤
      maynardLabelPolylogConstant * (Real.log T) ^ 120 := by
    simpa only [nlabels, maynardLabelPolylogConstant] using hlabel
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

end RHTower.Sieve
