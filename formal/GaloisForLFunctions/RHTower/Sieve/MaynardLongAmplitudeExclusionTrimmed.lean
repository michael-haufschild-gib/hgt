import GaloisForLFunctions.RHTower.Sieve.MaynardLongAmplitudeExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardTrimmedAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MaynardPerronRelevantAggregate

/-!
# Long-factor exclusion without exponent-positivity premise

The exact positive-length recut removes unit atoms before amplitude averaging.  The long-factor
branch therefore applies to every literal Perron-relevant box selected from the aggregate.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Fixed global deficit after exact removal of all length-one atoms. -/
theorem maynard_heathBrownBox_long_factor_global_deficit_trimmed
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (hL : 1 ≤ L) (hX : 1 ≤ X)
    {c y alpha : ℝ} (hc : 0 ≤ c)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hjpos : 1 ≤ heathBrownBoxFactorExponent box.a box.b box.q j)
    (hj : maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X k box
            ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
      1 - maynardDerivativeDeficit 47 / 2)
    (hlength :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
          (1 / 95 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        (maynardDerivativeDeficit 47 / 380) *
          Real.log
            ((groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    alpha ≤ 1 - maynardDerivativeDeficit 47 / 380 := by
  have hDelta : 0 ≤ maynardDerivativeDeficit 47 / 2 := by
    dsimp [maynardDerivativeDeficit]
    positivity
  have h := maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    box hL hX hc hDelta j hjpos hj hlength hslackMass hlarge
  convert h using 1
  dsimp [maynardDerivativeDeficit]
  ring

/-- **Ready long-factor capstone with no all-positive-exponents hypothesis.** -/
theorem maynard_heathBrownBox_long_factor_global_deficit_of_ready_trimmed
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {T t mu c y alpha : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hL : 1 ≤ L) (hX : 1 ≤ X)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hlong : 2 * t < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : 2 * Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      maynardDerivativeDeficit 47 *
        Real.log
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        maynardLongGlobalAmplitudeDeficit *
          Real.log
            ((groupedDyadicLower
              (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit := by
  classical
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qj := heathBrownBoxFactorExponent box.a box.b box.q j
  have hNbase : T ^ (1 / 45 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) :=
    dyadic_length_ge_fortyFive_root_of_maynard_long hready.1 hmu_lo ht hlong
  have hroot1 : 1 < T ^ (1 / 45 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 1 / 45)
  have hjpos : 1 ≤ qj := by
    by_contra hnot
    have hqj : qj = 0 := by omega
    have : (1 : ℝ) < 1 := by
      simpa [hqj] using hroot1.trans_le hNbase
    linarith
  let Z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X k box s i
  have hD0 : 0 <
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 <
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
            (alpha - c) := Real.rpow_pos_of_pos hD0 _
    exact hthreshold.trans_le (by simpa [s] using hlarge)
  have hprodZ : (∏ i, Z i) =
      heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s := by
    simpa [Z, heathBrownBoxFactorValue] using heathBrownBoxFactorProduct_eq_core
      L X k box.m box.a box.b box.q s
  have hZj : Z j ≠ 0 := by
    intro hzero
    have hpzero : ∏ i, Z i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hzero
    rw [hprodZ] at hpzero
    rw [hpzero, norm_zero] at hcorePos
    exact (lt_irrefl 0) hcorePos
  have hV : 0 < ‖heathBrownBoxFactorValue L X k box s j‖ := by
    exact norm_pos_iff.mpr (by simpa [Z] using hZj)
  have hj := maynard_heathBrown_long_factor_amplitude_le_one_sub_half
    box j hkind hX hready hmu_lo hmu_hi ht hXscale hc hylo hyupper hlong hsize
      (by simpa [s] using hV)
  have hlength := maynard_long_heathBrownBox_factor_relative_length
    box j hready.1 hmu_lo hmu_hi ht hXscale hcoreX hlong
  have hglobal := maynard_heathBrownBox_long_factor_global_deficit_trimmed
    box hL hX hc j (by simpa [qj] using hjpos) (by simpa [s] using hj) hlength
      (by simpa [maynardLongGlobalAmplitudeDeficit] using hslackMass) hlarge
  simpa [maynardLongGlobalAmplitudeDeficit] using hglobal

/-- **Uniform eventual Route-T long-factor exclusion.**  Eligibility and Perron relevance now
discharge all scalar, support, slack, and positivity conditions internally. -/
theorem eventually_maynard_perronRelevant_eligible_long_factor_global_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L → ∀ k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          IsHeathBrownBoxEligible L X k T (mu / 120) box →
          IsHeathBrownBoxPerronRelevant X k box →
          ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
            ∀ j : HeathBrownBoxFactorIndex k box.m,
              (heathBrownBoxFactorKind k box.m j = .zeta ∨
                heathBrownBoxFactorKind k box.m j = .log) →
              2 * (mu / 120) < dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
              ((groupedDyadicLower
                (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                  (alpha - c) ≤
                ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
              alpha ≤ 1 - maynardLongGlobalAmplitudeDeficit := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_maynard_long_box_amplitude_slack_ready,
    eventually_maynard_long_factor_amplitude_half_deficit_ready]
      with T hready hslack hsize
  intro X hX mu hmu_lo hmu_hi hXscale L hL k box helig hrel
    c y alpha hc hylo hyupper j hkind hlong hlarge
  have hq : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box
      ((c : ℂ) + (y : ℝ) * Complex.I) hlarge
  have hslackMass := hslack X hX mu hmu_lo hmu_hi hXscale L k box hq helig
  have hsize' := hsize X hX mu hmu_lo hmu_hi hXscale L k box j hkind hlong
  exact maynard_heathBrownBox_long_factor_global_deficit_of_ready_trimmed
    box hready hmu_lo hmu_hi rfl hL hX hXscale hc hylo hyupper
      (perronRelevant_heathBrownBox_coreLower_le hrel) j hkind hlong hsize'
      hslackMass hlarge

end RHTower.Sieve
