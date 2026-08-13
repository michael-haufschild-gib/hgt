import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightCountExponents
import GaloisForLFunctions.RHTower.Sieve.MaynardSubHeightColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardLongAmplitudeExclusionTrimmed

/-!
# Adaptive order-three exclusion for overweight selected cells

Witnessed greedy packing shows that every selected cell of exponent at least one contains a
zeta/log atom of exponent greater than `1-mu/60`.  Such an atom is almost height-sized, so the
third derivative test already supplies a local `1/24` power saving.  This is much stronger than
the uniform order-47 deficit used for merely long atoms.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem dyadic_length_ge_twentySixTwentySeven_root_of_overweight
    {T mu : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9) {q : ℕ}
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T q) :
    T ^ (26 / 27 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
  have hexp : (26 / 27 : ℝ) ≤ dyadicLogExponent T q := by
    linarith
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT).monotone hexp
  rwa [rpow_dyadicLogExponent hT q] at hpow

theorem maynard_overweight_orderThree_factorial
    {T mu : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9) {q : ℕ}
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T q) :
    Nat.factorial ((3 : ℕ) - 1) ≤ 2 ^ q := by
  have hpositive : 0 < dyadicLogExponent T q := by linarith
  have hq : 1 ≤ q := by
    by_contra hnot
    have hq0 : q = 0 := by omega
    subst q
    simp [dyadicLogExponent, Real.logb] at hpositive
  norm_num
  calc
    2 = 2 ^ (1 : ℕ) := by norm_num
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq

theorem maynard_overweight_orderThree_high_window
    {T mu y : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9) {q : ℕ}
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T q)
    (hy : y ≤ 2 * T) :
    y ≤ 2 * Real.pi * 2 ^ (3 : ℕ) *
      (((2 ^ q : ℕ) : ℝ)) ^ ((3 : ℕ) - 1) *
      (((2 ^ q : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hNroot : T ^ (26 / 27 : ℝ) ≤ N :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight hT hmuHi hover
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
    hNroot (by norm_num : (0 : ℝ) ≤ 5 / 3)
  have hleft : (T ^ (26 / 27 : ℝ)) ^ (5 / 3 : ℝ) =
      T ^ (130 / 81 : ℝ) := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  rw [hleft] at hraise
  have hTpow : T ≤ T ^ (130 / 81 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le
      (by norm_num : (1 : ℝ) ≤ 130 / 81)
    simpa using hpow
  have hTN : T ≤ N ^ (5 / 3 : ℝ) := hTpow.trans hraise
  have hshape : N ^ ((3 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ) =
      N ^ (5 / 3 : ℝ) := by
    norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
    norm_num
  change y ≤ 2 * Real.pi * 2 ^ (3 : ℕ) *
    N ^ ((3 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ)
  have hconstant : (2 : ℝ) ≤ 2 * Real.pi * 2 ^ (3 : ℕ) := by
    nlinarith [Real.pi_gt_three]
  calc
    y ≤ 2 * T := hy
    _ ≤ 2 * N ^ (5 / 3 : ℝ) := mul_le_mul_of_nonneg_left hTN (by norm_num)
    _ ≤ (2 * Real.pi * 2 ^ (3 : ℕ)) * N ^ (5 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hN0.le _)
    _ = (2 * Real.pi * 2 ^ (3 : ℕ)) *
        (N ^ ((3 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ)) := by rw [hshape]
    _ = 2 * Real.pi * 2 ^ (3 : ℕ) * N ^ ((3 : ℕ) - 1) *
        N ^ (-(1 / 3) : ℝ) := by ring

/-- Pointwise amplitude deficit for the near-height witness of an overweight cell.  Eventual
constant absorption retains `1/25` of the raw order-three `1/24` saving. -/
theorem maynard_heathBrown_overweight_factor_amplitude_le_twentyFour_div_twentyFive
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) {T mu c y : ℝ}
    (hready : IsMaynardLongScaleReady T) (hmuHi : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      (1 / 600 : ℝ) * Real.log
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hV : 0 < ‖heathBrownBoxFactorValue L X k box
      ((c : ℂ) + (y : ℝ) * Complex.I) j‖) :
    maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤ 24 / 25 := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j) q
  have hNbase := dyadic_length_ge_twentySixTwentySeven_root_of_overweight
    hready.1 hmuHi hover
  have hroot1 : 1 < T ^ (26 / 27 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 26 / 27)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 1 ≤ C := by
    dsimp [C, q]
    exact one_le_heathBrownDerivativeConstant_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_overweight_orderThree_factorial hready.1 hmuHi hover
  have hlow := maynard_zeta_log_factor_low_window
    box j hkind hX hready.1 hmuHi hXscale hylo hready.2.1
  have hhigh := maynard_overweight_orderThree_high_window
    hready.1 hmuHi hover hyupper
  have hy0 : 0 < y := lt_trans zero_lt_one (hready.1.trans_le hylo)
  have hqX := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hupper := norm_heathBrownBoxFactorValue_le_derivative_defect
    L X k box j hkind hX hc hy0 (k₀ := 3) (by norm_num) hqX hfac hlow hhigh
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    hN hV hCpos (by simpa [N, C, q] using hupper)
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hratio : Real.log C / Real.log N ≤ (1 / 600 : ℝ) := by
    rw [div_le_iff₀ hlogN]
    simpa [N, C, q] using hsize
  change maynardAmplitude c N
      ‖heathBrownBoxFactorValue L X k box
        ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤ 24 / 25
  dsimp only [maynardDerivativeDeficit] at hamp
  norm_num at hamp ⊢
  linarith

/-- Uniform absorption of the order-three derivative constant on every near-height witness. -/
theorem eventually_maynard_overweight_factor_amplitude_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          ∀ j : HeathBrownBoxFactorIndex k box.m,
            (heathBrownBoxFactorKind k box.m j = .zeta ∨
              heathBrownBoxFactorKind k box.m j = .log) →
            1 - 2 * (mu / 120) < dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q j) →
            Real.log
                (heathBrownDerivativeConstant X
                  (heathBrownBoxFactorKind k box.m j)
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
              (1 / 600 : ℝ) * Real.log
                (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let eps : ℝ := 13 / 16200
  have heps : 0 < eps := by norm_num [eps]
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le heps,
    hconst, Filter.eventually_gt_atTop (1 : ℝ)] with T hE hconstT hT
  intro X hX mu hmuHi hXscale L k box j hkind hover
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let N : ℝ := (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hCup : C ≤ 5120 * maynardLongPolylogEnvelope X :=
    heathBrownDerivativeConstant_le_polylogEnvelope box j hkind hX
  have hE1 : 1 ≤ maynardLongPolylogEnvelope X :=
    one_le_maynardLongPolylogEnvelope X
  have hlogC : Real.log C ≤ Real.log 5120 +
      Real.log (maynardLongPolylogEnvelope X) := by
    calc
      Real.log C ≤ Real.log (5120 * maynardLongPolylogEnvelope X) :=
        Real.log_le_log hC hCup
      _ = Real.log 5120 + Real.log (maynardLongPolylogEnvelope X) := by
        rw [Real.log_mul (by norm_num)
          (ne_of_gt (lt_of_lt_of_le zero_lt_one hE1))]
  have hlogE := hE X hX mu hmuHi hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by linarith
  have hN := dyadic_length_ge_twentySixTwentySeven_root_of_overweight hT hmuHi hover
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (26 / 27 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hlogN : (26 / 27 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hscaled := mul_le_mul_of_nonneg_left hlogN (by norm_num : (0 : ℝ) ≤ 1 / 600)
  calc
    Real.log C ≤ 2 * eps * Real.log T := hlogCsmall
    _ = (1 / 600 : ℝ) * ((26 / 27 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ (1 / 600 : ℝ) * Real.log N := hscaled

/-- A near-height witness occupies at least `9/20` of the full eligible box length. -/
theorem maynard_overweight_heathBrownBox_factor_relative_length
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    {T mu : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j)) :
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
        (9 / 20 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let D : ℝ := ((groupedDyadicLower
    (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  let N : ℝ := (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hDscale : D ≤ T ^ mu := by
    have hDX : D ≤ (X : ℝ) := by simpa [D] using hcoreX
    exact hDX.trans hXscale
  have hraise := Real.rpow_le_rpow hD0 hDscale (by norm_num : (0 : ℝ) ≤ 9 / 20)
  have hcollapse : (T ^ mu) ^ (9 / 20 : ℝ) = T ^ (mu * (9 / 20)) := by
    rw [← Real.rpow_mul hT0.le]
  rw [hcollapse] at hraise
  have hexp : mu * (9 / 20) ≤ (26 / 27 : ℝ) := by linarith
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hT.le hexp
  have hNroot : T ^ (26 / 27 : ℝ) ≤ N :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight hT hmuHi hover
  exact hraise.trans (hmiddle.trans hNroot)

/-- **Overweight-cell amplitude capstone.**  The order-three local gap, weighted over the full
eligible box, forces the global amplitude below `99/100`. -/
theorem maynard_heathBrownBox_overweight_global_amplitude_le_ninetyNine_div_hundred
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {T mu c y alpha : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 19 / 9)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      (1 / 600 : ℝ) * Real.log
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hslackMass :
      ∑ i : HeathBrownBoxFactorIndex k box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
        maynardLongGlobalAmplitudeDeficit * Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ))
    (hlarge :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^ (alpha - c) ≤
        ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
          ((c : ℂ) + (y : ℝ) * Complex.I)‖) :
    alpha ≤ 99 / 100 := by
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qj := heathBrownBoxFactorExponent box.a box.b box.q j
  have hNbase : T ^ (26 / 27 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight hready.1 hmuHi hover
  have hroot1 : 1 < T ^ (26 / 27 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 26 / 27)
  have hjpos : 1 ≤ qj := by
    by_contra hnot
    have hqj : qj = 0 := by omega
    have : (1 : ℝ) < 1 := by simpa [hqj] using hroot1.trans_le hNbase
    linarith
  let Z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X k box s i
  have hD0 : 0 < ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 < ((groupedDyadicLower
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
  have hV : 0 < ‖heathBrownBoxFactorValue L X k box s j‖ :=
    norm_pos_iff.mpr (by simpa [Z] using hZj)
  have hj := maynard_heathBrown_overweight_factor_amplitude_le_twentyFour_div_twentyFive
    box j hkind hX hready hmuHi hXscale hc hylo hyupper hover hsize
      (by simpa [s] using hV)
  have hlength := maynard_overweight_heathBrownBox_factor_relative_length
    box j hready.1 hmuHi hXscale hcoreX hover
  have hglobal := maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    box hL hX hc (by norm_num : (0 : ℝ) ≤ 1 / 25) j (by simpa [qj] using hjpos)
      (by norm_num at hj ⊢; exact hj) hlength hslackMass hlarge
  have hdsmall := maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  norm_num at hglobal ⊢
  linarith

/-- Every Perron-relevant overweight witness is eventually confined below amplitude `99/100`. -/
theorem eventually_maynard_perronRelevant_overweight_global_amplitude_le_ninetyNine_div_hundred :
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
              1 - 2 * (mu / 120) < dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
              ((groupedDyadicLower
                (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                  (alpha - c) ≤
                ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
              alpha ≤ 99 / 100 := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_maynard_long_box_amplitude_slack_ready,
    eventually_maynard_overweight_factor_amplitude_ready]
      with T hready hslack hsize
  intro X hX mu hmuLo hmuHi hXscale L hL k box helig hrel
    c y alpha hc hylo hyupper j hkind hover hlarge
  have hq : 1 ≤ box.q := heathBrownBox_log_exponent_pos_of_large_core box
    ((c : ℂ) + (y : ℝ) * Complex.I) hlarge
  have hslackMass := hslack X hX mu hmuLo hmuHi hXscale L k box hq helig
  have hsize' := hsize X hX mu hmuHi hXscale L k box j hkind hover
  exact maynard_heathBrownBox_overweight_global_amplitude_le_ninetyNine_div_hundred
    box hready hmuLo hmuHi hL hX hXscale hc hylo hyupper
      (perronRelevant_heathBrownBox_coreLower_le hrel) j hkind hover hsize'
      hslackMass hlarge

/-- A witness heavier than a `5/12` cell minus `2t` has exponent above `103/270`. -/
theorem dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
    {T mu beta : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9) {q : ℕ}
    (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q) :
    T ^ (103 / 270 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
  have hexp : (103 / 270 : ℝ) ≤ dyadicLogExponent T q := by linarith
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT).monotone hexp
  rwa [rpow_dyadicLogExponent hT q] at hpow

theorem maynard_moderate_orderFour_factorial
    {T mu beta : ℝ} (hready : IsMaynardLongScaleReady T)
    (hmuHi : mu ≤ 19 / 9) {q : ℕ} (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q) :
    Nat.factorial ((4 : ℕ) - 1) ≤ 2 ^ q := by
  have hN := dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
    hready.1 hmuHi hbeta hwitness
  have hrootCompare : T ^ (1 / 45 : ℝ) ≤ T ^ (103 / 270 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le (by norm_num)
  have hfacNat : Nat.factorial 3 ≤ Nat.factorial 46 :=
    Nat.factorial_le (by norm_num)
  have hfacReal : ((Nat.factorial 3 : ℕ) : ℝ) ≤
      ((Nat.factorial 46 : ℕ) : ℝ) := by exact_mod_cast hfacNat
  have hreal : ((Nat.factorial 3 : ℕ) : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) :=
    hfacReal.trans (hready.2.2.1.trans (hrootCompare.trans hN))
  exact_mod_cast hreal

theorem maynard_moderate_orderFour_high_window
    {T mu beta y : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 19 / 9) {q : ℕ}
    (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q)
    (hy : y ≤ 2 * T) :
    y ≤ 2 * Real.pi * 2 ^ (4 : ℕ) *
      (((2 ^ q : ℕ) : ℝ)) ^ ((4 : ℕ) - 1) *
      (((2 ^ q : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hNroot : T ^ (103 / 270 : ℝ) ≤ N :=
    dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
      hT hmuHi hbeta hwitness
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
    hNroot (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have hleft : (T ^ (103 / 270 : ℝ)) ^ (8 / 3 : ℝ) =
      T ^ (412 / 405 : ℝ) := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  rw [hleft] at hraise
  have hTpow : T ≤ T ^ (412 / 405 : ℝ) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le
      (by norm_num : (1 : ℝ) ≤ 412 / 405)
    simpa using hpow
  have hTN : T ≤ N ^ (8 / 3 : ℝ) := hTpow.trans hraise
  have hshape : N ^ ((4 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ) =
      N ^ (8 / 3 : ℝ) := by
    norm_num
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
    norm_num
  change y ≤ 2 * Real.pi * 2 ^ (4 : ℕ) *
    N ^ ((4 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ)
  have hconstant : (2 : ℝ) ≤ 2 * Real.pi * 2 ^ (4 : ℕ) := by
    nlinarith [Real.pi_gt_three]
  calc
    y ≤ 2 * T := hy
    _ ≤ 2 * N ^ (8 / 3 : ℝ) := mul_le_mul_of_nonneg_left hTN (by norm_num)
    _ ≤ (2 * Real.pi * 2 ^ (4 : ℕ)) * N ^ (8 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hN0.le _)
    _ = (2 * Real.pi * 2 ^ (4 : ℕ)) *
        (N ^ ((4 : ℕ) - 1) * N ^ (-(1 / 3) : ℝ)) := by rw [hshape]
    _ = _ := by ring

/-- Order-four local amplitude law for every witness in a selected cell above `5/12`. -/
theorem maynard_heathBrown_moderate_factor_amplitude_le_fortyNine_div_fifty
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hL : 1 ≤ L) (hX : 1 ≤ X) {T mu beta c y : ℝ}
    (hready : IsMaynardLongScaleReady T) (hmuHi : mu ≤ 19 / 9)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      (1 / 1200 : ℝ) * Real.log
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hV : 0 < ‖heathBrownBoxFactorValue L X k box
      ((c : ℂ) + (y : ℝ) * Complex.I) j‖) :
    maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤ 49 / 50 := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j) q
  have hNbase := dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
    hready.1 hmuHi hbeta hwitness
  have hroot1 : 1 < T ^ (103 / 270 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 103 / 270)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 0 < C := by
    dsimp [C, q]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_moderate_orderFour_factorial hready hmuHi hbeta hwitness
  have hlow := maynard_zeta_log_factor_low_window
    box j hkind hX hready.1 hmuHi hXscale hylo hready.2.1
  have hhigh := maynard_moderate_orderFour_high_window
    hready.1 hmuHi hbeta hwitness hyupper
  have hy0 : 0 < y := lt_trans zero_lt_one (hready.1.trans_le hylo)
  have hqX := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hupper := norm_heathBrownBoxFactorValue_le_derivative_defect
    L X k box j hkind hX hc hy0 (k₀ := 4) (by norm_num) hqX hfac hlow hhigh
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    hN hV hC (by simpa [N, C, q] using hupper)
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hratio : Real.log C / Real.log N ≤ (1 / 1200 : ℝ) := by
    rw [div_le_iff₀ hlogN]
    simpa [N, C, q] using hsize
  change maynardAmplitude c N
      ‖heathBrownBoxFactorValue L X k box
        ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤ 49 / 50
  dsimp only [maynardDerivativeDeficit] at hamp
  norm_num at hamp ⊢
  linarith

theorem eventually_maynard_moderate_factor_amplitude_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          ∀ beta : ℝ, 5 / 12 < beta →
          ∀ j : HeathBrownBoxFactorIndex k box.m,
            (heathBrownBoxFactorKind k box.m j = .zeta ∨
              heathBrownBoxFactorKind k box.m j = .log) →
            beta - 2 * (mu / 120) < dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q j) →
            Real.log
                (heathBrownDerivativeConstant X
                  (heathBrownBoxFactorKind k box.m j)
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
              (1 / 1200 : ℝ) * Real.log
                (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let eps : ℝ := 103 / 648000
  have heps : 0 < eps := by norm_num [eps]
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le heps,
    hconst, Filter.eventually_gt_atTop (1 : ℝ)] with T hE hconstT hT
  intro X hX mu hmuHi hXscale L k box beta hbeta j hkind hwitness
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let N : ℝ := (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hCup : C ≤ 5120 * maynardLongPolylogEnvelope X :=
    heathBrownDerivativeConstant_le_polylogEnvelope box j hkind hX
  have hE1 : 1 ≤ maynardLongPolylogEnvelope X := one_le_maynardLongPolylogEnvelope X
  have hlogC : Real.log C ≤ Real.log 5120 +
      Real.log (maynardLongPolylogEnvelope X) := by
    calc
      Real.log C ≤ Real.log (5120 * maynardLongPolylogEnvelope X) :=
        Real.log_le_log hC hCup
      _ = Real.log 5120 + Real.log (maynardLongPolylogEnvelope X) := by
        rw [Real.log_mul (by norm_num)
          (ne_of_gt (lt_of_lt_of_le zero_lt_one hE1))]
  have hlogE := hE X hX mu hmuHi hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by linarith
  have hN := dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
    hT hmuHi hbeta hwitness
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (103 / 270 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hlogN : (103 / 270 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hscaled := mul_le_mul_of_nonneg_left hlogN (by norm_num : (0 : ℝ) ≤ 1 / 1200)
  calc
    Real.log C ≤ 2 * eps * Real.log T := hlogCsmall
    _ = (1 / 1200 : ℝ) * ((103 / 270 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ (1 / 1200 : ℝ) * Real.log N := hscaled

/-- Middle cells force a full-box amplitude gap `3/1000`. -/
theorem eventually_maynard_perronRelevant_moderate_global_amplitude_le_997 :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, 1 ≤ L → ∀ k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          IsHeathBrownBoxEligible L X k T (mu / 120) box →
          IsHeathBrownBoxPerronRelevant X k box →
          ∀ c y alpha beta : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
            5 / 12 < beta →
            ∀ j : HeathBrownBoxFactorIndex k box.m,
              (heathBrownBoxFactorKind k box.m j = .zeta ∨
                heathBrownBoxFactorKind k box.m j = .log) →
              beta - 2 * (mu / 120) < dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
              ((groupedDyadicLower
                (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                  (alpha - c) ≤
                ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
              alpha ≤ 997 / 1000 := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_maynard_long_box_amplitude_slack_ready,
    eventually_maynard_moderate_factor_amplitude_ready]
      with T hready hslack hsize
  intro X hX mu hmuLo hmuHi hXscale L hL k box helig hrel
    c y alpha beta hc hylo hyupper hbeta j hkind hwitness hlarge
  have hq : 1 ≤ box.q := heathBrownBox_log_exponent_pos_of_large_core box
    ((c : ℂ) + (y : ℝ) * Complex.I) hlarge
  have hslackMass := hslack X hX mu hmuLo hmuHi hXscale L k box hq helig
  have hsize' := hsize X hX mu hmuHi hXscale L k box beta hbeta j hkind hwitness
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qj := heathBrownBoxFactorExponent box.a box.b box.q j
  have hNbase := dyadic_length_ge_oneHundredThreeTwoSeventy_root_of_moderate_cell
    hready.1 hmuHi hbeta hwitness
  have hroot1 : 1 < T ^ (103 / 270 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 103 / 270)
  have hjpos : 1 ≤ qj := by
    by_contra hnot
    have hqj : qj = 0 := by omega
    have hone := hroot1.trans_le hNbase
    change (1 : ℝ) < (((2 ^ qj : ℕ) : ℝ)) at hone
    rw [hqj] at hone
    norm_num at hone
  let Z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    heathBrownBoxFactorValue L X k box s i
  have hD0 : 0 < ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
    exact lt_of_lt_of_le zero_lt_one (by
      exact_mod_cast one_le_groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q))
  have hcorePos : 0 <
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q s‖ := by
    have hthreshold : 0 < ((groupedDyadicLower
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
  have hV : 0 < ‖heathBrownBoxFactorValue L X k box s j‖ :=
    norm_pos_iff.mpr (by simpa [Z] using hZj)
  have hj := maynard_heathBrown_moderate_factor_amplitude_le_fortyNine_div_fifty
    box j hkind hL hX hready hmuHi hXscale hc hylo hyupper hbeta hwitness hsize'
      (by simpa [s] using hV)
  have hlength :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
          (9 / 50 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) := by
    let D : ℝ := ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
    have hD0' : 0 ≤ D := by dsimp [D]; positivity
    have hDX : D ≤ (X : ℝ) := by
      simpa [D] using perronRelevant_heathBrownBox_coreLower_le hrel
    have hDscale : D ≤ T ^ mu := hDX.trans hXscale
    have hraise := Real.rpow_le_rpow hD0' hDscale (by norm_num : (0 : ℝ) ≤ 9 / 50)
    have hT0 : 0 < T := lt_trans zero_lt_one hready.1
    have hcollapse : (T ^ mu) ^ (9 / 50 : ℝ) = T ^ (mu * (9 / 50)) := by
      rw [← Real.rpow_mul hT0.le]
    rw [hcollapse] at hraise
    have hexp : mu * (9 / 50) ≤ (103 / 270 : ℝ) := by linarith
    have hmiddle := Real.rpow_le_rpow_of_exponent_le hready.1.le hexp
    simpa [D, qj] using hraise.trans (hmiddle.trans hNbase)
  have hglobal := maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    box hL hX hc (by norm_num : (0 : ℝ) ≤ 1 / 50) j (by simpa [qj] using hjpos)
      (by norm_num at hj ⊢; exact hj) hlength hslackMass hlarge
  have hdsmall := maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  norm_num at hglobal ⊢
  linarith

end RHTower.Sieve
