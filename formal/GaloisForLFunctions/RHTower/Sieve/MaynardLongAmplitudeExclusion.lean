import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MaynardArbitraryAmplitudeCount
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicGreedyGroup

/-!
# Long-factor exclusion in fixed-abscissa amplitude coordinates

This module combines exact local derivative deficit, one-logarithm slack mass, and Maynard's
height geometry.  It produces a fixed global product-amplitude deficit, which then matches the
arbitrarily small Huxley energy loss.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Any factor above `T^(1/45)` occupies at least `1/95` of the logarithmic length of a product
bounded by `X ≤ T^mu`, uniformly for `mu ≤ 19/9`. -/
theorem maynard_long_factor_relative_length
    {T x X N mu : ℝ} (hT : 1 < T) (hx : 0 ≤ x) (hxX : x ≤ X)
    (hXscale : X ≤ T ^ mu) (hmu : mu ≤ 19 / 9)
    (hN : T ^ (1 / 45 : ℝ) ≤ N) :
    x ^ (1 / 95 : ℝ) ≤ N := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hX0 : 0 ≤ X := hx.trans hxX
  have hxscale : x ≤ T ^ mu := hxX.trans hXscale
  have hfirst : x ^ (1 / 95 : ℝ) ≤ (T ^ mu) ^ (1 / 95 : ℝ) :=
    Real.rpow_le_rpow hx hxscale (by norm_num)
  have hflatten : (T ^ mu) ^ (1 / 95 : ℝ) = T ^ (mu / 95) := by
    rw [← Real.rpow_mul hT0.le]
    congr 1
    ring
  have hexp : mu / 95 ≤ 1 / 45 := by linarith
  have hsecond : T ^ (mu / 95) ≤ T ^ (1 / 45 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT.le hexp
  exact hfirst.trans_eq hflatten |>.trans (hsecond.trans hN)

/-- Exact Route-T global deficit left by a long derivative-controlled factor after paying half
of its length-weighted saving to the unique logarithmic slack. -/
theorem maynard_heathBrownBox_long_factor_global_deficit
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {c y alpha : ℝ} (hc : 0 ≤ c)
    (hqpos : ∀ i : HeathBrownBoxFactorIndex k box.m,
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hj : maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖LSeries (complexCoeff (arithmeticDyadicBlock
          (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m j))
          (heathBrownBoxFactorExponent box.a box.b box.q j)))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤
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
  have h := maynard_heathBrownBox_threshold_one_factor_deficit
    box hc hqpos hDelta j hj hlength hslackMass hlarge
  convert h using 1
  dsimp [maynardDerivativeDeficit]
  ring

/-- The fixed positive global deficit produced by the long-factor branch. -/
def maynardLongGlobalAmplitudeDeficit : ℝ := maynardDerivativeDeficit 47 / 380

theorem maynardLongGlobalAmplitudeDeficit_pos :
    0 < maynardLongGlobalAmplitudeDeficit := by
  dsimp [maynardLongGlobalAmplitudeDeficit, maynardDerivativeDeficit]
  positivity

/-- Canonical arbitrary energy loss matched to the long-factor global deficit. -/
def maynardLongMatchedEnergyRho : ℝ :=
  maynardPointwiseMatchedRho maynardLongGlobalAmplitudeDeficit

theorem maynardLongMatchedEnergyRho_pos : 0 < maynardLongMatchedEnergyRho :=
  maynardPointwiseMatchedRho_pos maynardLongGlobalAmplitudeDeficit_pos

/-- Every canonical long box factor occupies relative logarithmic length at least `1/95`, once
the Perron-relevant box lower edge is at most `X`. -/
theorem maynard_long_heathBrownBox_factor_relative_length
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    {T t mu : ℝ} (hT : 1 < T) (hmu_lo : 4 / 3 ≤ mu)
    (hmu_hi : mu ≤ 19 / 9) (ht : t = mu / 120)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (hlong : 2 * t < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j)) :
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
        (1 / 95 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  have hN := dyadic_length_ge_fortyFive_root_of_maynard_long
    hT hmu_lo ht hlong
  exact maynard_long_factor_relative_length hT (by positivity)
    (by exact_mod_cast hcoreX) hXscale hmu_hi hN

/-- The unique logarithmic amplitude slack is eventually at most half the fixed long-factor
global deficit, uniformly over every eligible literal box and Maynard cutoff. -/
theorem eventually_maynard_long_box_amplitude_slack_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          1 ≤ box.q → IsHeathBrownBoxEligible L X k T (mu / 120) box →
          ∑ i : HeathBrownBoxFactorIndex k box.m,
              heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind k box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
            maynardLongGlobalAmplitudeDeficit *
              Real.log
                ((groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
  let eps : ℝ := maynardLongGlobalAmplitudeDeficit / 90
  have heps : 0 < eps := div_pos maynardLongGlobalAmplitudeDeficit_pos (by norm_num)
  filter_upwards [eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le heps,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hsum hT
  intro X hX mu hmu_lo hmu_hi hXscale L k box hq helig
  have hraw := hsum X hX mu hmu_hi hXscale L k box hq
  let total : ℝ := heathBrownBoxTotalExponent L X k T box
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
        (Finset.univ : Finset (HeathBrownBoxFactorIndex k box.m)))
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT.le
  have hlogD : Real.log D = total * Real.log T := by
    rw [hD, Real.log_rpow (lt_trans zero_lt_one hT)]
  have hbase : (1 / 90 : ℝ) * Real.log T ≤ Real.log D := by
    rw [hlogD]
    exact mul_le_mul_of_nonneg_right htotalMin hlogT
  have hdef0 : 0 ≤ maynardLongGlobalAmplitudeDeficit :=
    maynardLongGlobalAmplitudeDeficit_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hbase hdef0
  have habsorb : eps * Real.log T ≤
      maynardLongGlobalAmplitudeDeficit * Real.log D := by
    calc
      eps * Real.log T =
          maynardLongGlobalAmplitudeDeficit *
            ((1 / 90 : ℝ) * Real.log T) := by
        dsimp [eps]
        ring
      _ ≤ maynardLongGlobalAmplitudeDeficit * Real.log D := hscaled
  exact hraw.trans (by simpa [D] using habsorb)

theorem heathBrownDerivativeConstant_pos_of_zeta_or_log
    {X : ℕ} (kind : HeathBrownFactorKind) (q : ℕ)
    (hX : 1 ≤ X) (hkind : kind = .zeta ∨ kind = .log) :
    0 < heathBrownDerivativeConstant X kind q := by
  rcases hkind with rfl | rfl
  · simp [heathBrownDerivativeConstant]
  · dsimp [heathBrownDerivativeConstant]
    have htop2 : 2 ≤ heathBrownDyadicFactorTop X q := by
      rw [heathBrownDyadicFactorTop, Nat.le_min]
      constructor
      · omega
      · calc
          2 = 2 ^ (1 : ℕ) := by norm_num
          _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htop : (1 : ℝ) < heathBrownDyadicFactorTop X q := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) htop2)
    exact mul_pos (by norm_num) (Real.log_pos htop)

theorem heathBrownDerivativeConstant_le_polylogEnvelope
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) :
    heathBrownDerivativeConstant X
        (heathBrownBoxFactorKind k box.m j)
        (heathBrownBoxFactorExponent box.a box.b box.q j) ≤
      5120 * maynardLongPolylogEnvelope X := by
  rcases j with j | j
  · simp [heathBrownBoxFactorKind] at hkind
  · rcases j with j | j
    · dsimp [heathBrownBoxFactorKind, heathBrownDerivativeConstant]
      have hE := one_le_maynardLongPolylogEnvelope X
      nlinarith
    · rcases j with ⟨⟩
      simp only [heathBrownBoxFactorKind, heathBrownBoxFactorExponent,
        heathBrownDerivativeConstant]
      exact mul_le_mul_of_nonneg_left
        (log_heathBrownDyadicFactorTop_le_polylogEnvelope
          (X := X) (q := box.q) hX) (by norm_num)

theorem one_le_heathBrownDerivativeConstant_of_zeta_or_log
    {X : ℕ} (kind : HeathBrownFactorKind) (q : ℕ)
    (hX : 1 ≤ X) (hkind : kind = .zeta ∨ kind = .log) :
    1 ≤ heathBrownDerivativeConstant X kind q := by
  rcases hkind with rfl | rfl
  · simp [heathBrownDerivativeConstant]
  · dsimp [heathBrownDerivativeConstant]
    have htop2 : 2 ≤ heathBrownDyadicFactorTop X q := by
      rw [heathBrownDyadicFactorTop, Nat.le_min]
      constructor
      · omega
      · calc
          2 = 2 ^ (1 : ℕ) := by norm_num
          _ ≤ 2 ^ (q + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlog : Real.log 2 ≤ Real.log (heathBrownDyadicFactorTop X q : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast htop2)
    have hlog2 := Real.log_two_gt_d9
    nlinarith

/-- Ready-scale local derivative theorem stated directly for the exact amplitude coordinate of
the actual long factor. -/
theorem maynard_heathBrown_long_factor_amplitude_le_one_sub_half
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) {T t mu c y : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hlong : 2 * t < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : 2 * Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      maynardDerivativeDeficit 47 *
        Real.log
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hV : 0 < ‖heathBrownBoxFactorValue L X k box
      ((c : ℂ) + (y : ℝ) * Complex.I) j‖) :
    maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
      1 - maynardDerivativeDeficit 47 / 2 := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j) q
  have hNbase := dyadic_length_ge_fortyFive_root_of_maynard_long
    hready.1 hmu_lo ht hlong
  have hroot1 : 1 < T ^ (1 / 45 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 1 / 45)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 1 ≤ C := by
    dsimp [C, q]
    exact one_le_heathBrownDerivativeConstant_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_long_fixedOrder_factorial
    hready.1 hmu_lo ht hlong hready.2.2.1
  have hlow := maynard_zeta_log_factor_low_window
    box j hkind hX hready.1 hmu_hi hXscale hylo hready.2.1
  have hhigh := maynard_long_fixedOrder_high_window
    hready.1 hmu_lo ht hlong hyupper
  have hy0 : 0 < y := lt_trans zero_lt_one (hready.1.trans_le hylo)
  have hqX := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hupper := norm_heathBrownBoxFactorValue_le_derivative_defect
    L X k box j hkind hX hc hy0 (k₀ := 47) (by norm_num) hqX hfac hlow hhigh
  exact maynardAmplitude_le_one_sub_half_of_pointwise_power_saving
    hN hV hC (by simpa [N, C, q] using hsize)
      (by simpa [N, C, q] using hupper)

/-- Uniform eventual absorption of the derivative-test constant by half of the order-47 local
power saving. -/
theorem eventually_maynard_long_factor_amplitude_half_deficit_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 19 / 9 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L k : ℕ, ∀ box : HeathBrownBoxChoice L X k,
          ∀ j : HeathBrownBoxFactorIndex k box.m,
            (heathBrownBoxFactorKind k box.m j = .zeta ∨
              heathBrownBoxFactorKind k box.m j = .log) →
            2 * (mu / 120) < dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q j) →
            2 * Real.log
                (heathBrownDerivativeConstant X
                  (heathBrownBoxFactorKind k box.m j)
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
              maynardDerivativeDeficit 47 *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let eps : ℝ := maynardDerivativeDeficit 47 / 180
  have heps : 0 < eps := by
    dsimp [eps, maynardDerivativeDeficit]
    positivity
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le heps,
    hconst, Filter.eventually_gt_atTop (1 : ℝ)] with T hE hconstT hT
  intro X hX mu hmu_lo hmu_hi hXscale L k box j hkind hlong
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hE1 : 1 ≤ maynardLongPolylogEnvelope X :=
    one_le_maynardLongPolylogEnvelope X
  have hCup : C ≤ 5120 * maynardLongPolylogEnvelope X :=
    heathBrownDerivativeConstant_le_polylogEnvelope box j hkind hX
  have hlogC : Real.log C ≤ Real.log 5120 +
      Real.log (maynardLongPolylogEnvelope X) := by
    calc
      Real.log C ≤ Real.log (5120 * maynardLongPolylogEnvelope X) :=
        Real.log_le_log hC hCup
      _ = Real.log 5120 + Real.log (maynardLongPolylogEnvelope X) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
  have hlogE := hE X hX mu hmu_hi hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by
    linarith
  have hN := dyadic_length_ge_fortyFive_root_of_maynard_long
    hT hmu_lo rfl hlong
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (1 / 45 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hN0 : 0 < N := hroot0.trans_le hN
  have hlogN : (1 / 45 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hdelta : 0 ≤ maynardDerivativeDeficit 47 := by
    dsimp [maynardDerivativeDeficit]
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hlogN hdelta
  calc
    2 * Real.log C ≤ 4 * eps * Real.log T := by linarith
    _ = maynardDerivativeDeficit 47 * ((1 / 45 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ maynardDerivativeDeficit 47 * Real.log N := hscaled

/-- **Long-factor fixed-abscissa capstone.**  At a ready height, the actual literal box product
has the fixed global amplitude deficit once the two uniform scalar readiness inequalities proved
above are instantiated. -/
theorem maynard_heathBrownBox_long_factor_global_deficit_of_ready
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {T t mu c y alpha : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hqpos : ∀ i : HeathBrownBoxFactorIndex k box.m,
      1 ≤ heathBrownBoxFactorExponent box.a box.b box.q i)
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
  let Z : HeathBrownBoxFactorIndex k box.m → ℂ := fun i =>
    LSeries (complexCoeff (arithmeticDyadicBlock
      (heathBrownFactorBase L X (heathBrownBoxFactorKind k box.m i))
      (heathBrownBoxFactorExponent box.a box.b box.q i))) s
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
    simpa [Z] using heathBrownBoxFactorProduct_eq_core
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
  have hglobal := maynard_heathBrownBox_long_factor_global_deficit
    box hc hqpos j (by simpa [s] using hj) hlength
      (by simpa [maynardLongGlobalAmplitudeDeficit] using hslackMass) hlarge
  simpa [maynardLongGlobalAmplitudeDeficit] using hglobal

end RHTower.Sieve
