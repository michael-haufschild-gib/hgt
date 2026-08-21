import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightZetaLogExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleFibreCount
import GaloisForLFunctions.RHTower.Sieve.MaynardUnboundedHeightScalar

/-!
# Route-T selected-cell exclusion through height ratio `11/5`

The historical `19/9` ceiling in moderate and overweight selected-cell exclusion is not a
derivative-test barrier. Retuning the factor-to-box shares from `9/20` to `7/16` and from `9/50`
to `17/100`, while using the low-ordinate logarithmic envelope, preserves the exact global
amplitude caps `983/1000` and `997/1000` through `mu = 11/5`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

theorem dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
    {T mu : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 11 / 5) {q : ℕ}
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T q) :
    T ^ (26 / 27 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
  have hexp : (26 / 27 : ℝ) ≤ dyadicLogExponent T q := by linarith
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT).monotone hexp
  rwa [rpow_dyadicLogExponent hT q] at hpow

theorem maynard_overweight_orderThree_factorial_elevenFifths
    {T mu : ℝ} (_hT : 1 < T) (hmuHi : mu ≤ 11 / 5) {q : ℕ}
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

theorem maynard_overweight_orderThree_high_window_elevenFifths
    {T mu y : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 11 / 5) {q : ℕ}
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T q)
    (hy : y ≤ 2 * T) :
    y ≤ 2 * Real.pi * 2 ^ (3 : ℕ) *
      (((2 ^ q : ℕ) : ℝ)) ^ ((3 : ℕ) - 1) *
      (((2 ^ q : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hNroot : T ^ (26 / 27 : ℝ) ≤ N :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
      hT hmuHi hover
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
    simpa using Real.rpow_le_rpow_of_exponent_le hT.le
      (by norm_num : (1 : ℝ) ≤ 130 / 81)
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
    _ = _ := by ring

theorem maynard_overweight_heathBrownBox_factor_relative_length_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    {T mu : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 11 / 5)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (hover : 1 - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j)) :
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
        (7 / 16 : ℝ) ≤
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let D : ℝ := ((groupedDyadicLower
    (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  let N : ℝ := (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hDscale : D ≤ T ^ mu := by
    have hDX : D ≤ (X : ℝ) := by simpa [D] using hcoreX
    exact hDX.trans hXscale
  have hraise := Real.rpow_le_rpow hD0 hDscale (by norm_num : (0 : ℝ) ≤ 7 / 16)
  have hcollapse : (T ^ mu) ^ (7 / 16 : ℝ) = T ^ (mu * (7 / 16)) := by
    rw [← Real.rpow_mul hT0.le]
  rw [hcollapse] at hraise
  have hexp : mu * (7 / 16) ≤ (26 / 27 : ℝ) := by linarith
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hT.le hexp
  have hNroot : T ^ (26 / 27 : ℝ) ≤ N :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
      hT hmuHi hover
  exact hraise.trans (hmiddle.trans hNroot)

theorem dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
    {T mu beta : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 11 / 5) {q : ℕ}
    (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q) :
    T ^ (19 / 50 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
  have hexp : (19 / 50 : ℝ) ≤ dyadicLogExponent T q := by linarith
  have hpow := (Real.strictMono_rpow_of_base_gt_one hT).monotone hexp
  rwa [rpow_dyadicLogExponent hT q] at hpow

theorem maynard_moderate_orderFour_factorial_elevenFifths
    {T mu beta : ℝ} (hready : IsMaynardLongScaleReady T)
    (hmuHi : mu ≤ 11 / 5) {q : ℕ} (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q) :
    Nat.factorial ((4 : ℕ) - 1) ≤ 2 ^ q := by
  have hN := dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
    hready.1 hmuHi hbeta hwitness
  have hrootCompare : T ^ (1 / 45 : ℝ) ≤ T ^ (19 / 50 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le (by norm_num)
  have hfacNat : Nat.factorial 3 ≤ Nat.factorial 46 :=
    Nat.factorial_le (by norm_num)
  have hfacReal : ((Nat.factorial 3 : ℕ) : ℝ) ≤
      ((Nat.factorial 46 : ℕ) : ℝ) := by exact_mod_cast hfacNat
  have hreal : ((Nat.factorial 3 : ℕ) : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) :=
    hfacReal.trans (hready.2.2.1.trans (hrootCompare.trans hN))
  exact_mod_cast hreal

theorem maynard_moderate_orderFour_high_window_elevenFifths
    {T mu beta y : ℝ} (hT : 1 < T) (hmuHi : mu ≤ 11 / 5) {q : ℕ}
    (hbeta : 5 / 12 < beta)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T q)
    (hy : y ≤ 2 * T) :
    y ≤ 2 * Real.pi * 2 ^ (4 : ℕ) *
      (((2 ^ q : ℕ) : ℝ)) ^ ((4 : ℕ) - 1) *
      (((2 ^ q : ℕ) : ℝ)) ^ (-(1 / 3) : ℝ) := by
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  have hNroot : T ^ (19 / 50 : ℝ) ≤ N :=
    dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
      hT hmuHi hbeta hwitness
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hN0 : 0 < N := by dsimp [N]; positivity
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
    hNroot (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have hleft : (T ^ (19 / 50 : ℝ)) ^ (8 / 3 : ℝ) =
      T ^ (76 / 75 : ℝ) := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  rw [hleft] at hraise
  have hTpow : T ≤ T ^ (76 / 75 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hT.le
      (by norm_num : (1 : ℝ) ≤ 76 / 75)
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

theorem maynard_zeta_log_factor_low_window_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) {T mu y : ℝ} (hT : 1 < T)
    (hmuHi : mu ≤ 11 / 5) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hy : T ≤ y) (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ)) :
    8 * Real.pi *
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
          ((1 : ℝ) / 3) ≤ y := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hq := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hNnat : 2 ^ heathBrownBoxFactorExponent box.a box.b box.q j ≤ X :=
    (Nat.pow_le_pow_right (by norm_num) hq).trans
      (Nat.pow_log_le_self 2 (by omega : X ≠ 0))
  have hNX : N ≤ (X : ℝ) := by dsimp [N]; exact_mod_cast hNnat
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have hX0 : 0 ≤ (X : ℝ) := by positivity
  have hthird : N ^ ((1 : ℝ) / 3) ≤ (X : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hN0 hNX (by norm_num)
  have hmu3 : mu / 3 ≤ 11 / 15 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hXpow : (X : ℝ) ^ ((1 : ℝ) / 3) ≤ T ^ (11 / 15 : ℝ) := by
    calc
      (X : ℝ) ^ ((1 : ℝ) / 3) ≤ (T ^ mu) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hX0 hXscale (by norm_num)
      _ = T ^ (mu / 3) := by
        rw [← Real.rpow_mul hT0]
        congr 1
        ring
      _ ≤ T ^ (11 / 15 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT.le hmu3
  calc
    8 * Real.pi * N ^ ((1 : ℝ) / 3)
        ≤ T ^ (4 / 15 : ℝ) * T ^ (11 / 15 : ℝ) :=
      mul_le_mul hpi (hthird.trans hXpow) (Real.rpow_nonneg hN0 _)
        (Real.rpow_nonneg hT0 _)
    _ = T := by
      rw [← Real.rpow_add (by linarith : 0 < T)]
      norm_num
    _ ≤ y := hy

theorem eventually_eight_pi_le_rpow_fourFifteenths :
    ∀ᶠ T : ℝ in Filter.atTop, 8 * Real.pi ≤ T ^ (4 / 15 : ℝ) := by
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 15)).eventually_ge_atTop
    (8 * Real.pi)

theorem eventually_maynard_elevenFifths_long_box_amplitude_slack_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
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
  filter_upwards [
    eventually_sum_heathBrownBoxFactorAmplitudeSlack_mul_log_le_lowOrdinate heps,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hsum hT
  intro X hX mu hmuLo hmuHi hXscale L k box hq helig
  have hraw := hsum X hX mu (by linarith : mu ≤ 8) hXscale L k box hq
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
  have hscaled := mul_le_mul_of_nonneg_left hbase
    maynardLongGlobalAmplitudeDeficit_pos.le
  have habsorb : eps * Real.log T ≤
      maynardLongGlobalAmplitudeDeficit * Real.log D := by
    calc
      eps * Real.log T = maynardLongGlobalAmplitudeDeficit *
          ((1 / 90 : ℝ) * Real.log T) := by dsimp [eps]; ring
      _ ≤ maynardLongGlobalAmplitudeDeficit * Real.log D := hscaled
  exact hraw.trans (by simpa [D] using habsorb)

theorem eventually_maynard_elevenFifths_overweight_factor_amplitude_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 11 / 5 →
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
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le_lowOrdinate heps,
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
  have hlogE := hE X hX mu (by linarith : mu ≤ 8) hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by linarith
  have hN :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
      hT hmuHi hover
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (26 / 27 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hlogN : (26 / 27 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hscaled := mul_le_mul_of_nonneg_left hlogN
    (by norm_num : (0 : ℝ) ≤ 1 / 600)
  calc
    Real.log C ≤ 2 * eps * Real.log T := hlogCsmall
    _ = (1 / 600 : ℝ) * ((26 / 27 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ (1 / 600 : ℝ) * Real.log N := hscaled

theorem eventually_maynard_elevenFifths_moderate_factor_amplitude_ready :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 11 / 5 →
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
  let eps : ℝ := 19 / 120000
  have heps : 0 < eps := by norm_num [eps]
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le_lowOrdinate heps,
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
  have hlogE := hE X hX mu (by linarith : mu ≤ 8) hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by linarith
  have hN := dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
    hT hmuHi hbeta hwitness
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (19 / 50 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hlogN : (19 / 50 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hscaled := mul_le_mul_of_nonneg_left hlogN
    (by norm_num : (0 : ℝ) ≤ 1 / 1200)
  calc
    Real.log C ≤ 2 * eps * Real.log T := hlogCsmall
    _ = (1 / 1200 : ℝ) * ((19 / 50 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ (1 / 1200 : ℝ) * Real.log N := hscaled

theorem maynard_heathBrown_overweight_factor_amplitude_le_twentyFour_div_twentyFive_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) {T mu c y : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ))
    (hmuHi : mu ≤ 11 / 5) (hXscale : (X : ℝ) ≤ T ^ mu)
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
  have hNbase :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
      hready.1 hmuHi hover
  have hroot1 : 1 < T ^ (26 / 27 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 26 / 27)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 1 ≤ C := by
    dsimp [C, q]
    exact one_le_heathBrownDerivativeConstant_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_overweight_orderThree_factorial_elevenFifths
    hready.1 hmuHi hover
  have hlow := maynard_zeta_log_factor_low_window_elevenFifths
    box j hkind hX hready.1 hmuHi hXscale hylo hpi
  have hhigh := maynard_overweight_orderThree_high_window_elevenFifths
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

theorem maynard_heathBrown_moderate_factor_amplitude_le_fortyNine_div_fifty_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (_hL : 1 ≤ L) (hX : 1 ≤ X) {T mu beta c y : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ))
    (hmuHi : mu ≤ 11 / 5) (hXscale : (X : ℝ) ≤ T ^ mu)
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
  have hNbase := dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
    hready.1 hmuHi hbeta hwitness
  have hroot1 : 1 < T ^ (19 / 50 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 19 / 50)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 0 < C := by
    dsimp [C, q]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_moderate_orderFour_factorial_elevenFifths
    hready hmuHi hbeta hwitness
  have hlow := maynard_zeta_log_factor_low_window_elevenFifths
    box j hkind hX hready.1 hmuHi hXscale hylo hpi
  have hhigh := maynard_moderate_orderFour_high_window_elevenFifths
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

theorem maynard_heathBrownBox_overweight_global_amplitude_le_nineEightyThree_div_thousand_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {T mu c y alpha : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ))
    (_hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 11 / 5)
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
    alpha ≤ 983 / 1000 := by
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qj := heathBrownBoxFactorExponent box.a box.b box.q j
  have hNbase : T ^ (26 / 27 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) :=
    dyadic_length_ge_twentySixTwentySeven_root_of_overweight_elevenFifths
      hready.1 hmuHi hover
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
  have hj :=
    maynard_heathBrown_overweight_factor_amplitude_le_twentyFour_div_twentyFive_elevenFifths
      box j hkind hX hready hpi hmuHi hXscale hc hylo hyupper hover hsize
        (by simpa [s] using hV)
  have hlength := maynard_overweight_heathBrownBox_factor_relative_length_elevenFifths
    box j hready.1 hmuHi hXscale hcoreX hover
  have hglobal := maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    box hL hX hc (by norm_num : (0 : ℝ) ≤ 1 / 25) j (by simpa [qj] using hjpos)
      (by norm_num at hj ⊢; exact hj) hlength hslackMass hlarge
  have hdsmall := maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  norm_num at hglobal ⊢
  linarith

theorem maynard_heathBrownBox_moderate_global_amplitude_le_997_elevenFifths
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    {T mu c y alpha beta : ℝ}
    (hready : IsMaynardLongScaleReady T)
    (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ))
    (_hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 11 / 5)
    (hL : 1 ≤ L) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T ^ mu)
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hcoreX :
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) ≤ X)
    (hbeta : 5 / 12 < beta)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hwitness : beta - 2 * (mu / 120) < dyadicLogExponent T
      (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hsize : Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind k box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      (1 / 1200 : ℝ) * Real.log
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
    alpha ≤ 997 / 1000 := by
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let qj := heathBrownBoxFactorExponent box.a box.b box.q j
  have hNbase : T ^ (19 / 50 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) :=
    dyadic_length_ge_nineteenFiftieths_root_of_moderate_cell_elevenFifths
      hready.1 hmuHi hbeta hwitness
  have hroot1 : 1 < T ^ (19 / 50 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hready.1)
      (by norm_num : (0 : ℝ) < 19 / 50)
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
  have hj := maynard_heathBrown_moderate_factor_amplitude_le_fortyNine_div_fifty_elevenFifths
    box j hkind hL hX hready hpi hmuHi hXscale hc hylo hyupper
      hbeta hwitness hsize (by simpa [s] using hV)
  let D : ℝ := ((groupedDyadicLower
    (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have hD0' : 0 ≤ D := by dsimp [D]; positivity
  have hDscale : D ≤ T ^ mu := by
    have hDX : D ≤ (X : ℝ) := by simpa [D] using hcoreX
    exact hDX.trans hXscale
  have hraise := Real.rpow_le_rpow hD0' hDscale
    (by norm_num : (0 : ℝ) ≤ 17 / 100)
  have hcollapse : (T ^ mu) ^ (17 / 100 : ℝ) =
      T ^ (mu * (17 / 100)) := by
    rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
  rw [hcollapse] at hraise
  have hexp : mu * (17 / 100) ≤ (19 / 50 : ℝ) := by linarith
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hready.1.le hexp
  have hlength :
      ((groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
          (17 / 100 : ℝ) ≤ (((2 ^ qj : ℕ) : ℝ)) := by
    simpa [D, qj] using hraise.trans (hmiddle.trans hNbase)
  have hglobal := maynard_heathBrownBox_threshold_one_factor_deficit_trimmed
    box hL hX hc (by norm_num : (0 : ℝ) ≤ 1 / 50) j (by simpa [qj] using hjpos)
      (by norm_num at hj ⊢; exact hj) hlength hslackMass hlarge
  have hdsmall := maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  norm_num at hglobal ⊢
  linarith

theorem eventually_maynard_perronRelevant_overweight_global_amplitude_le_nineEightyThree_div_thousand_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
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
              alpha ≤ 983 / 1000 := by
  filter_upwards [eventually_isMaynardLongScaleReady,
    eventually_eight_pi_le_rpow_fourFifteenths,
    eventually_maynard_elevenFifths_long_box_amplitude_slack_ready,
    eventually_maynard_elevenFifths_overweight_factor_amplitude_ready]
      with T hready hpi hslack hsize
  intro X hX mu hmuLo hmuHi hXscale L hL k box helig hrel
    c y alpha hc hylo hyupper j hkind hover hlarge
  have hq : 1 ≤ box.q := heathBrownBox_log_exponent_pos_of_large_core box
    ((c : ℂ) + (y : ℝ) * Complex.I) hlarge
  have hslackMass := hslack X hX mu hmuLo hmuHi hXscale L k box hq helig
  have hsize' := hsize X hX mu hmuHi hXscale L k box j hkind hover
  exact
    maynard_heathBrownBox_overweight_global_amplitude_le_nineEightyThree_div_thousand_elevenFifths
      box hready hpi hmuLo hmuHi hL hX hXscale hc hylo hyupper
        (perronRelevant_heathBrownBox_coreLower_le hrel) j hkind hover hsize'
        hslackMass hlarge

theorem eventually_maynard_perronRelevant_moderate_global_amplitude_le_997_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
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
    eventually_eight_pi_le_rpow_fourFifteenths,
    eventually_maynard_elevenFifths_long_box_amplitude_slack_ready,
    eventually_maynard_elevenFifths_moderate_factor_amplitude_ready]
      with T hready hpi hslack hsize
  intro X hX mu hmuLo hmuHi hXscale L hL k box helig hrel
    c y alpha beta hc hylo hyupper hbeta j hkind hwitness hlarge
  have hq : 1 ≤ box.q := heathBrownBox_log_exponent_pos_of_large_core box
    ((c : ℂ) + (y : ℝ) * Complex.I) hlarge
  have hslackMass := hslack X hX mu hmuLo hmuHi hXscale L k box hq helig
  have hsize' := hsize X hX mu hmuHi hXscale L k box beta hbeta j hkind hwitness
  exact maynard_heathBrownBox_moderate_global_amplitude_le_997_elevenFifths
    box hready hpi hmuLo hmuHi hL hX hXscale hc hylo hyupper
      (perronRelevant_heathBrownBox_coreLower_le hrel) hbeta j hkind hwitness
      hsize' hslackMass hlarge

+theorem sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent_elevenFifths
    {L X k : ℕ} {T : ℝ} (box : HeathBrownBoxChoice L X k) :
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i)) =
      heathBrownBoxTotalExponent L X k T box := by
  classical
  let q : HeathBrownBoxFactorIndex k box.m → ℕ :=
    heathBrownBoxFactorExponent box.a box.b box.q
  let u : Finset (HeathBrownBoxFactorIndex k box.m) :=
    Finset.univ.filter fun i => 1 ≤ q i
  have hu (i : HeathBrownBoxFactorIndex k box.m) : i ∈ u ↔ 1 ≤ q i := by
    simp [u]
  have hreindex := Finset.sum_subtype
    (F := Subtype.fintype fun i : HeathBrownBoxFactorIndex k box.m => 1 ≤ q i)
    u hu (fun i => dyadicLogExponent T (q i))
  calc
    (∑ i : PositiveHeathBrownBoxFactorIndex box,
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i)) =
        ∑ i ∈ u, dyadicLogExponent T (q i) := by
      simpa [PositiveHeathBrownBoxFactorIndex, q] using hreindex.symm
    _ = ∑ i : HeathBrownBoxFactorIndex k box.m, dyadicLogExponent T (q i) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _hi hiu
      have hqi : q i = 0 := by
        have : ¬ 1 ≤ q i := by simpa [u] using hiu
        omega
      simp [hqi, dyadicLogExponent]
    _ = heathBrownBoxTotalExponent L X k T box := by rfl

theorem eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_box_elevenFifths :
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
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) →
          0 ≤ c → T ≤ y → y ≤ 2 * T → 3 / 4 ≤ alpha →
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
    hmobius hsubHeight hc hylo hyupper halpha hcore
  have htotal : mu / 120 ≤ heathBrownBoxTotalExponent L X 60 T box := by
    simpa [IsHeathBrownBoxEligible, heathBrownBoxTotalExponent] using helig
  have hfilter :
      (Finset.univ.filter fun i : PositiveHeathBrownBoxFactorIndex box =>
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) =
        Finset.univ := by
    ext i
    simp [hsubHeight i]
  have hmass : mu / 120 ≤ ∑ i ∈ (Finset.univ.filter
      fun i : PositiveHeathBrownBoxFactorIndex box =>
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q i) < 1),
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) := by
    rw [hfilter]
    simpa using htotal.trans_eq
      (sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent_elevenFifths
        (T := T) box).symm
  have hsmall : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      1 ≤ dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q i) →
      ‖heathBrownBoxFactorValue L X 60 box
        ((c : ℂ) + (y : ℝ) * Complex.I) i‖ ≤
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ^
          (alpha - c) := by
    intro i hi
    exfalso
    have := hsubHeight i
    linarith
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

+theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_subHeight_box_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ {L X : ℕ} {mu N0 c alpha : ℝ},
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
          (∀ i : HeathBrownBoxFactorIndex 60 box.m,
            dyadicLogExponent T
              (heathBrownBoxFactorExponent box.a box.b box.q i) < 1) →
          0 ≤ c → 3 / 4 ≤ alpha →
          ∀ S : Finset ℕ, ∀ y : ℕ → ℝ,
            (∀ r ∈ S, T ≤ y r ∧ y r ≤ 2 * T) →
            (∀ r ∈ S,
              ((groupedDyadicLower
                (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                  (alpha - c) ≤
                ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                  ((c : ℂ) + (y r : ℝ) * Complex.I)‖) →
            ∃ color : ℕ → HeathBrownSelectionLabel L X 60,
              ∀ r ∈ S, (color r).1 = box ∧
                IsMaynardWindowRelevantSelectedCell
                  L X T mu N0 c (y r) alpha (color r) := by
  filter_upwards [
    eventually_exists_maynardWindowRelevantSelectedCell_label_of_subHeight_box_elevenFifths
  ] with T hpoint
  intro L X mu N0 c alpha hL hX hmuLo hmuHi hXscale box helig hrel
    hmobius hsubHeight hc halpha S y hy hcore
  classical
  have hchoose : ∀ r : ℕ, r ∈ S →
      ∃ label : HeathBrownSelectionLabel L X 60,
        label.1 = box ∧ IsMaynardWindowRelevantSelectedCell
          L X T mu N0 c (y r) alpha label := by
    intro r hr
    exact hpoint hL hX hmuLo hmuHi hXscale box helig hrel hmobius hsubHeight
      hc (hy r hr).1 (hy r hr).2 halpha (hcore r hr)
  choose selected hselected using hchoose
  let fallback : HeathBrownSelectionLabel L X 60 :=
    Classical.choice (nonempty_heathBrownSelectionLabel L X 60 (by norm_num))
  let color : ℕ → HeathBrownSelectionLabel L X 60 := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  refine ⟨color, ?_⟩
  intro r hr
  simpa [color, hr] using hselected r hr

+/-- Upper-height-free adjacent-optimizer reserve. The historical upper endpoint is absent from
every inequality in the proof. -/
theorem routeT_adjacent_optimizer_with_reserve_of_amplitude_le_997_unbounded
    {mu alpha : ℝ}
    (_hmuLo : 4 / 3 ≤ mu)
    (halphaLo : 3 / 4 ≤ alpha) (halphaHi : alpha ≤ 997 / 1000) :
    2 * (1 - alpha) / alpha + maynardLongGlobalAmplitudeDeficit / 100 ≤
          mu * (1 - alpha) ∨
      2 * (1 - alpha) / alpha + maynardLongGlobalAmplitudeDeficit / 100 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d := maynardLongGlobalAmplitudeDeficit
  let delta := 1 - alpha
  let q := 1 + routeTGapMomentNu - 2 * alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < (1 / 1000000 : ℝ) :=
    maynardLongGlobalAmplitudeDeficit_lt_one_millionth
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaLo
  have halphaOne : alpha ≤ 1 := by linarith
  have hdeltaLo : (3 / 1000 : ℝ) ≤ delta := by
    dsimp only [delta]
    linarith
  have hdelta0 : 0 ≤ delta := (by norm_num : (0 : ℝ) ≤ 3 / 1000).trans hdeltaLo
  have hqnonpos : q ≤ 0 := by
    dsimp only [q, routeTGapMomentNu]
    linarith
  by_cases hfirst : 2 + delta / 100 ≤ mu * alpha
  · left
    have hmargin : delta * delta / (100 * alpha) ≤
        mu * delta - 2 * delta / alpha := by
      have hgap : delta / 100 ≤ mu * alpha - 2 := by linarith
      have hscale := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ delta / alpha)
      calc
        delta * delta / (100 * alpha) = (delta / alpha) * (delta / 100) := by ring
        _ ≤ (delta / alpha) * (mu * alpha - 2) := hscale
        _ = mu * delta - 2 * delta / alpha := by field_simp [halpha0.ne']
    have hfixed : d / 100 ≤ delta * delta / (100 * alpha) := by
      have hdeltaSq : (9 / 1000000 : ℝ) ≤ delta * delta := by nlinarith
      have halphaD : alpha * d ≤ d := by
        have hmul := mul_le_mul_of_nonneg_right halphaOne hd.le
        simpa using hmul
      have hcore : d ≤ delta * delta / alpha := by
        rw [le_div_iff₀ halpha0]
        linarith
      calc
        d / 100 ≤ (delta * delta / alpha) / 100 :=
          div_le_div_of_nonneg_right hcore (by norm_num)
        _ = delta * delta / (100 * alpha) := by ring
    dsimp only [delta, d] at hmargin hfixed ⊢
    linarith
  · right
    have hmualpha : mu * alpha < 2 + delta / 100 := lt_of_not_ge hfirst
    have hmu : mu < (2 + delta / 100) / alpha := by
      rw [lt_div_iff₀ halpha0]
      simpa [mul_comm] using hmualpha
    have hqmul : ((2 + delta / 100) / alpha) * q ≤ mu * q :=
      mul_le_mul_of_nonpos_right hmu.le hqnonpos
    have hbase : 2 * delta / alpha + d / 100 ≤
        1 + ((2 + delta / 100) / alpha) * q := by
      have hqLower : -(1 / 2 : ℝ) ≤ q := by
        dsimp only [q, routeTGapMomentNu]
        linarith
      have hid : 1 + (2 / alpha) * q - 2 * delta / alpha =
          (delta - d) / alpha := by
        dsimp only [q, routeTGapMomentNu, delta, d]
        field_simp [halpha0.ne']
        ring
      have hperturb : (delta / (100 * alpha)) * q ≥
          -delta / (200 * alpha) := by
        have hmul := mul_le_mul_of_nonneg_left hqLower
          (by positivity : 0 ≤ delta / (100 * alpha))
        calc
          -delta / (200 * alpha) = (delta / (100 * alpha)) * (-(1 / 2 : ℝ)) := by ring
          _ ≤ (delta / (100 * alpha)) * q := hmul
      have hdDelta : d ≤ delta := by linarith
      have hroom : d / 100 + delta / (200 * alpha) ≤ (delta - d) / alpha := by
        have halphaD : alpha * d ≤ d := by
          have hmul := mul_le_mul_of_nonneg_right halphaOne hd.le
          simpa using hmul
        have hscaledD : alpha * (d / 100) ≤ d / 100 := by nlinarith
        have hsmallCore : d + d / 100 + delta / 200 ≤ delta := by linarith
        rw [le_div_iff₀ halpha0]
        calc
          (d / 100 + delta / (200 * alpha)) * alpha =
              alpha * (d / 100) + delta / 200 := by field_simp [halpha0.ne']
          _ ≤ d / 100 + delta / 200 := by
            simpa [add_comm] using add_le_add_right hscaledD (delta / 200)
          _ ≤ delta - d := by linarith
      have hsplit : ((2 + delta / 100) / alpha) * q =
          (2 / alpha) * q + (delta / (100 * alpha)) * q := by ring
      calc
        2 * delta / alpha + d / 100 =
            1 + (2 / alpha) * q - (delta - d) / alpha + d / 100 := by
          linarith [hid]
        _ ≤ 1 + (2 / alpha) * q - delta / (200 * alpha) := by linarith
        _ ≤ 1 + (2 / alpha) * q + (delta / (100 * alpha)) * q := by
          have hh := add_le_add_left hperturb (1 + (2 / alpha) * q)
          convert hh using 1 <;> ring
        _ = 1 + ((2 + delta / 100) / alpha) * q := by
          rw [hsplit]
          ring
    dsimp only [q] at hqmul
    have hqmul' : 1 + ((2 + delta / 100) / alpha) *
        (1 + routeTGapMomentNu - 2 * alpha) ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) :=
      by simpa [add_comm] using add_le_add_left hqmul 1
    have htarget := hbase.trans (by simpa only [q] using hqmul')
    simpa [delta, d] using htarget

/-- The shifted middle-strip scalar budget has no upper-height restriction. -/
theorem routeT_middle_shifted_adjacent_with_cost_first_or_second_unbounded
    {mu alpha : ℝ}
    (hmuLo : 4 / 3 ≤ mu)
    (halphaLo : 19 / 25 ≤ alpha) (halphaHi : alpha ≤ 997 / 1000) :
    2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 1000 ≤ mu * (1 - alpha) ∨
      2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 1000 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let alpha0 : ℝ := maynardMiddleReferenceAmplitude alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have halphaThree : 3 / 4 ≤ alpha := by linarith
  have ha0Range := maynardMiddleReferenceAmplitude_range halphaLo halphaHi
  have ha0pos : 0 < alpha0 := lt_of_lt_of_le (by norm_num) ha0Range.1
  have halphapos : 0 < alpha := lt_of_lt_of_le (by norm_num) halphaThree
  have ha0le : alpha0 ≤ alpha := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    linarith
  have hprod : (9 / 16 : ℝ) ≤ alpha * alpha0 := by
    have h := mul_le_mul halphaThree ha0Range.1 (by norm_num : (0 : ℝ) ≤ 3 / 4)
      halphapos.le
    norm_num at h ⊢
    exact h
  have hshift : alpha - alpha0 = d / 100000 := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    ring
  have hfrac : 2 * (alpha - alpha0) / (alpha * alpha0) ≤ d / 1000 := by
    rw [div_le_iff₀ (mul_pos halphapos ha0pos)]
    rw [hshift]
    have hmul := mul_le_mul_of_nonneg_left hprod hd.le
    nlinarith
  have hcapIdentity :
      2 * (1 - alpha0) / alpha0 =
        2 * (1 - alpha) / alpha +
          2 * (alpha - alpha0) / (alpha * alpha0) := by
    field_simp [halphapos.ne', ha0pos.ne']
    ring
  have hcap :
      2 * (1 - alpha0) / alpha0 + d / 1000 ≤
        2 * (1 - alpha) / alpha + d / 100 := by
    rw [hcapIdentity]
    nlinarith
  rcases routeT_adjacent_optimizer_with_reserve_of_amplitude_le_997_unbounded
      hmuLo halphaThree halphaHi with hfirst | hsecond
  · left
    simpa only [alpha0, d] using hcap.trans hfirst
  · right
    simpa only [alpha0, d] using hcap.trans hsecond

/-- Through the raw analytic range mu <= 8, every nonempty fixed-label middle fibre reaches
one Route-T receiver. This removes the historical 19/9 ceiling from both selected branches. -/
theorem eventually_maynardWindowRelevantSelectedCell_middle_fibre_first_or_second_through_eight :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 8 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60),
      ∀ (S : Finset ℕ), S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (mu * (1 - alpha) - maynardLongGlobalAmplitudeDeficit / 2000) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            maynardLongGlobalAmplitudeDeficit / 2000) := by
  filter_upwards [eventually_maynardWindowRelevantSelectedCell_middle_adjacent_count,
    eventually_maynardWindowRelevantSelectedCell_middle_overweight_count,
    eventually_gt_atTop (1 : ℝ)] with T hadj hover hT
  intro L X K mu N0 c alpha delta hmuLo hmuEight hc halphaLo halphaHi hdelta
    label S hSne hS lam hgap hband hselection
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  by_cases hbetaOne : beta < 1
  · have hraw := hadj hmuLo hmuEight hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaOne) S hSne hS lam hgap hband hselection
    rcases routeT_middle_shifted_adjacent_with_cost_first_or_second_unbounded
        hmuLo halphaLo halphaHi with hfirst | hsecond
    · left
      have hexp :
          2 * (1 - maynardMiddleReferenceAmplitude alpha) /
              maynardMiddleReferenceAmplitude alpha + d / 100000 ≤
            mu * (1 - alpha) - d / 2000 := by
        dsimp only [d] at hfirst ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      exact hraw.trans (mul_le_mul_of_nonneg_left hpow hHF0)
    · right
      have hexp :
          2 * (1 - maynardMiddleReferenceAmplitude alpha) /
              maynardMiddleReferenceAmplitude alpha + d / 100000 ≤
            1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000 := by
        dsimp only [d] at hsecond ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      exact hraw.trans (mul_le_mul_of_nonneg_left hpow hHF0)
  · have hbetaLo : 1 ≤ beta := le_of_not_gt hbetaOne
    have hraw := hover hmuLo hmuEight hc halphaLo halphaHi hdelta label
      (by simpa only [beta] using hbetaLo) S hSne hS lam hgap hband hselection
    obtain ⟨r0, hr0⟩ := hSne
    rcases hselection r0 hr0 with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, hbetaUpper,
        _hlength, _hlarge, hbranch⟩
    have hbetaHi : beta ≤ 1 + mu / 60 := by
      have hbetaUpper' : beta < 1 + 2 * (mu / 120) := by
        simpa only [beta] using hbetaUpper
      linarith
    have halpha983 : alpha ≤ 983 / 1000 := by
      rcases hbranch with hsmall | hmoderate | hoverweight
      · have hsmall' : beta ≤ 5 / 12 := by
          simpa only [IsMaynardSelectedCellBranch, beta] using hsmall
        linarith
      · have hmoderate' : beta < 1 := by
          simpa only [IsMaynardSelectedCellBranch, beta] using hmoderate.2.1
        exact (hbetaOne hmoderate').elim
      · simpa only [IsMaynardSelectedCellBranch, beta] using hoverweight.2.1
    rcases routeT_overweight_literal_cap_with_reserve_first_or_second_unbounded
        hmuLo (by linarith : 3 / 4 ≤ alpha) halpha983 hbetaHi with
      hfirst | hsecond
    · left
      have hexp : beta * (2 - 2 * alpha) + d / 100000 ≤
          mu * (1 - alpha) - d / 2000 := by
        dsimp only [d] at hfirst ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      have hraw' : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (beta * (2 - 2 * alpha) + d / 100000) := by
        simpa only [beta, d] using hraw
      exact hraw'.trans (mul_le_mul_of_nonneg_left hpow hHF0)
    · right
      have hexp : beta * (2 - 2 * alpha) + d / 100000 ≤
          1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000 := by
        dsimp only [d] at hsecond ⊢
        linarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hexp
      have hraw' : (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (beta * (2 - 2 * alpha) + d / 100000) := by
        simpa only [beta, d] using hraw
      exact hraw'.trans (mul_le_mul_of_nonneg_left hpow hHF0)



end RHTower.Sieve

end RHTower.Sieve

end RHTower.Sieve
