import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightZetaLogExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardDerivativeCountDuality
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleFibreCount
import GaloisForLFunctions.RHTower.Sieve.MaynardUnboundedHeightScalar
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellFibreMontgomery
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalMiddleHuxley
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalMontgomery
import GaloisForLFunctions.RHTower.Sieve.MaynardUpperSeamSelectedCell
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellGlobalCount
import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusEndpoint
import GaloisForLFunctions.RHTower.Sieve.RouteTEndpointAmplitudeExclusion
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellRouteTAllAmplitudeCount

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

theorem sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent_elevenFifths
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

theorem eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_subHeight_box_elevenFifths :
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

/-- Upper-height-free adjacent-optimizer reserve. The historical upper endpoint is absent from
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



/-- The wide-cell tuned Montgomery scalar law survives exactly through Route T's new
height ceiling mu <= 11/5. -/
theorem routeT_wide_tunedMontgomery_exponents_with_polylog_le_second_elevenFifths
    {mu alpha beta r : ℝ}
    (_hmuLo : 4 / 3 ≤ mu) (hmuHi : mu ≤ 11 / 5)
    (halphaLo : (1 + routeTGapMomentNu) / 2 ≤ alpha)
    (halphaHi : alpha ≤ 19 / 25)
    (_hbetaLo : mu / 120 ≤ beta) (hbetaHi : beta < 1 + mu / 60)
    (hrLo : 4 / 5 ≤ r) (hrHi : r < 4 / 5 + beta) :
    r * (2 - 2 * alpha) + 1 / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) ∧
      1 + r * (1 - 2 * alpha) + 1 / 100 ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let q : ℝ := 1 + routeTGapMomentNu - 2 * alpha
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have hdsmall : d < 1 / 100 :=
    maynardLongGlobalAmplitudeDeficit_lt_one_hundredth
  have hq : q ≤ 0 := by
    dsimp only [q]
    linarith
  have hmuq : (11 / 5 : ℝ) * q ≤ mu * q :=
    mul_le_mul_of_nonpos_right hmuHi hq
  have hbeta : beta < 311 / 300 := by linarith
  have hr : r < 551 / 300 := by linarith
  have halphaLower : 149 / 200 < alpha := by
    dsimp only [routeTGapMomentNu] at halphaLo
    linarith
  have hwidth : r * (2 - 2 * alpha) + 1 / 100 ≤
      1 + (11 / 5 : ℝ) * q := by
    dsimp only [q, routeTGapMomentNu, d]
    nlinarith
  have hheight : 1 + r * (1 - 2 * alpha) + 1 / 100 ≤
      1 + (11 / 5 : ℝ) * q := by
    have hcoef : 1 - 2 * alpha < 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_right hrLo hcoef.le
    dsimp only [q, routeTGapMomentNu, d]
    nlinarith
  dsimp only [q] at hmuq
  exact ⟨hwidth.trans (by linarith), hheight.trans (by linarith)⟩


theorem exists_maynardWindowRelevantSelectedCell_fibre_tuned_montgomery_elevenFifths
    (L X : ℕ) {T mu N0 c alpha delta : ℝ}
    (hT : 1 < T) (hc : 0 ≤ c)
    (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 11 / 5)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hSne : S.Nonempty)
    (lam : ℕ → ℝ) (hdelta : 0 < delta) (hdeltaHi : delta ≤ 2 * T)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T)
    (hselection : ∀ r ∈ S,
      IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 90 ∧
      let beta := maynardSubHeightSelectedExponent T label
      4 / 5 ≤ (ell : ℝ) * beta ∧
      (ell : ℝ) * beta < 4 / 5 + beta ∧
      IsMaynardSelectedMontgomeryBound (3 * T) c alpha delta label S ell := by
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hrel, _hcore, hlabel, _husub, hbetaT, _hbetaHi,
      hlength, _hlarge, _hbranch⟩
  let beta := maynardSubHeightSelectedExponent T label
  have hbetaLo : 1 / 90 ≤ beta := by
    have : mu / 120 ≤ beta := by simpa [beta] using hbetaT
    linarith
  obtain ⟨ell, hell, hell90, hcross, hover⟩ :=
    exists_maynard_wide_tuned_raise_multiplier hbetaLo
      (by norm_num : (0 : ℝ) < 4 / 5) (by norm_num : (4 / 5 : ℝ) ≤ 1)
  let A : ℝ :=
    (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ)
  let Y : ℝ :=
    (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)
  have hAeq : A = T ^ beta := by
    simpa [A, beta] using hlength
  have hlarge : ∀ r ∈ S,
      Y ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖ := by
    intro r hr
    rcases hselection r hr with
      ⟨_helig, _hrel, _hcore, _hlabel, _husub, _hbetaT, _hbetaHi,
        _hlength, hbaseLarge, _hbranch⟩
    have hbase : A ^ (alpha - c) ≤
        ‖∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
      simpa [A] using hbaseLarge
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ A) _)
      hbase ell
    have hrewrite : Y ^ (alpha - c) = (A ^ (alpha - c)) ^ ell := by
      dsimp only [Y]
      calc
        ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
            (alpha - c)) = A ^ ((ell : ℝ) * (alpha - c)) := by
          rw [Nat.cast_pow, show
            (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ) = A by rfl,
            ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = A ^ ((alpha - c) * (ell : ℝ)) := by congr 1; ring
        _ = (A ^ (alpha - c)) ^ (ell : ℝ) := by
          rw [Real.rpow_mul (by positivity : 0 ≤ A)]
        _ = (A ^ (alpha - c)) ^ ell := Real.rpow_natCast _ _
    calc
      Y ^ (alpha - c) = (A ^ (alpha - c)) ^ ell := hrewrite
      _ ≤ ‖∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i)))
                ((c : ℂ) + (lam r : ℝ) * Complex.I)‖ ^ ell := hpow
      _ = ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i)))
                ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖ := by rw [norm_pow]
  have hMontBand : ∀ r ∈ S,
      delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ 3 * T := by
    intro r hr
    have hrband := hband r hr
    constructor <;> linarith
  have hYpos : 0 < Y := by
    dsimp only [Y]
    exact_mod_cast pow_pos (Nat.zero_lt_of_lt
      (one_le_groupedDyadicLower (heathBrownSelectedExponent label))) ell
  have hMont := montgomery_heathBrown_selected_raised_large_values_finset
    label ell hell hlabel hc
      (show heathBrownSelectedRaisedEnergy label ell ≤
          heathBrownSelectedRaisedEnergy label ell from le_rfl)
      hdelta (by linarith : 0 ≤ 3 * T)
      (Real.rpow_pos_of_pos hYpos (alpha - c))
      hgap hMontBand hlarge
  refine ⟨ell, hell, hell90, ?_, ?_, ?_⟩
  · simpa [beta] using hcross
  · simpa [beta] using hover
  · simpa [IsMaynardSelectedMontgomeryBound, Y] using hMont

set_option maxHeartbeats 1000000 in
/-- **Literal lower-strip selected-cell count.**  First crossing of `T^(4/5)`, exact two-term
Montgomery cancellation, and one fixed-polylog absorption put every selected-cell fibre with
`3/4 ≤ alpha ≤ 19/25` directly inside Route T's second alternative.  The theorem already
allows an external `T^(1/400)` multiplier for the later finite-label sum. -/
theorem eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude_elevenFifths :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      0 ≤ c → 3 / 4 ≤ alpha → alpha ≤ 19 / 25 →
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
    linarith [Real.log_nonneg hWY1]
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
    have hlog0 : 0 ≤ Real.log (W * Y) := Real.log_nonneg hWY1
    have hfirst : 1 / delta ≤ HF * B0 := by
      exact honeDivHF.trans (by
        calc
          HF = HF * 1 := by ring
          _ ≤ HF * B0 := mul_le_mul_of_nonneg_left hB01 hHFpos.le)
    have hsecond : 2 * Real.log (W * Y) ≤ 2 * HF * B0 := by
      have hlogB : Real.log (W * Y) ≤ B0 := by
        dsimp only [B0]
        linarith
      have := hlogB.trans (by
        calc
          B0 = 1 * B0 := by ring
          _ ≤ HF * B0 := mul_le_mul_of_nonneg_right hHF1 hB00)
      linarith
    nlinarith
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
    have hreplace :
        W * (1 / delta + 2 * Real.log (W * Y)) * B0 ^ e *
            (3 * U + W * (4 * B0) * V) ≤
          W * (3 * HF * B0) * B0 ^ e *
            (3 * U + W * (4 * B0) * V) := by
      have htail0 : 0 ≤ 3 * U + W * (4 * B0) * V :=
        add_nonneg (mul_nonneg (by norm_num) hU0)
          (mul_nonneg (mul_nonneg hW0 (mul_nonneg (by norm_num) hB00)) hV0)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdeltaLog hW0)
          (pow_nonneg hB00 e)) htail0
    have hcoef : 9 * W * HF * B0 ^ (e + 1) ≤
        12 * W ^ 2 * HF * B0 ^ (e + 2) := by
      have hpow : B0 ^ (e + 1) ≤ B0 ^ (e + 2) :=
        pow_le_pow_right₀ hB01 (by omega)
      have hWsqCore : W ≤ W ^ 2 := by
        calc
          W = W * 1 := by ring
          _ ≤ W * W := mul_le_mul_of_nonneg_left hW1 hW0
          _ = W ^ 2 := by ring
      have hWsq : 9 * W ≤ 12 * W ^ 2 := by
        calc
          9 * W ≤ 12 * W := mul_le_mul_of_nonneg_right (by norm_num) hW0
          _ ≤ 12 * W ^ 2 := mul_le_mul_of_nonneg_left hWsqCore (by norm_num)
      calc
        9 * W * HF * B0 ^ (e + 1) ≤
            12 * W ^ 2 * HF * B0 ^ (e + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hWsq hHFpos.le)
            (pow_nonneg hB00 _)
        _ ≤ 12 * W ^ 2 * HF * B0 ^ (e + 2) := by
          exact mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg W)) hHFpos.le)
    calc
      (S.card : ℝ) ≤
          W * (1 / delta + 2 * Real.log (W * Y)) * B0 ^ e *
            (3 * U + W * (4 * B0) * V) := hraw'
      _ ≤ W * (3 * HF * B0) * B0 ^ e *
            (3 * U + W * (4 * B0) * V) := hreplace
      _ = (9 * W * HF * B0 ^ (e + 1)) * U +
          (12 * W ^ 2 * HF * B0 ^ (e + 2)) * V := by
        rw [pow_succ, show e + 2 = (e + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ (12 * W ^ 2 * HF * B0 ^ (e + 2)) * U +
          (12 * W ^ 2 * HF * B0 ^ (e + 2)) * V := by
        exact add_le_add (mul_le_mul_of_nonneg_right hcoef hU0) le_rfl
      _ = HF * (12 * W ^ 2 * B0 ^ (e + 2)) * (U + V) := by ring
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
    routeT_wide_tunedMontgomery_exponents_with_polylog_le_second_elevenFifths
      hmuLo hmuHi
      (by linarith [routeTGapMomentNu_lt_half]) halphaHi
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

/-- Complete degree-60 label entropy costs at most `T^(1/400)`. -/
theorem eventually_maynardUpperSeamLabelCost_absorbed_four_hundred :
    ∀ᶠ T : ℝ in atTop,
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 ≤
        T ^ (1 / 400 : ℝ) := by
  let C : ℝ := maynardUpperSeamLabelPolylogConstant
  have hC : 0 < C := by
    dsimp only [C, maynardUpperSeamLabelPolylogConstant]
    positivity
  have heps : (0 : ℝ) < 1 / 400 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 120 heps).def
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (0 : ℝ)] with T hsmall hlogT hT
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow : 0 < T ^ (1 / 400 : ℝ) := Real.rpow_pos_of_pos hT _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.log T ^ (120 : ℝ)),
    abs_of_nonneg hTpow.le] at hsmall
  have hlogpow : Real.log T ^ (120 : ℝ) = Real.log T ^ (120 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hlogpow] at hsmall
  have hscaled := mul_le_mul_of_nonneg_left hsmall hC.le
  have hcancel : C * (1 / (2 * C)) = 1 / 2 := by
    field_simp [hC.ne']
  have hhalf : (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) ≤
      T ^ (1 / 400 : ℝ) := by nlinarith
  change C * Real.log T ^ 120 ≤ T ^ (1 / 400 : ℝ)
  calc
    C * Real.log T ^ 120 ≤ C * (1 / (2 * C) * T ^ (1 / 400 : ℝ)) := hscaled
    _ = (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
      rw [← mul_assoc, hcancel]
    _ ≤ T ^ (1 / 400 : ℝ) := hhalf

/-- **Global lower-strip Route-T second alternative.** -/
theorem eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      0 ≤ c → 3 / 4 ≤ alpha → alpha ≤ 19 / 25 →
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
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude_elevenFifths,
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

/-- **Global middle-strip Route-T dichotomy.**  Literal selected-cell coloring, including the
unique overweight cell, satisfies one receiver with a residual `d/4000` power margin. -/
theorem eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle_elevenFifths :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (mu * (1 - alpha) - maynardLongGlobalAmplitudeDeficit / 4000) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            maynardLongGlobalAmplitudeDeficit / 4000) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_middle_fibre_first_or_second_through_eight,
    eventually_maynardMiddleFixedLogCost_absorbed maynardUpperSeamLabelPolylogConstant
      (by
        dsimp only [maynardUpperSeamLabelPolylogConstant]
        positivity)
      120 4000 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hfibre hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaHi hdelta S hS lam hgap hband color hcolor
  classical
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B1 : ℝ := maynardHarmonicFactor K delta *
    T ^ (mu * (1 - alpha) - d / 4000)
  let B2 : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 4000)
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
  have hlabelAbsorbedRaw := hlabelCost 1 0 (by norm_num)
    (by exact_mod_cast one_le_pow₀ (n := 90) hT.le)
    (by omega : 0 ≤ maynardMontgomeryFixedPolylogExponentBound)
  have hlabelAbsorbed :
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 ≤ T ^ (d / 4000) := by
    norm_num [d] at hlabelAbsorbedRaw ⊢
    exact hlabelAbsorbedRaw
  have hnlabels : nlabels ≤ T ^ (d / 4000) := hlabelRaw.trans hlabelAbsorbed
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hpowMerge1 :
      T ^ (d / 4000) *
          (maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - d / 2000)) = B1 := by
    dsimp only [B1]
    rw [mul_left_comm, ← Real.rpow_add hT0]
    congr 1
    ring
  have hpowMerge2 :
      T ^ (d / 4000) *
          (maynardHarmonicFactor K delta *
            T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000)) =
        B2 := by
    dsimp only [B2]
    rw [mul_left_comm, ← Real.rpow_add hT0]
    congr 1
    ring
  have hfibres : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B1 ∨
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B2 := by
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
      rcases hfibre hmuLo (by linarith : mu ≤ 8) hc halphaLo halphaHi hdelta label
          Sf hSf hSfRange lam hgap hSfBand hSfSelection with hfirst | hsecond
      · left
        calc
          nlabels * (Sf.card : ℝ) ≤ T ^ (d / 4000) *
              (maynardHarmonicFactor K delta *
                T ^ (mu * (1 - alpha) - d / 2000)) :=
            mul_le_mul hnlabels hfirst (Nat.cast_nonneg _)
              (Real.rpow_nonneg hT0.le _)
          _ = B1 := hpowMerge1
      · right
        calc
          nlabels * (Sf.card : ℝ) ≤ T ^ (d / 4000) *
              (maynardHarmonicFactor K delta *
                T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 2000)) :=
            mul_le_mul hnlabels hsecond (Nat.cast_nonneg _)
              (Real.rpow_nonneg hT0.le _)
          _ = B2 := hpowMerge2
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      left
      simpa only [Sf, hzero, Nat.cast_zero, mul_zero] using hB10
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  by_cases htargets : B1 ≤ B2
  · right
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B2 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B2 :=
          Finset.sum_le_sum fun label _ => (hfibres label).elim
            (fun h => h.trans htargets) (fun h => h)
        _ = nlabels * B2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B2, d] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum
  · left
    have htargets' : B2 ≤ B1 := le_of_not_ge htargets
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B1 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B1 :=
          Finset.sum_le_sum fun label _ => (hfibres label).elim
            (fun h => h) (fun h => h.trans htargets')
        _ = nlabels * B1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B1, d] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

/-- **Global exact Maynard dichotomy for literal selected-cell colors.** -/
theorem eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_elevenFifths (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu → (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      1 / 2 ≤ c → 997 / 1000 < alpha →
      alpha ≤ 1 - routeTEndpointGlobalDeficit A T →
      0 < delta →
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      ∀ (color : ℕ → HeathBrownSelectionLabel L X 60),
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha (color r)) →
      (S.card : ℝ) ≤
          maynardHarmonicFactor K delta *
            T ^ (mu * (1 - alpha) - routeTEndpointGlobalDeficit A T / 200) ∨
        (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
          T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) -
            routeTEndpointGlobalDeficit A T / 200) := by
  filter_upwards [
    eventually_maynardWindowRelevantSelectedCell_scaled_fibre_first_or_second_unbounded A,
    eventually_maynardOptimizerFixedLogCost_absorbed A maynardUpperSeamLabelPolylogConstant
      (by
        dsimp only [maynardUpperSeamLabelPolylogConstant]
        positivity)
      120 400 (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hscaled hlabelCost hlogT hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo halphaEndpoint hdelta S hS lam hgap hdiam color hcolor
  classical
  let d := routeTEndpointGlobalDeficit A T
  let nlabels : ℝ := Fintype.card (HeathBrownSelectionLabel L X 60)
  let B1 : ℝ := maynardHarmonicFactor K delta *
    T ^ (mu * (1 - alpha) - d / 200)
  let B2 : ℝ := maynardHarmonicFactor K delta *
    T ^ (1 + mu * (1 + routeTGapMomentNu - 2 * alpha) - d / 200)
  have hd : 0 < d := routeTEndpointGlobalDeficit_pos A (by linarith)
  have hT0 : 0 < T := by linarith
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
  have hlabelAbsorbedRaw := hlabelCost 1 0 (by norm_num)
    (by exact_mod_cast hT.le) (by omega : 0 ≤ maynardFixedPolylogExponentBound)
  have hlabelAbsorbed :
      maynardUpperSeamLabelPolylogConstant * (Real.log T) ^ 120 ≤ T ^ (d / 400) := by
    norm_num [d] at hlabelAbsorbedRaw ⊢
    exact hlabelAbsorbedRaw
  have hnlabels : nlabels ≤ T ^ (d / 400) := hlabelRaw.trans hlabelAbsorbed
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
      (Real.rpow_nonneg hT0.le _)
  have hfibre : ∀ label : HeathBrownSelectionLabel L X 60,
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B1 ∨
      nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B2 := by
    intro label
    let Sf : Finset ℕ := S.filter fun r => color r = label
    by_cases hSf : Sf.Nonempty
    · have hSfS : Sf ⊆ S := Finset.filter_subset _ _
      have hSfRange : Sf ⊆ Finset.range K := hSfS.trans hS
      have hSfDiam : ∀ r ∈ Sf, ∀ s ∈ Sf, |lam s - lam r| ≤ T := by
        intro r hr s hs
        exact hdiam r (hSfS hr) s (hSfS hs)
      have hSfSelection : ∀ r ∈ Sf,
          IsMaynardWindowRelevantSelectedCell
            L X T mu N0 c (lam r) alpha label := by
        intro r hr
        have hrS := hSfS hr
        have hrcolor : color r = label := (Finset.mem_filter.mp hr).2
        simpa only [hrcolor] using hcolor r hrS
      simpa only [Sf, B1, B2] using
        hscaled hmuLo hc halphaLo halphaEndpoint hdelta
          nlabels hnlabelsPos.le hnlabels label Sf hSf hSfRange lam hgap
          hSfDiam hSfSelection
    · have hzero : Sf.card = 0 :=
        Finset.card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hSf)
      left
      simpa only [Sf, hzero, Nat.cast_zero, mul_zero] using hB10
  have hcardCast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  by_cases htargets : B1 ≤ B2
  · right
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B2 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B2 :=
          Finset.sum_le_sum fun label _ => (hfibre label).elim
            (fun h => h.trans htargets) (fun h => h)
        _ = nlabels * B2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B2] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum
  · left
    have htargets' : B2 ≤ B1 := le_of_not_ge htargets
    have hsum : nlabels * (S.card : ℝ) ≤ nlabels * B1 := by
      rw [hcardCast, mul_sum]
      calc
        ∑ label : HeathBrownSelectionLabel L X 60,
            nlabels * (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
            ∑ _label : HeathBrownSelectionLabel L X 60, B1 :=
          Finset.sum_le_sum fun label _ => (hfibre label).elim
            (fun h => h) (fun h => h.trans htargets')
        _ = nlabels * B1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simpa only [B1] using (mul_le_mul_iff_right₀ hnlabelsPos).mp hsum

/-- The canonical cutoff is so short that every fourth power of a dyadic Möbius length fits below
half the endpoint height.  The coarse exponent `1/8` deliberately avoids any fragile decimal
arithmetic: `mu/60 <= 19/540 < 1/8`. -/
theorem fourth_power_le_half_height_of_maynard_cutoff_elevenFifths
    {T mu N : ℝ} (hT : 4 ≤ T) (hmu : mu ≤ 11 / 5)
    (hN : 0 ≤ N) (hcut : N ≤ T ^ (mu / 60)) :
    N ^ (4 : ℕ) ≤ T / 2 := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hexp : mu / 60 ≤ 1 / 8 := by linarith
  have hroot : N ≤ T ^ (1 / 8 : ℝ) :=
    hcut.trans (Real.rpow_le_rpow_of_exponent_le hT1 hexp)
  have hpow : N ^ (4 : ℕ) ≤ (T ^ (1 / 8 : ℝ)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ hN hroot 4
  have hcollapse : (T ^ (1 / 8 : ℝ)) ^ (4 : ℕ) = T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    norm_num
  rw [hcollapse] at hpow
  have hroot2 : 2 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqrtSq : (Real.sqrt T) ^ (2 : ℕ) = T := Real.sq_sqrt hT0.le
  have hsqrtHalf : Real.sqrt T ≤ T / 2 := by nlinarith
  rw [← Real.sqrt_eq_rpow] at hpow
  exact hpow.trans hsqrtHalf

/-- **Unconditional endpoint-long Möbius exclusion.**  The constants are the literal constants
delivered by the Route-T reciprocal contour.  Every positive-length Möbius coordinate above the
Maynard endpoint threshold has a common amplitude deficit at all sufficiently large heights. -/
theorem exists_eventually_maynard_endpoint_moebius_amplitude_deficit_elevenFifths :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ (L X : ℕ), 1 ≤ L → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
          (L : ℝ) ≤ T ^ (mu / 60) →
          ∀ box : HeathBrownBoxChoice L X 60,
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            ∀ j : PositiveHeathBrownBoxFactorIndex box,
              heathBrownBoxFactorKind 60 box.m j = .moebius →
              (∑ i : PositiveHeathBrownBoxFactorIndex box,
                  dyadicLogExponent T
                    (heathBrownBoxFactorExponent box.a box.b box.q i)) /
                    (40 * 60 : ℕ) ≤
                dyadicLogExponent T
                  (heathBrownBoxFactorExponent box.a box.b box.q j) →
              ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
                0 < ‖heathBrownBoxFactorValue L X 60 box
                  ((c : ℂ) + (y : ℝ) * Complex.I) j‖ →
                maynardAmplitude c
                    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
                    ‖heathBrownBoxFactorValue L X 60 box
                      ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
                  1 - routeTEndpointMoebiusDeficit A delta T := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hmain⟩ :=
    exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  filter_upwards [eventually_routeT_endpoint_moebius_coefficient_ready
      A C C' delta hC hC' hdelta,
    eventually_ge_atTop (4 : ℝ)] with T hready hT4
  intro L X hL mu hmu_lo hmu_hi hcut box helig j hkind hlong c y hc hylo hyhi hV
  let q : ℕ := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let U : ℝ := |y| / 2
  let S : ℝ := |y| + U
  have hT : 1 < T := by linarith
  have hy0 : 0 < y := lt_trans zero_lt_one (hT.trans_le hylo)
  have hq : 1 ≤ q := by simpa only [q] using j.property
  have hNL : 2 ^ q ≤ L := by
    dsimp only [q]
    exact box.moebius_factor_pow_le_cutoff hL j hkind
  have hNcut : N ≤ T ^ (mu / 60) := by
    have hreal : (((2 ^ q : ℕ) : ℝ)) ≤ (L : ℝ) := by exact_mod_cast hNL
    exact hreal.trans hcut
  have hNU : N ^ (4 : ℕ) ≤ U := by
    have hpow := fourth_power_le_half_height_of_maynard_cutoff_elevenFifths
      hT4 hmu_hi (by dsimp only [N]; positivity) hNcut
    dsimp only [U]
    rw [abs_of_pos hy0]
    linarith
  have hlongTotal :
      heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
        dyadicLogExponent T q := by
    rw [← sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
    simpa only [q] using hlong
  have hNroot : T ^ (1 / 216000 : ℝ) ≤ N := by
    simpa only [N, q] using
      dyadic_length_ge_maynard_endpoint_root box hT hmu_lo helig j hlongTotal
  have hroot0 : 0 < T ^ (1 / 216000 : ℝ) := by positivity
  have hlogN : (1 / 216000 : ℝ) * Real.log T ≤ Real.log N := by
    have hlog := Real.log_le_log hroot0 hNroot
    rwa [Real.log_rpow (by linarith : 0 < T)] at hlog
  have hready' :
      2 * Real.log
          (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
        (routeTContourShift A delta S / 3) * (Real.log T / 216000) ∧
      routeTContourShift A delta (3 * T) ≤ routeTContourShift A delta S ∧
      routeTInverseBaseHeight + U ≤ |y| := by
    simpa only [U, S] using hready y hylo hyhi
  rcases hready' with ⟨hcost, hcommon, hsep⟩
  have hshift0 : 0 ≤ routeTContourShift A delta S / 3 := by
    exact div_nonneg (routeTContourShift_pos (A := A) (T := S) hdelta).le (by norm_num)
  have hlogN' : Real.log T / 216000 ≤ Real.log N := by
    calc
      Real.log T / 216000 = (1 / 216000 : ℝ) * Real.log T := by ring
      _ ≤ Real.log N := hlogN
  have hsize :
      2 * Real.log
          (2 * routeTMoebiusPowerConstant C C' * routeTContourEdgeBound A S) ≤
        (routeTContourShift A delta S / 3) * Real.log N :=
    hcost.trans (mul_le_mul_of_nonneg_left hlogN' hshift0)
  have hatom := hmain L q c y U hq hNL hc hNU hsep
  have hlocal := maynard_moebius_amplitude_le_routeTEndpointDeficit
    (A := A) (C := C) (C' := C') (delta := delta) (T := T) (S := S)
      hC hC' hq (by rfl) hsize hcommon (by
        simpa only [heathBrownBoxFactorValue, hkind, q, heathBrownFactorBase] using hV) (by
        simpa only [q, S] using hatom)
  simpa only [heathBrownBoxFactorValue, hkind, q, heathBrownFactorBase] using hlocal

/-- Exact endpoint-long zeta/log factor theorem at fixed order `216002`. -/
theorem maynard_heathBrown_endpoint_zeta_log_amplitude_le_one_sub_half_elevenFifths
    {L X : ℕ} (box : HeathBrownBoxChoice L X 60)
    (j : HeathBrownBoxFactorIndex 60 box.m)
    (hkind : heathBrownBoxFactorKind 60 box.m j = .zeta ∨
      heathBrownBoxFactorKind 60 box.m j = .log)
    (hX : 1 ≤ X) {T mu c y : ℝ}
    (hT : 1 < T) (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 11 / 5)
    (hXscale : (X : ℝ) ≤ T ^ mu)
    (helig : IsHeathBrownBoxEligible L X 60 T (mu / 120) box)
    (hlong : heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
      dyadicLogExponent T
        (heathBrownBoxFactorExponent box.a box.b box.q j))
    (hc : 0 ≤ c) (hylo : T ≤ y) (hyupper : y ≤ 2 * T)
    (hpi : 8 * Real.pi ≤ T ^ (4 / 15 : ℝ))
    (hfactorial : ((Nat.factorial 216001 : ℕ) : ℝ) ≤ T ^ (1 / 216000 : ℝ))
    (hsize : 2 * Real.log
        (heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind 60 box.m j)
          (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
      maynardEndpointDerivativeDeficit *
        Real.log
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)))
    (hV : 0 < ‖heathBrownBoxFactorValue L X 60 box
      ((c : ℂ) + (y : ℝ) * Complex.I) j‖) :
    maynardAmplitude c
        (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
        ‖heathBrownBoxFactorValue L X 60 box
          ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
      1 - maynardEndpointDerivativeDeficit / 2 := by
  let q := heathBrownBoxFactorExponent box.a box.b box.q j
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 60 box.m j) q
  have hNbase := dyadic_length_ge_maynard_endpoint_root box hT hmu_lo helig j hlong
  have hroot1 : 1 < T ^ (1 / 216000 : ℝ) := by
    simpa using (Real.strictMono_rpow_of_base_gt_one hT)
      (by norm_num : (0 : ℝ) < 1 / 216000)
  have hN : 1 < N := hroot1.trans_le hNbase
  have hC : 1 ≤ C := by
    dsimp [C, q]
    exact one_le_heathBrownDerivativeConstant_of_zeta_or_log _ _ hX hkind
  have hfac := maynard_endpoint_fixedOrder_factorial box hT hmu_lo helig j hlong hfactorial
  have hlow := maynard_zeta_log_factor_low_window_elevenFifths
    box j hkind hX hT hmu_hi hXscale hylo hpi
  have hhigh := maynard_endpoint_fixedOrder_high_window
    box hT hmu_lo helig j hlong hyupper
  have hy0 : 0 < y := lt_trans zero_lt_one (hT.trans_le hylo)
  have hqX := box.factorExponent_le_log_X_of_zeta_or_log j hkind
  have hupper := norm_heathBrownBoxFactorValue_le_derivative_defect
    L X 60 box j hkind hX hc hy0
      (k₀ := maynardEndpointDerivativeOrder) (by
        dsimp [maynardEndpointDerivativeOrder]
        norm_num) hqX hfac hlow hhigh
  exact maynardAmplitude_le_one_sub_half_of_pointwise_power_saving
    hN hV hC (by simpa [N, C, q, maynardEndpointDerivativeDeficit] using hsize)
      (by simpa [N, C, q, maynardEndpointDerivativeDeficit] using hupper)

/-- Uniform eventual absorption of every endpoint-long zeta/log derivative constant. -/
theorem eventually_maynard_endpoint_zeta_log_size_ready_eight :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 8 → (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60,
          ∀ j : HeathBrownBoxFactorIndex 60 box.m,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) →
            IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
            4 / 3 ≤ mu →
            heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
            2 * Real.log
                (heathBrownDerivativeConstant X
                  (heathBrownBoxFactorKind 60 box.m j)
                  (heathBrownBoxFactorExponent box.a box.b box.q j)) ≤
              maynardEndpointDerivativeDeficit *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) := by
  let eps : ℝ := maynardEndpointDerivativeDeficit / (4 * 216000)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity [maynardEndpointDerivativeDeficit_pos]
  have hconst : ∀ᶠ T : ℝ in Filter.atTop,
      Real.log 5120 ≤ eps * Real.log T := by
    have hlogGrow : Filter.Tendsto (fun T : ℝ => eps * Real.log T)
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heps Real.tendsto_log_atTop
    exact hlogGrow.eventually_ge_atTop (Real.log 5120)
  filter_upwards [eventually_log_maynardLongPolylogEnvelope_le_lowOrdinate heps,
    hconst, Filter.eventually_gt_atTop (1 : ℝ)] with T hE hconstT hT
  intro X hX mu hmu_hi hXscale L box j hkind helig hmu_lo hlong
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 60 box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  have hC : 0 < C := by
    dsimp [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hCup : C ≤ 5120 * maynardLongPolylogEnvelope X :=
    heathBrownDerivativeConstant_le_polylogEnvelope box j hkind hX
  have hlogC : Real.log C ≤ Real.log 5120 +
      Real.log (maynardLongPolylogEnvelope X) := by
    have hEpos : 0 < maynardLongPolylogEnvelope X :=
      lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
    calc
      Real.log C ≤ Real.log (5120 * maynardLongPolylogEnvelope X) :=
        Real.log_le_log hC hCup
      _ = Real.log 5120 + Real.log (maynardLongPolylogEnvelope X) := by
        rw [Real.log_mul (by norm_num) hEpos.ne']
  have hlogE := hE X hX mu hmu_hi hXscale
  have hlogCsmall : Real.log C ≤ 2 * eps * Real.log T := by
    linarith
  have hN := dyadic_length_ge_maynard_endpoint_root box hT hmu_lo helig j hlong
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hroot0 : 0 < T ^ (1 / 216000 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hN0 : 0 < N := hroot0.trans_le hN
  have hlogN : (1 / 216000 : ℝ) * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log hroot0 hN
    rwa [Real.log_rpow hT0] at h
  have hdelta : 0 ≤ maynardEndpointDerivativeDeficit :=
    maynardEndpointDerivativeDeficit_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hlogN hdelta
  calc
    2 * Real.log C ≤ 4 * eps * Real.log T := by linarith
    _ = maynardEndpointDerivativeDeficit * ((1 / 216000 : ℝ) * Real.log T) := by
      dsimp [eps]
      ring
    _ ≤ maynardEndpointDerivativeDeficit * Real.log N := hscaled

/-- **Unconditional endpoint zeta/log exclusion.**  At all sufficiently large heights, every

endpoint-long zeta or logarithm factor of every eligible degree-`60` box has one fixed local
amplitude deficit. -/
theorem eventually_maynard_endpoint_zeta_log_amplitude_deficit_elevenFifths :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60,
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          ∀ j : HeathBrownBoxFactorIndex 60 box.m,
            (heathBrownBoxFactorKind 60 box.m j = .zeta ∨
              heathBrownBoxFactorKind 60 box.m j = .log) →
            heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
              dyadicLogExponent T
                (heathBrownBoxFactorExponent box.a box.b box.q j) →
            ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
              0 < ‖heathBrownBoxFactorValue L X 60 box
                ((c : ℂ) + (y : ℝ) * Complex.I) j‖ →
              maynardAmplitude c
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
                  ‖heathBrownBoxFactorValue L X 60 box
                    ((c : ℂ) + (y : ℝ) * Complex.I) j‖ ≤
                1 - maynardEndpointDerivativeDeficit / 2 := by
  have hpi : Filter.Tendsto (fun T : ℝ => T ^ (4 / 15 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  have hfac : Filter.Tendsto (fun T : ℝ => T ^ (1 / 216000 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hpi.eventually_ge_atTop (8 * Real.pi),
    hfac.eventually_ge_atTop (((Nat.factorial 216001 : ℕ) : ℝ)),
    eventually_maynard_endpoint_zeta_log_size_ready_eight]
      with T hT hpiT hfacT hsize
  intro X hX mu hmu_lo hmu_hi hXscale L box helig j hkind hlong
    c y hc hylo hyupper hV
  exact maynard_heathBrown_endpoint_zeta_log_amplitude_le_one_sub_half_elevenFifths
    box j hkind hX hT hmu_lo hmu_hi hXscale helig hlong hc hylo hyupper
      hpiT hfacT (hsize X hX mu (by linarith : mu ≤ 8) hXscale
        L box j hkind helig hmu_lo hlong) hV

/-- The logarithm of the uniform Maynard polylog envelope fits inside one Route-T edge envelope.
This is a direct comparison on the `log log` scale, not an `o(log T)` weakening. -/
theorem log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope_eight
    {A T mu : ℝ} {X : ℕ} (hX : 1 ≤ X) (hT : 0 < T)
    (hlogT : 1 ≤ Real.log T) (hmu : mu ≤ 8)
    (hXscale : (X : ℝ) ≤ T ^ mu) :
    Real.log (maynardLongPolylogEnvelope X) ≤
      routeTContourEdgeLogEnvelope A (3 * T) := by
  let Z : ℝ := routeTLogHeightEnvelope (4 * (3 * T + 1))
  let W : ℝ := 1 + Real.log Z
  have hE := maynardLongPolylogEnvelope_le_twelve_log_of_mu_le_eight hX hT hlogT hmu hXscale
  have hE0 : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  have hlogT0 : 0 < Real.log T := by linarith
  have hlogE : Real.log (maynardLongPolylogEnvelope X) ≤
      Real.log (12 * Real.log T) := Real.log_le_log hE0 hE
  have harg0 : 0 < 4 * (3 * T + 1) + 2 := by positivity
  have harg : T ≤ 4 * (3 * T + 1) + 2 := by linarith
  have hlogArg : Real.log T ≤ Real.log (4 * (3 * T + 1) + 2) :=
    Real.log_le_log hT harg
  have hZlogT : Real.log T ≤ Z := by
    dsimp only [Z, routeTLogHeightEnvelope]
    linarith
  have hZ0 : 0 < Z := hlogT0.trans_le hZlogT
  have hloglog : Real.log (Real.log T) ≤ Real.log Z :=
    Real.log_le_log hlogT0 hZlogT
  have hlog12 : Real.log 12 < 11 := by
    have h := Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 12) (by norm_num : (12 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hsplit : Real.log (12 * Real.log T) =
      Real.log 12 + Real.log (Real.log T) := by
    rw [Real.log_mul (by norm_num) hlogT0.ne']
  have hW1 : 1 ≤ W := by
    dsimp only [W]
    linarith [Real.log_nonneg (by linarith : 1 ≤ Z)]
  have hlog12T : Real.log (12 * Real.log T) ≤ 12 * W := by
    rw [hsplit]
    dsimp only [W]
    linarith
  have hB : 2 ≤ routeTZeroFreeBudgetEnvelopeConstant A + 2 := by
    linarith [routeTZeroFreeBudgetEnvelopeConstant_pos A]
  have hBsq : 4 ≤ (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) := by
    nlinarith
  have hWsq : 12 * W ≤ 1600 * W ^ (2 : ℕ) := by
    nlinarith
  calc
    Real.log (maynardLongPolylogEnvelope X) ≤ Real.log (12 * Real.log T) := hlogE
    _ ≤ 12 * W := hlog12T
    _ ≤ 1600 * W ^ (2 : ℕ) := hWsq
    _ ≤ 400 * (routeTZeroFreeBudgetEnvelopeConstant A + 2) ^ (2 : ℕ) *
        W ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [hBsq]) (sq_nonneg W)
    _ = routeTContourEdgeLogEnvelope A (3 * T) := by
      rfl

/-- The unique logarithmic atom's complete amplitude slack is eventually at most one quarter of
the common endpoint deficit times the exact box logarithmic length. -/
theorem eventually_routeT_endpoint_slack_mass_le_eight (A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 8 →
        (X : ℝ) ≤ T ^ mu →
        ∀ L : ℕ, ∀ box : HeathBrownBoxChoice L X 60, 1 ≤ box.q →
          IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
          ∑ i : HeathBrownBoxFactorIndex 60 box.m,
              heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
                (heathBrownBoxFactorExponent box.a box.b box.q i) *
                Real.log
                  (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) ≤
            (routeTEndpointCommonDeficit A T / 4) *
              Real.log
                ((groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
  obtain ⟨a, ha⟩ := eventually_atTop.1
    (eventually_const_mul_routeTContourEdgeLogEnvelope_le_shiftGain
      A 4320 (by norm_num))
  filter_upwards [eventually_ge_atTop (a / 3),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with T hTa hlogT hT3
  intro X hX mu hmu_lo hmu_hi hXscale L box hq helig
  let total : ℝ := heathBrownBoxTotalExponent L X 60 T box
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have hT0 : 0 < T := by linarith
  have htotal : mu / 120 ≤ total := by
    simpa [IsHeathBrownBoxEligible, total] using helig
  have htotalMin : (1 / 90 : ℝ) ≤ total := by linarith
  have hD : D = T ^ total := by
    dsimp [D, total]
    simpa [heathBrownBoxTotalExponent, groupedDyadicLower] using
      (cast_prod_twoPow_eq_rpow_sum_dyadicLogExponent (by linarith : 1 < T)
        (heathBrownBoxFactorExponent box.a box.b box.q)
        (Finset.univ : Finset (HeathBrownBoxFactorIndex 60 box.m)))
  have hlogD : Real.log D = total * Real.log T := by
    rw [hD, Real.log_rpow hT0]
  have hlogDlower : (1 / 90 : ℝ) * Real.log T ≤ Real.log D := by
    rw [hlogD]
    exact mul_le_mul_of_nonneg_right htotalMin (Real.log_nonneg (by linarith))
  have hslack :
      (∑ i : HeathBrownBoxFactorIndex 60 box.m,
          heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
            (heathBrownBoxFactorExponent box.a box.b box.q i) *
            Real.log
              (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) ≤
        routeTContourEdgeLogEnvelope A (3 * T) := by
    rw [sum_heathBrownBoxFactorAmplitudeSlack_mul_log box.a box.b hq]
    exact (log_heathBrown_log_trivialConstant_le_log_polylogEnvelope box hX hq).trans
      (log_maynardLongPolylogEnvelope_le_routeTContourEdgeLogEnvelope_eight
        hX hT0 hlogT hmu_hi hXscale)
  have habsorb := ha (3 * T) (by linarith)
  have hlog3T : Real.log (3 * T) ≤ 2 * Real.log T := by
    have hthree : 3 * T ≤ T ^ (2 : ℕ) := by nlinarith
    have hlog := Real.log_le_log (by positivity : 0 < 3 * T) hthree
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have henv0 : 0 ≤ routeTContourShiftEnvelope A (3 * T) :=
    (routeTContourShiftEnvelope_pos A (by positivity)).le
  have hedge : routeTContourEdgeLogEnvelope A (3 * T) ≤
      routeTContourShiftEnvelope A (3 * T) * Real.log T / 2160 := by
    have htransfer : routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
        2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by
      calc
        routeTContourShiftEnvelope A (3 * T) * Real.log (3 * T) ≤
            routeTContourShiftEnvelope A (3 * T) * (2 * Real.log T) :=
          mul_le_mul_of_nonneg_left hlog3T henv0
        _ = 2 * routeTContourShiftEnvelope A (3 * T) * Real.log T := by ring
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hlogDlower
    (show 0 ≤ routeTContourShiftEnvelope A (3 * T) / 24 by positivity)
  calc
    (∑ i : HeathBrownBoxFactorIndex 60 box.m,
        heathBrownFactorAmplitudeSlack (heathBrownBoxFactorKind 60 box.m i)
          (heathBrownBoxFactorExponent box.a box.b box.q i) *
          Real.log
            (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ))) ≤
        routeTContourEdgeLogEnvelope A (3 * T) := hslack
    _ ≤ routeTContourShiftEnvelope A (3 * T) * Real.log T / 2160 := hedge
    _ ≤ (routeTContourShiftEnvelope A (3 * T) / 24) * Real.log D := by
      nlinarith
    _ = (routeTEndpointCommonDeficit A T / 4) *
        Real.log
          ((groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) := by
      simp only [routeTEndpointCommonDeficit, D]
      ring

/-- **Every endpoint-long atom is excluded.**  Möbius, zeta, and logarithm factors share one
explicit vanishing deficit, and the complete literal box loses `7/10` of it globally. -/
theorem exists_eventually_routeT_endpoint_box_amplitude_exclusion_elevenFifths :
    ∃ (A C C' delta : ℝ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 < delta ∧
      ∀ᶠ T : ℝ in atTop,
        ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, 4 / 3 ≤ mu → mu ≤ 11 / 5 →
          (X : ℝ) ≤ T ^ mu →
          ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ T ^ (mu / 60) →
            ∀ box : HeathBrownBoxChoice L X 60,
              IsHeathBrownBoxEligible L X 60 T (mu / 120) box →
              ∀ c y alpha : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
                ((groupedDyadicLower
                  (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
                    (alpha - c) ≤
                  ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
                    ((c : ℂ) + (y : ℝ) * Complex.I)‖ →
                alpha ≤ 1 - routeTEndpointGlobalDeficit A T := by
  obtain ⟨A, C, C', delta, hC, hC', hdelta, hmobius⟩ :=
    exists_eventually_maynard_endpoint_moebius_amplitude_deficit_elevenFifths
  refine ⟨A, C, C', delta, hC, hC', hdelta, ?_⟩
  filter_upwards [hmobius,
    eventually_maynard_endpoint_zeta_log_amplitude_deficit_elevenFifths,
    eventually_routeTEndpointCommonDeficit_le_zetaLog A,
    eventually_routeTEndpointCommonDeficit_le_moebius hdelta,
    eventually_routeT_endpoint_slack_mass_le_eight A,
    eventually_gt_atTop (1 : ℝ)]
      with T hmob hzeta hcommonZeta hcommonMob hslack hT
  intro X hX mu hmu_lo hmu_hi hXscale L hL hcut box helig c y alpha hc hylo hyhi hlarge
  let s : ℂ := (c : ℂ) + (y : ℝ) * Complex.I
  let D : ℝ :=
    ((groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ)
  have hq : 1 ≤ box.q :=
    heathBrownBox_log_exponent_pos_of_large_core box s (by simpa only [s] using hlarge)
  have hD0 : 0 < D := by
    dsimp only [D]
    exact_mod_cast (show 0 < groupedDyadicLower
      (heathBrownBoxFactorExponent box.a box.b box.q) by
        exact lt_of_lt_of_le Nat.zero_lt_one
          (one_le_groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q)))
  have hthreshold : 0 < D ^ (alpha - c) := Real.rpow_pos_of_pos hD0 _
  have hcorePos : 0 < ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s‖ :=
    hthreshold.trans_le (by simpa only [D, s] using hlarge)
  have hprod :
      (∏ i : PositiveHeathBrownBoxFactorIndex box,
        heathBrownBoxFactorValue L X 60 box s i) =
        heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q s :=
    prod_positive_heathBrownBoxFactorValue_eq_core box hL hX hq s
  have hfactorPos : ∀ i : PositiveHeathBrownBoxFactorIndex box,
      0 < ‖heathBrownBoxFactorValue L X 60 box s i‖ := by
    intro i
    by_contra hi
    have hi0 : ‖heathBrownBoxFactorValue L X 60 box s i‖ = 0 :=
      le_antisymm (le_of_not_gt hi) (norm_nonneg _)
    have hvalue0 : heathBrownBoxFactorValue L X 60 box s i = 0 := norm_eq_zero.mp hi0
    have hprod0 : (∏ r : PositiveHeathBrownBoxFactorIndex box,
        heathBrownBoxFactorValue L X 60 box s r) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hvalue0
    rw [hprod] at hprod0
    rw [hprod0, norm_zero] at hcorePos
    exact (lt_irrefl 0) hcorePos
  have hDelta : 0 ≤ routeTEndpointCommonDeficit A T :=
    (routeTEndpointCommonDeficit_pos A (by linarith)).le
  have hlong : ∀ j : PositiveHeathBrownBoxFactorIndex box,
      (∑ i : PositiveHeathBrownBoxFactorIndex box,
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q i)) /
            (40 * 60 : ℕ) ≤
        dyadicLogExponent T
          (heathBrownBoxFactorExponent box.a box.b box.q j) →
      maynardAmplitude c
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
          ‖heathBrownBoxFactorValue L X 60 box s j‖ ≤
        1 - routeTEndpointCommonDeficit A T := by
    intro j hj
    have hV := hfactorPos j
    have htotal :
        heathBrownBoxTotalExponent L X 60 T box / (40 * 60 : ℕ) ≤
          dyadicLogExponent T
            (heathBrownBoxFactorExponent box.a box.b box.q j) := by
      rw [← sum_positive_dyadicLogExponent_eq_heathBrownBoxTotalExponent box]
      exact hj
    cases hkind : heathBrownBoxFactorKind 60 box.m j with
    | moebius =>
        have hm := hmob L X hL mu hmu_lo hmu_hi hcut box helig j hkind hj
          c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
    | zeta =>
        have hz := hzeta X hX mu hmu_lo hmu_hi hXscale L box helig j
          (Or.inl hkind) htotal c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
    | log =>
        have hz := hzeta X hX mu hmu_lo hmu_hi hXscale L box helig j
          (Or.inr hkind) htotal c y hc hylo hyhi (by simpa only [s] using hV)
        linarith
  have hslackMass := hslack X hX mu hmu_lo (by linarith : mu ≤ 8) hXscale L box hq helig
  have hbox := maynard_heathBrownBox_endpoint_long_deficits_trimmed
    (k := 60) (by norm_num) box hL hX hT hc hDelta hlong hslackMass
      (by simpa only [s] using hlarge)
  unfold routeTEndpointGlobalDeficit
  linarith

/-- One fixed eligible all-subheight box satisfies a complete all-amplitude Route-T count through
the natural height ceiling mu <= 11/5. -/
theorem exists_eventually_routeT_subHeightBox_all_amplitude_first_or_second_elevenFifths :
    ∃ A : ℝ, ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      1 ≤ X → 1 ≤ L →
      (X : ℝ) ≤ T ^ mu →
      (L : ℝ) ≤ T ^ (2 * (mu / 120)) →
      4 / 3 ≤ mu → mu ≤ 11 / 5 →
      1 / 2 ≤ c → 3 / 4 ≤ alpha →
      0 < delta → delta ≤ 2 * T →
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
      ∀ (S : Finset ℕ), S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T) →
      (∀ r ∈ S,
        ((groupedDyadicLower
          (heathBrownBoxFactorExponent box.a box.b box.q) : ℕ) : ℝ) ^
            (alpha - c) ≤
          ‖heathBrownDyadicCoreProduct L X 60 box.m box.a box.b box.q
            ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) →
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
    eventually_exists_maynardWindowRelevantSelectedCell_coloring_of_subHeight_box_elevenFifths,
    eventually_card_le_maynard_second_of_selected_cell_coloring_low_amplitude_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_middle_elevenFifths,
    eventually_card_le_maynard_first_or_second_of_selected_cell_coloring_elevenFifths A,
    eventually_gt_atTop (1 : ℝ)] with T hbox hcolorT hlowT hmiddleT hglobal hT
  intro L X K mu N0 c alpha delta hX hL hXscale hLscale hmuLo hmuHi hc
    halphaLo hdelta hdeltaHi box helig hrel hmobius hsubHeight
    S hS lam hband hgap hdiam hcore
  obtain ⟨color, hcolorBox⟩ := hcolorT hL hX hmuLo hmuHi hXscale
    box helig hrel hmobius hsubHeight (by linarith) halphaLo S lam hband hcore
  have hcolor : ∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
      L X T mu N0 c (lam r) alpha (color r) := by
    intro r hr
    exact (hcolorBox r hr).2
  by_cases hlow : alpha ≤ 19 / 25
  · refine Or.inr ?_
    simpa only [routeTSelectedCellAmplitudeReserve, if_pos hlow] using
      hlowT hX hL hXscale hLscale hmuLo hmuHi (by linarith) halphaLo hlow
        hdelta hdeltaHi S hS lam hgap hband color hcolor
  · have halphaMiddleLo : 19 / 25 ≤ alpha := le_of_not_ge hlow
    by_cases hmiddle : alpha ≤ 997 / 1000
    · simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_pos hmiddle] using
        hmiddleT hX hL hXscale hLscale hmuLo hmuHi hc halphaMiddleLo hmiddle
          hdelta S hS lam hgap hband color hcolor
    · have halphaHigh : 997 / 1000 < alpha := lt_of_not_ge hmiddle
      by_cases halphaEndpoint : alpha ≤ 1 - routeTEndpointGlobalDeficit A T
      · simpa only [routeTSelectedCellAmplitudeReserve, if_neg hlow, if_neg hmiddle] using
          hglobal hX hL hXscale hLscale hmuLo hmuHi hc halphaHigh
            halphaEndpoint hdelta S hS lam hgap hdiam color hcolor
      · have hcut : (L : ℝ) ≤ T ^ (mu / 60) := by
          have hexp : 2 * (mu / 120) = mu / 60 := by ring
          simpa only [hexp] using hLscale
        have hSempty : S = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hSne
          obtain ⟨r, hr⟩ := hSne
          have hbound := hbox X hX mu hmuLo hmuHi hXscale L hL hcut
            box helig c (lam r) alpha (by linarith)
              (hband r hr).1 (hband r hr).2 (hcore r hr)
          exact halphaEndpoint hbound
        left
        rw [hSempty]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (maynardHarmonicFactor_pos K hdelta).le
          (Real.rpow_nonneg (by linarith) _)

end RHTower.Sieve

end RHTower.Sieve

end RHTower.Sieve
