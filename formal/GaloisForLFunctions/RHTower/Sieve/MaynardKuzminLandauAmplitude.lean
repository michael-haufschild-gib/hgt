import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauFactor
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells

/-!
# Amplitude exclusion from the over-height Kuzmin--Landau saving

The explicit `N / T` first-derivative saving becomes a fixed local Maynard-amplitude deficit
because every literal Heath--Brown length is at most `T^(19/9)`.  The logarithmic coefficient
cost is absorbed into `T^(1/10)`, leaving the exact common deficit `81/190`.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta

/-- The complete zeta/logarithm prefactor in the over-height first-derivative estimate costs at
most `T^(1/10)`, uniformly over every Maynard cutoff. -/
theorem eventually_maynardKuzminLandau_polylog_absorbed :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 < T ∧
        ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
          2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
            T ^ (1 / 10 : ℝ) := by
  have heps : (0 : ℝ) < 1 / 10 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 1 heps).def
    (show (0 : ℝ) < 1 / 1024 by norm_num)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_gt_atTop (1 : ℝ)] with T hsmall hlogT hT
  refine ⟨hT, ?_⟩
  intro X hX mu hmu hXscale
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow : 0 < T ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hT0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog0 _), abs_of_nonneg hTpow.le,
    Real.rpow_one] at hsmall
  have hE := maynardLongPolylogEnvelope_le_eight_log
    hX hT0 hlogT hmu hXscale
  have hcoeff : 2 * (6 * Real.pi + 1) ≤ 50 := by
    nlinarith [Real.pi_le_four]
  have hleft :
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
        400 * Real.log T := by
    calc
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
          2 * (6 * Real.pi + 1) * (8 * Real.log T) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ 50 * (8 * Real.log T) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 400 * Real.log T := by ring
  have hhalf : 512 * Real.log T ≤ (1 / 2 : ℝ) * T ^ (1 / 10 : ℝ) := by
    nlinarith
  calc
    2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
        400 * Real.log T := hleft
    _ ≤ 512 * Real.log T := by nlinarith
    _ ≤ (1 / 2 : ℝ) * T ^ (1 / 10 : ℝ) := hhalf
    _ ≤ T ^ (1 / 10 : ℝ) := by nlinarith

/-- Scalar conversion behind the new amplitude law.  A `T^(-9/10)` height saving is at least an
`N^(-81/190)` length saving throughout the full Maynard range `N ≤ T^(19/9)`. -/
theorem kuzminLandau_height_saving_to_length_saving
    {T N C c V : ℝ} (hT : 1 < T) (hTN : T ≤ N)
    (hNcap : N ≤ T ^ (19 / 9 : ℝ))
    (hC : C ≤ T ^ (1 / 10 : ℝ))
    (hV : V ≤ C / T * N ^ (1 - c)) :
    V ≤ N ^ (1 - c) * N ^ (-(81 / 190 : ℝ)) := by
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hN0 : 0 < N := hT0.trans_le hTN
  have hdiv : C / T ≤ T ^ (1 / 10 : ℝ) / T :=
    div_le_div_of_nonneg_right hC hT0.le
  have hdivEq : T ^ (1 / 10 : ℝ) / T = T ^ (-(9 / 10 : ℝ)) := by
    calc
      T ^ (1 / 10 : ℝ) / T = T ^ (1 / 10 : ℝ) / T ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = T ^ ((1 / 10 : ℝ) - 1) := (Real.rpow_sub hT0 _ _).symm
      _ = T ^ (-(9 / 10 : ℝ)) := by ring
  have hNrootRaw := Real.rpow_le_rpow hN0.le hNcap
    (by norm_num : (0 : ℝ) ≤ 9 / 19)
  have hflattenT :
      (T ^ (19 / 9 : ℝ)) ^ (9 / 19 : ℝ) = T := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  have hNroot : N ^ (9 / 19 : ℝ) ≤ T := hNrootRaw.trans_eq hflattenT
  have hnegRaw := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hN0 (9 / 19 : ℝ)) hNroot
      (by norm_num : -(9 / 10 : ℝ) ≤ 0)
  have hflattenN :
      (N ^ (9 / 19 : ℝ)) ^ (-(9 / 10 : ℝ)) =
        N ^ (-(81 / 190 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]
    congr 1
    ring
  have hheight : T ^ (-(9 / 10 : ℝ)) ≤ N ^ (-(81 / 190 : ℝ)) := by
    simpa [hflattenN] using hnegRaw
  have hratio : C / T ≤ N ^ (-(81 / 190 : ℝ)) :=
    hdiv.trans_eq hdivEq |>.trans hheight
  calc
    V ≤ C / T * N ^ (1 - c) := hV
    _ ≤ N ^ (-(81 / 190 : ℝ)) * N ^ (1 - c) :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN0.le _)
    _ = N ^ (1 - c) * N ^ (-(81 / 190 : ℝ)) := by ring

/-- An over-height zeta atom has local Maynard amplitude at most `109/190`. -/
theorem eventually_maynard_overHeight_zeta_amplitude_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        ∀ q : ℕ, q ≤ Nat.log 2 X → ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          T ≤ ((2 ^ q : ℕ) : ℝ) →
          0 < ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
              ((c : ℂ) + (y : ℂ) * Complex.I)‖ →
          maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
              ‖LSeries (complexCoeff
                (arithmeticDyadicBlock
                  (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
                    ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
            1 - 81 / 190 := by
  filter_upwards [eventually_maynardKuzminLandau_polylog_absorbed] with T hready
  intro X hX mu hmu hXscale q hq c y hc hylo hyhi hTN hV
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
  have hN : 1 < N := hready.1.trans_le hTN
  have hpowNat : 2 ^ q ≤ X :=
    (Nat.pow_le_pow_right (by norm_num) hq).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hNcapX : N ≤ (X : ℝ) := by
    dsimp [N]
    exact_mod_cast hpowNat
  have hTpow : T ^ mu ≤ T ^ (19 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le hmu
  have hNcap : N ≤ T ^ (19 / 9 : ℝ) := hNcapX.trans (hXscale.trans hTpow)
  have hC := hready.2 X hX mu hmu hXscale
  have hraw := norm_LSeries_zetaDyadicBlock_le_over_height
    hX hq (lt_trans zero_lt_one hready.1) hc hylo hyhi hTN
  have hE : 1 ≤ maynardLongPolylogEnvelope X :=
    one_le_maynardLongPolylogEnvelope X
  have hbaseC : 6 * Real.pi + 1 ≤ C := by
    dsimp [C]
    nlinarith [Real.pi_pos]
  have hupper :
      ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc (zeta : ArithmeticFunction ℝ) X) q))
          ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C / T * N ^ (1 - c) := by
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hbaseC (lt_trans zero_lt_one hready.1).le)
        (Real.rpow_nonneg (by positivity : 0 ≤ N) _))
  have hsave := kuzminLandau_height_saving_to_length_saving
    hready.1 hTN hNcap hC hupper
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    (c := c) hN hV (by norm_num : (0 : ℝ) < 1)
      (Delta := 81 / 190) (C := 1) (by simpa [N] using hsave)
  simpa [N] using hamp

/-- The unique over-height logarithmic atom obeys the same local amplitude deficit. -/
theorem eventually_maynard_overHeight_log_amplitude_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 19 / 9 → (X : ℝ) ≤ T ^ mu →
        ∀ q : ℕ, q ≤ Nat.log 2 X → ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          T ≤ ((2 ^ q : ℕ) : ℝ) →
          0 < ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
              ((c : ℂ) + (y : ℂ) * Complex.I)‖ →
          maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
              ‖LSeries (complexCoeff
                (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
                    ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
            1 - 81 / 190 := by
  filter_upwards [eventually_maynardKuzminLandau_polylog_absorbed] with T hready
  intro X hX mu hmu hXscale q hq c y hc hylo hyhi hTN hV
  let N : ℝ := (((2 ^ q : ℕ) : ℝ))
  let C : ℝ := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
  have hN : 1 < N := hready.1.trans_le hTN
  have hpowNat : 2 ^ q ≤ X :=
    (Nat.pow_le_pow_right (by norm_num) hq).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hNcapX : N ≤ (X : ℝ) := by
    dsimp [N]
    exact_mod_cast hpowNat
  have hTpow : T ^ mu ≤ T ^ (19 / 9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le hmu
  have hNcap : N ≤ T ^ (19 / 9 : ℝ) := hNcapX.trans (hXscale.trans hTpow)
  have hC := hready.2 X hX mu hmu hXscale
  have hraw := norm_LSeries_logDyadicBlock_le_over_height
    hX hq (lt_trans zero_lt_one hready.1) hc hylo hyhi hTN
  have hupper :
      ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C / T * N ^ (1 - c) := by
    simpa [C, N] using hraw
  have hsave := kuzminLandau_height_saving_to_length_saving
    hready.1 hTN hNcap hC hupper
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    (c := c) hN hV (by norm_num : (0 : ℝ) < 1)
      (Delta := 81 / 190) (C := 1) (by simpa [N] using hsave)
  simpa [N] using hamp

end RHTower.Sieve
