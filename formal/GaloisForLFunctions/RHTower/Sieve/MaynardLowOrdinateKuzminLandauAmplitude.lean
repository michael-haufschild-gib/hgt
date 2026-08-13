import GaloisForLFunctions.RHTower.Sieve.MaynardKuzminLandauAmplitude

/-!
# Kuzmin--Landau amplitude exclusion on the full low-ordinate Perron band

Maynard's Perron integral starts at ordinate `x^(1/8)`, whereas the selected-cell count was
previously normalized only in the shorter range `x ≤ T^(19/9)`.  The first-derivative estimate is
stronger at lower ordinate.  On the full band `x ≤ T^8`, its `T^(-9/10)` saving is still the fixed
length saving `N^(-9/80)`.  Thus every over-height zeta or logarithmic atom has local amplitude at
most `1 - 9/80`, uniformly down to the Perron cutoff.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped zeta

/-- The literal logarithmic envelope remains `O(log T)` on the full low-ordinate scale
`X ≤ T^8`. -/
theorem maynardLongPolylogEnvelope_le_twelve_log_of_mu_le_eight
    {X : ℕ} (hX : 1 ≤ X) {T mu : ℝ}
    (hT : 0 < T) (hlogT : 1 ≤ Real.log T) (hmu : mu ≤ 8)
    (hXscale : (X : ℝ) ≤ T ^ mu) :
    maynardLongPolylogEnvelope X ≤ 12 * Real.log T := by
  have hXcast : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have harg : (((2 * (X + 1) : ℕ) : ℝ)) ≤ 4 * T ^ mu := by
    push_cast
    calc
      2 * ((X : ℝ) + 1) ≤ 4 * (X : ℝ) := by nlinarith
      _ ≤ 4 * T ^ mu := mul_le_mul_of_nonneg_left hXscale (by norm_num)
  have hlogarg : Real.log (((2 * (X + 1) : ℕ) : ℝ)) ≤
      Real.log (4 * T ^ mu) := by
    apply Real.log_le_log (by positivity)
    exact harg
  have hlog4 : Real.log 4 ≤ 3 := by
    nlinarith [Real.log_le_sub_one_of_pos (x := (4 : ℝ)) (by norm_num)]
  have hsplit : Real.log (4 * T ^ mu) = Real.log 4 + mu * Real.log T := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hT _).ne', Real.log_rpow hT]
  rw [hsplit] at hlogarg
  dsimp [maynardLongPolylogEnvelope]
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hmumul : mu * Real.log T ≤ 8 * Real.log T :=
    mul_le_mul_of_nonneg_right hmu hlog0
  linarith

/-- Every literal zeta/log coefficient cost is absorbed by `T^(1/10)` uniformly on
`X ≤ T^8`. -/
theorem eventually_maynardLowOrdinateKuzminLandau_polylog_absorbed :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 < T ∧
        ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 8 → (X : ℝ) ≤ T ^ mu →
          2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
            T ^ (1 / 10 : ℝ) := by
  have heps : (0 : ℝ) < 1 / 10 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop 1 heps).def
    (show (0 : ℝ) < 1 / 2048 by norm_num)
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
  have hE := maynardLongPolylogEnvelope_le_twelve_log_of_mu_le_eight
    hX hT0 hlogT hmu hXscale
  have hcoeff : 2 * (6 * Real.pi + 1) ≤ 50 := by
    nlinarith [Real.pi_le_four]
  have hleft :
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
        600 * Real.log T := by
    calc
      2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
          2 * (6 * Real.pi + 1) * (12 * Real.log T) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ 50 * (12 * Real.log T) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 600 * Real.log T := by ring
  have hhalf : 1024 * Real.log T ≤ (1 / 2 : ℝ) * T ^ (1 / 10 : ℝ) := by
    nlinarith
  calc
    2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X ≤
        600 * Real.log T := hleft
    _ ≤ 1024 * Real.log T := by nlinarith
    _ ≤ (1 / 2 : ℝ) * T ^ (1 / 10 : ℝ) := hhalf
    _ ≤ T ^ (1 / 10 : ℝ) := by nlinarith

/-- On `N ≤ T^8`, a `T^(-9/10)` saving is exactly at least the length saving
`N^(-9/80)`. -/
theorem kuzminLandau_height_saving_to_length_saving_eight
    {T N C c V : ℝ} (hT : 1 < T) (hTN : T ≤ N)
    (hNcap : N ≤ T ^ (8 : ℝ))
    (hC : C ≤ T ^ (1 / 10 : ℝ))
    (hV : V ≤ C / T * N ^ (1 - c)) :
    V ≤ N ^ (1 - c) * N ^ (-(9 / 80 : ℝ)) := by
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
    (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hflattenT :
      (T ^ (8 : ℝ)) ^ (1 / 8 : ℝ) = T := by
    rw [← Real.rpow_mul hT0.le]
    norm_num
  have hNroot : N ^ (1 / 8 : ℝ) ≤ T := hNrootRaw.trans_eq hflattenT
  have hnegRaw := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hN0 (1 / 8 : ℝ)) hNroot
      (by norm_num : -(9 / 10 : ℝ) ≤ 0)
  have hflattenN :
      (N ^ (1 / 8 : ℝ)) ^ (-(9 / 10 : ℝ)) =
        N ^ (-(9 / 80 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]
    norm_num
  have hheight : T ^ (-(9 / 10 : ℝ)) ≤ N ^ (-(9 / 80 : ℝ)) := by
    exact hnegRaw.trans_eq hflattenN
  have hratio : C / T ≤ N ^ (-(9 / 80 : ℝ)) :=
    hdiv.trans_eq hdivEq |>.trans hheight
  calc
    V ≤ C / T * N ^ (1 - c) := hV
    _ ≤ N ^ (-(9 / 80 : ℝ)) * N ^ (1 - c) :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hN0.le _)
    _ = N ^ (1 - c) * N ^ (-(9 / 80 : ℝ)) := by ring

/-- Full-Perron-band zeta specialization of the low-ordinate amplitude law. -/
theorem eventually_maynard_lowOrdinate_overHeight_zeta_amplitude_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 8 → (X : ℝ) ≤ T ^ mu →
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
            1 - 9 / 80 := by
  filter_upwards [eventually_maynardLowOrdinateKuzminLandau_polylog_absorbed] with T hready
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
  have hTpow : T ^ mu ≤ T ^ (8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le hmu
  have hNcap : N ≤ T ^ (8 : ℝ) := hNcapX.trans (hXscale.trans hTpow)
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
  have hsave := kuzminLandau_height_saving_to_length_saving_eight
    hready.1 hTN hNcap hC hupper
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    (c := c) hN hV (by norm_num : (0 : ℝ) < 1)
      (Delta := 9 / 80) (C := 1) (by simpa [N] using hsave)
  simpa [N] using hamp

/-- Full-Perron-band logarithmic specialization of the low-ordinate amplitude law. -/
theorem eventually_maynard_lowOrdinate_overHeight_log_amplitude_deficit :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ X : ℕ, 1 ≤ X → ∀ mu : ℝ, mu ≤ 8 → (X : ℝ) ≤ T ^ mu →
        ∀ q : ℕ, q ≤ Nat.log 2 X → ∀ c y : ℝ, 0 ≤ c → T ≤ y → y ≤ 2 * T →
          T ≤ ((2 ^ q : ℕ) : ℝ) →
          0 < ‖LSeries (complexCoeff
            (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
              ((c : ℂ) + (y : ℂ) * Complex.I)‖ →
          maynardAmplitude c (((2 ^ q : ℕ) : ℝ))
              ‖LSeries (complexCoeff
                (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
                    ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
            1 - 9 / 80 := by
  filter_upwards [eventually_maynardLowOrdinateKuzminLandau_polylog_absorbed] with T hready
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
  have hTpow : T ^ mu ≤ T ^ (8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hready.1.le hmu
  have hNcap : N ≤ T ^ (8 : ℝ) := hNcapX.trans (hXscale.trans hTpow)
  have hC := hready.2 X hX mu hmu hXscale
  have hraw := norm_LSeries_logDyadicBlock_le_over_height
    hX hq (lt_trans zero_lt_one hready.1) hc hylo hyhi hTN
  have hupper :
      ‖LSeries (complexCoeff
        (arithmeticDyadicBlock (coeffTrunc ArithmeticFunction.log X) q))
          ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C / T * N ^ (1 - c) := by
    simpa [C, N] using hraw
  have hsave := kuzminLandau_height_saving_to_length_saving_eight
    hready.1 hTN hNcap hC hupper
  have hamp := maynardAmplitude_le_of_pointwise_power_saving
    (c := c) hN hV (by norm_num : (0 : ℝ) < 1)
      (Delta := 9 / 80) (C := 1) (by simpa [N] using hsave)
  simpa [N] using hamp

end RHTower.Sieve
