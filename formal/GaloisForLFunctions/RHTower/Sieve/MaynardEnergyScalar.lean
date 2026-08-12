import Mathlib

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

/-- Worst fixed-width dilation after raising at most `120` factors to order at most `51`. -/
def maynardRaisedWidthConstant : ℝ := ((2 ^ 6120 : ℕ) : ℝ)

/-- Common envelope constant for the Huxley square-root terms. -/
def maynardEnergyEnvelopeConstant : ℝ :=
  257 + 2048 * maynardRaisedWidthConstant

theorem maynardRaisedWidthConstant_one_le :
    1 ≤ maynardRaisedWidthConstant := by
  dsimp [maynardRaisedWidthConstant]
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : 2 ≠ 0)))

theorem maynardEnergyEnvelopeConstant_pos :
    0 < maynardEnergyEnvelopeConstant := by
  dsimp [maynardEnergyEnvelopeConstant]
  have := maynardRaisedWidthConstant_one_le
  positivity

/-- **Exact scalar closure of the Route-T energy wall.**  An energy exponent `41/40` is
strictly below the critical `10/9`: after the Huxley square-root envelope costs `8/9`, the
remaining power margin is `31/360` in the raised lower edge, hence `31/640` in height. -/
theorem maynard_huxley_energy_scale_of_subcritical_energy
    (A w ell : ℕ) {T C Graw : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (hGraw0 : 0 ≤ Graw)
    (hw : w ≤ 120) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T ^ (9 / 16 : ℝ) ≤ ((A ^ ell : ℕ) : ℝ))
    (henergy : Graw ≤ C * (((A ^ ell : ℕ) : ℝ)) ^ (41 / 40 : ℝ))
    (hready : 2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
      T ^ (31 / 640 : ℝ)) :
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T +
          8 * Real.sqrt ((((A * 2 ^ w) ^ ell : ℕ) : ℝ)))) ≤
      (((A ^ ell : ℕ) : ℝ)) ^ 2 := by
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := (((A * 2 ^ w) ^ ell : ℕ) : ℝ)
  let R : ℝ := Y ^ (8 / 9 : ℝ)
  have hT0 : 0 < T := by linarith
  have hTone : 1 ≤ T := hT.le
  have hY1 : 1 ≤ Y := by
    have hTpow1 : 1 ≤ T ^ (9 / 16 : ℝ) :=
      Real.one_le_rpow hTone (by norm_num)
    exact hTpow1.trans hYlo
  have hY0 : 0 ≤ Y := hY1.trans' (by norm_num)
  have hR1 : 1 ≤ R := Real.one_le_rpow hY1 (by norm_num)
  have hcard : w * ell + 1 ≤ 6121 := by
    calc
      w * ell + 1 ≤ 120 * 51 + 1 := Nat.add_le_add_right (Nat.mul_le_mul hw hell51) 1
      _ = 6121 := by norm_num
  have hcard_cast : (((w * ell + 1 : ℕ) : ℝ)) ≤ 6121 := by exact_mod_cast hcard
  have hZwidth : Z ≤ maynardRaisedWidthConstant * Y := by
    have hpow : w * ell ≤ 6120 := by
      calc
        w * ell ≤ 120 * 51 := Nat.mul_le_mul hw hell51
        _ = 6120 := by norm_num
    have hn : (A * 2 ^ w) ^ ell ≤ 2 ^ 6120 * A ^ ell := by
      rw [mul_pow, ← pow_mul]
      simpa [mul_comm] using Nat.mul_le_mul_right (A ^ ell)
        (Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow)
    have hn' := (Nat.cast_le (α := ℝ)).mpr hn
    change (((A * 2 ^ w) ^ ell : ℕ) : ℝ) ≤
      ((2 ^ 6120 : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ)
    simpa only [Nat.cast_mul] using hn'
  have hsqrtT : Real.sqrt T ≤ R := by
    rw [Real.sqrt_eq_rpow]
    have hcollapse : T ^ (1 / 2 : ℝ) = (T ^ (9 / 16 : ℝ)) ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      congr 1
      norm_num
    rw [hcollapse]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
      hYlo (by norm_num)
  have hsqrtWidth : Real.sqrt maynardRaisedWidthConstant ≤
      maynardRaisedWidthConstant := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact maynardRaisedWidthConstant_one_le.trans' (by norm_num)
    · have hW := maynardRaisedWidthConstant_one_le
      nlinarith
  have hsqrtY : Real.sqrt Y ≤ R := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  have hsqrtZ : Real.sqrt Z ≤ maynardRaisedWidthConstant * R := by
    calc
      Real.sqrt Z ≤ Real.sqrt (maynardRaisedWidthConstant * Y) :=
        Real.sqrt_le_sqrt hZwidth
      _ = Real.sqrt maynardRaisedWidthConstant * Real.sqrt Y := by
        rw [Real.sqrt_mul]
        exact maynardRaisedWidthConstant_one_le.trans' (by norm_num)
      _ ≤ maynardRaisedWidthConstant * R := by
        exact mul_le_mul hsqrtWidth hsqrtY (Real.sqrt_nonneg _)
          (by linarith [maynardRaisedWidthConstant_one_le])
  have henvelope : 1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z) ≤
      maynardEnergyEnvelopeConstant * R := by
    calc
      1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z)
          ≤ R + 256 * (R + 8 * (maynardRaisedWidthConstant * R)) := by
            gcongr
      _ = maynardEnergyEnvelopeConstant * R := by
        simp [maynardEnergyEnvelopeConstant]
        ring
  have hYgap : T ^ (31 / 640 : ℝ) ≤ Y ^ (31 / 360 : ℝ) := by
    have hcollapse : T ^ (31 / 640 : ℝ) =
        (T ^ (9 / 16 : ℝ)) ^ (31 / 360 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      congr 1
      norm_num
    rw [hcollapse]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
      hYlo (by norm_num)
  have hconst : 2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
      Y ^ (31 / 360 : ℝ) := hready.trans hYgap
  have hcard_sq : (((w * ell + 1 : ℕ) : ℝ)) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcard_cast 2
  have hprefix : 2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y ^ (41 / 40 : ℝ)) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hcard_sq (by norm_num)) henergy hGraw0
        (mul_nonneg (by norm_num) (sq_nonneg _))
  have henvelope0 : 0 ≤
      1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z) := by
    have hsT := Real.sqrt_nonneg T
    have hsZ := Real.sqrt_nonneg Z
    nlinarith
  have hprefixRight0 :
      0 ≤ 2 * (6121 : ℝ) ^ 2 * (C * Y ^ (41 / 40 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hC (Real.rpow_nonneg hY0 _))
  calc
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z))
        ≤ 2 * (6121 : ℝ) ^ 2 *
            (C * Y ^ (41 / 40 : ℝ)) *
              (maynardEnergyEnvelopeConstant * R) := by
          exact mul_le_mul hprefix henvelope henvelope0 hprefixRight0
    _ = (2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant) *
          (Y ^ (41 / 40 : ℝ) * R) := by ring
    _ ≤ Y ^ (31 / 360 : ℝ) * (Y ^ (41 / 40 : ℝ) * R) := by
          gcongr
    _ = Y ^ (2 : ℝ) := by
          dsimp [R]
          have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
          rw [← Real.rpow_add hYpos]
          rw [← Real.rpow_add hYpos]
          congr 1
          norm_num
    _ = Y ^ 2 := by rw [Real.rpow_two]

/-- Every fixed subcritical energy constant is eventually absorbed. -/
theorem eventually_maynard_huxley_energy_scalar_ready (C : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 < T ∧
        2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
          T ^ (31 / 640 : ℝ) := by
  have hgrowth : Filter.Tendsto (fun T : ℝ => T ^ (31 / 640 : ℝ))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hgrowth.eventually_ge_atTop
      (2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant)] with T hT hready
  exact ⟨hT, hready⟩

end RHTower.Sieve
