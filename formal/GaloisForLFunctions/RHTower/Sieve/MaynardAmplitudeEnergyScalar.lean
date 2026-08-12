import GaloisForLFunctions.RHTower.Sieve.MaynardEnergyScalar

/-!
# Huxley energy absorption at an independent amplitude

The scalar energy gate is parameterized by the actual Maynard amplitude.  An energy bound
`C Y^(1+rho)`, the universal square-root envelope `Y^(8/9)`, and any remaining power `gamma`
fit below the threshold `Y^(2 alpha)` whenever their exponents do.
-/

noncomputable section
namespace RHTower.Sieve

/-- Variable-energy scalar closure at independent amplitude `alpha`. -/
theorem maynard_huxley_energy_scale_at_amplitude
    (A w ell : ℕ) {T C Graw alpha rho gamma : ℝ}
    (hT : 1 < T) (hC : 0 ≤ C) (hGraw0 : 0 ≤ Graw)
    (hw : w ≤ 120) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T ^ (9 / 16 : ℝ) ≤ ((A ^ ell : ℕ) : ℝ))
    (henergy : Graw ≤ C * (((A ^ ell : ℕ) : ℝ)) ^ (1 + rho))
    (hgamma : 0 ≤ gamma)
    (hmargin : gamma + (1 + rho) + 8 / 9 ≤ 2 * alpha)
    (hready : 2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
      T ^ ((9 / 16 : ℝ) * gamma)) :
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T +
          8 * Real.sqrt ((((A * 2 ^ w) ^ ell : ℕ) : ℝ)))) ≤
      (((A ^ ell : ℕ) : ℝ)) ^ (2 * alpha) := by
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := (((A * 2 ^ w) ^ ell : ℕ) : ℝ)
  let R : ℝ := Y ^ (8 / 9 : ℝ)
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hY1 : 1 ≤ Y := by
    have hTpow1 : 1 ≤ T ^ (9 / 16 : ℝ) :=
      Real.one_le_rpow hT.le (by norm_num)
    exact hTpow1.trans hYlo
  have hY0 : 0 ≤ Y := le_trans (by norm_num) hY1
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hR1 : 1 ≤ R := Real.one_le_rpow hY1 (by norm_num)
  have hcard : w * ell + 1 ≤ 6121 := by
    calc
      w * ell + 1 ≤ 120 * 51 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hw hell51) 1
      _ = 6121 := by norm_num
  have hcardCast : (((w * ell + 1 : ℕ) : ℝ)) ≤ 6121 := by
    exact_mod_cast hcard
  have hZwidth : Z ≤ maynardRaisedWidthConstant * Y := by
    have hpow : w * ell ≤ 6120 := by
      calc
        w * ell ≤ 120 * 51 := Nat.mul_le_mul hw hell51
        _ = 6120 := by norm_num
    have hn : (A * 2 ^ w) ^ ell ≤ 2 ^ 6120 * A ^ ell := by
      have hpow2 : 2 ^ (w * ell) ≤ 2 ^ 6120 :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow
      calc
        (A * 2 ^ w) ^ ell = A ^ ell * 2 ^ (w * ell) := by
          rw [mul_pow, ← pow_mul]
        _ ≤ A ^ ell * 2 ^ 6120 := Nat.mul_le_mul_left _ hpow2
        _ = 2 ^ 6120 * A ^ ell := Nat.mul_comm _ _
    have hn' := (Nat.cast_le (α := ℝ)).mpr hn
    change (((A * 2 ^ w) ^ ell : ℕ) : ℝ) ≤
      ((2 ^ 6120 : ℕ) : ℝ) * ((A ^ ell : ℕ) : ℝ)
    simpa only [Nat.cast_mul] using hn'
  have hsqrtT : Real.sqrt T ≤ R := by
    rw [Real.sqrt_eq_rpow]
    have hcollapse : T ^ (1 / 2 : ℝ) =
        (T ^ (9 / 16 : ℝ)) ^ (8 / 9 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      congr 1
      norm_num
    rw [hcollapse]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hYlo (by norm_num)
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
      1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z) ≤
          R + 256 * (R + 8 * (maynardRaisedWidthConstant * R)) := by
        gcongr
      _ = maynardEnergyEnvelopeConstant * R := by
        simp [maynardEnergyEnvelopeConstant]
        ring
  have hYgap : T ^ ((9 / 16 : ℝ) * gamma) ≤ Y ^ gamma := by
    have hcollapse : T ^ ((9 / 16 : ℝ) * gamma) =
        (T ^ (9 / 16 : ℝ)) ^ gamma := by
      rw [← Real.rpow_mul hT0.le]
    rw [hcollapse]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _) hYlo hgamma
  have hconst : 2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
      Y ^ gamma := hready.trans hYgap
  have hcardSq : (((w * ell + 1 : ℕ) : ℝ)) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcardCast 2
  have hprefix : 2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y ^ (1 + rho)) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hcardSq (by norm_num)) henergy hGraw0
        (mul_nonneg (by norm_num) (sq_nonneg _))
  have henvelope0 : 0 ≤ 1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z) := by
    have hsT := Real.sqrt_nonneg T
    have hsZ := Real.sqrt_nonneg Z
    nlinarith
  have hprefixRight0 : 0 ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y ^ (1 + rho)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg hC (Real.rpow_nonneg hY0 _))
  calc
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z)) ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y ^ (1 + rho)) *
        (maynardEnergyEnvelopeConstant * R) :=
      mul_le_mul hprefix henvelope henvelope0 hprefixRight0
    _ = (2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant) *
        (Y ^ (1 + rho) * R) := by ring
    _ ≤ Y ^ gamma * (Y ^ (1 + rho) * R) := by gcongr
    _ = Y ^ (gamma + (1 + rho) + 8 / 9) := by
      dsimp [R]
      rw [← Real.rpow_add hYpos, ← Real.rpow_add hYpos]
      congr 1
      ring
    _ ≤ Y ^ (2 * alpha) :=
      Real.rpow_le_rpow_of_exponent_le hY1 hmargin

end RHTower.Sieve
