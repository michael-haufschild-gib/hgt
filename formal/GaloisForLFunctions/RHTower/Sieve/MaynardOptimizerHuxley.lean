import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardAdjacentOptimizerRaise
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogAmplitudeFibre
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogAmplitudeCount

/-!
# Optimizer-scale Huxley receiver for Route T

The old fixed interval `T^(9/16) <= Y <= T^(1367/2160)` hid two independent mechanisms.
Crossing Huxley's optimizer supplies the square-root envelope, while an amplitude gap absorbs
the exact fixed-polylog coefficient cost.  This file separates those mechanisms and keeps the
selected length `Y` symbolic.
-/

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Optimizer-scale energy absorption with an explicit amplitude reserve. -/
theorem maynard_huxley_energy_scale_of_optimizer_reserve
    (A w ell : ℕ) {T C Graw alpha alpha0 : ℝ}
    (hT : 1 < T) (halpha0 : 99 / 100 ≤ alpha0)
    (hC : 0 ≤ C) (hGraw0 : 0 ≤ Graw)
    (hw : w ≤ 120) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T ^ maynardHuxleyOptimizer alpha0 ≤ ((A ^ ell : ℕ) : ℝ))
    (henergy : Graw ≤ C * ((A ^ ell : ℕ) : ℝ))
    (hready : 2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
      (((A ^ ell : ℕ) : ℝ)) ^ (2 * (alpha - alpha0))) :
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T +
          8 * Real.sqrt ((((A * 2 ^ w) ^ ell : ℕ) : ℝ)))) ≤
      (((A ^ ell : ℕ) : ℝ)) ^ (2 * alpha) := by
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := (((A * 2 ^ w) ^ ell : ℕ) : ℝ)
  let theta := maynardHuxleyOptimizer alpha0
  let R : ℝ := Y ^ (2 * alpha0 - 1)
  have hT0 : 0 < T := by linarith
  have htheta0 : 0 < theta := maynardHuxleyOptimizer_pos (by linarith)
  have hY1 : 1 ≤ Y := by
    have hTpow1 : 1 ≤ T ^ theta := Real.one_le_rpow hT.le htheta0.le
    exact hTpow1.trans (by simpa [Y, theta] using hYlo)
  have hY0 : 0 ≤ Y := by linarith
  have hYpos : 0 < Y := by linarith
  have hR1 : 1 ≤ R := Real.one_le_rpow hY1 (by linarith)
  have hcard : w * ell + 1 ≤ 6121 := by
    calc
      w * ell + 1 ≤ 120 * 51 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hw hell51) 1
      _ = 6121 := by norm_num
  have hcardCast : (((w * ell + 1 : ℕ) : ℝ)) ≤ 6121 := by exact_mod_cast hcard
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
    have hcollapse : T ^ (1 / 2 : ℝ) = (T ^ theta) ^ (2 * alpha0 - 1) := by
      rw [← Real.rpow_mul hT0.le]
      congr 1
      dsimp only [theta, maynardHuxleyOptimizer]
      have hden : 4 * alpha0 - 2 ≠ 0 := by linarith
      field_simp [hden]
      ring
    rw [hcollapse]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hT0.le _)
      (by simpa [Y, theta] using hYlo) (by linarith)
  have hsqrtWidth : Real.sqrt maynardRaisedWidthConstant ≤
      maynardRaisedWidthConstant := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact maynardRaisedWidthConstant_one_le.trans' (by norm_num)
    · have hW := maynardRaisedWidthConstant_one_le
      nlinarith
  have hsqrtY : Real.sqrt Y ≤ R := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
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
  have hcardSq : (((w * ell + 1 : ℕ) : ℝ)) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcardCast 2
  have hprefix : 2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hcardSq (by norm_num))
      (by simpa [Y] using henergy) hGraw0
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have henvelope0 : 0 ≤ 1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z) := by
    have hsT := Real.sqrt_nonneg T
    have hsZ := Real.sqrt_nonneg Z
    nlinarith
  have hprefix0 : 0 ≤ 2 * (6121 : ℝ) ^ 2 * (C * Y) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (mul_nonneg hC hY0)
  calc
    2 * (((w * ell + 1 : ℕ) : ℝ)) ^ 2 * Graw *
        (1 + 256 * (Real.sqrt T + 8 * Real.sqrt Z)) ≤
      2 * (6121 : ℝ) ^ 2 * (C * Y) *
        (maynardEnergyEnvelopeConstant * R) :=
      mul_le_mul hprefix henvelope henvelope0 hprefix0
    _ = (2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant) *
        (Y * R) := by ring
    _ ≤ Y ^ (2 * (alpha - alpha0)) * (Y * R) := by
      exact mul_le_mul_of_nonneg_right (by simpa [Y] using hready)
        (mul_nonneg hY0 (Real.rpow_nonneg hY0 _))
    _ = Y ^ (2 * alpha) := by
      dsimp only [R]
      calc
        Y ^ (2 * (alpha - alpha0)) * (Y * Y ^ (2 * alpha0 - 1)) =
            Y ^ (2 * (alpha - alpha0)) *
              (Y ^ (1 : ℝ) * Y ^ (2 * alpha0 - 1)) := by simp
        _ = Y ^ (2 * (alpha - alpha0)) * Y ^ (1 + (2 * alpha0 - 1)) := by
          rw [← Real.rpow_add hYpos]
        _ = Y ^ (2 * (alpha - alpha0) + (1 + (2 * alpha0 - 1))) := by
          rw [← Real.rpow_add hYpos]
        _ = Y ^ (2 * alpha) := by congr 1; ring

/-- Canonical weighted Huxley conclusion for one selected raised cell. -/
def IsMaynardSelectedHuxleyBound
    {L X : ℕ} (K : ℕ) (c alpha delta : ℝ)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ) (ell : ℕ) : Prop :=
  (S.card : ℝ) *
      (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
        (alpha - c)) ^ 2) ≤
    2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) *
      ∑ r : Fin (Fintype.card (HeathBrownSelectedFactor label) * ell + 1),
        ((((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
            2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 *
          heathBrownSelectedRaisedEnergy label ell *
          (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
              2 ^ (r : ℕ) : ℕ) : ℝ)) +
            (12 * Real.pi *
              ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell *
                2 ^ (r : ℕ) : ℕ) : ℝ)) / delta) *
              ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)))

/-- Exact length-form count extracted from canonical Huxley, before any height specialization. -/
theorem card_le_of_selected_huxley_with_fixed_polylog_raw
    {L X K : ℕ} {c alpha delta : ℝ}
    (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1) (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hHuxley : IsMaynardSelectedHuxleyBound K c alpha delta label S ell) :
    (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
        maynardHarmonicFactor K delta *
        (1 + Real.log
          (maynardRaisedWidthConstant *
            ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
          (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
            (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
        (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
          (2 - 2 * alpha) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let Q : ℕ := w * ell + 1
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  let H : ℝ := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let HF : ℝ := maynardHarmonicFactor K delta
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  let PL : ℝ := (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e
  have hY1 : 1 ≤ Y := by
    dsimp only [Y, A]
    exact_mod_cast Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hw : w ≤ 120 := card_heathBrownSelectedFactor_sixty_le label
  have hQ : Q ≤ 6121 := by
    dsimp [Q]
    calc
      w * ell + 1 ≤ 120 * 51 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul hw hell51) 1
      _ = 6121 := by norm_num
  have hQcast : (Q : ℝ) ≤ 6121 := by exact_mod_cast hQ
  have hG0 : 0 ≤ G := heathBrownSelectedRaisedEnergy_nonneg label ell
  have hG : G ≤ maynardRaisedWidthConstant * Y * PL := by
    simpa [G, Y, A, PL, e, w] using
      heathBrownSelectedRaisedEnergy_le_lower_fixed_polylog label ell hell hell51
  have hG' : G ≤ maynardRaisedWidthConstant * PL * Y := by
    calc
      G ≤ maynardRaisedWidthConstant * Y * PL := hG
      _ = maynardRaisedWidthConstant * PL * Y := by ring
  have hHFpos : 0 < HF := maynardHarmonicFactor_pos K hdelta
  have hPL0 : 0 ≤ PL := by
    dsimp [PL]
    exact pow_nonneg (by
      have hWY1 : 1 ≤ maynardRaisedWidthConstant * Y := by
        nlinarith [maynardRaisedWidthConstant_one_le]
      have := Real.log_nonneg hWY1
      linarith) e
  have hexp : 1 - 2 * c ≤ 0 := by linarith
  let term : Fin Q → ℝ := fun r =>
    (((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 * G) *
      ((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) +
        (12 * Real.pi * ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) / delta) * H)
  have hterm : ∀ r : Fin Q,
      term r ≤ maynardRaisedWidthConstant * PL * Y * HF * Y ^ (1 - 2 * c) := by
    intro r
    let D : ℝ := (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    have htwo : 1 ≤ (2 ^ (r : ℕ) : ℕ) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hDlower : Y ≤ D := by
      dsimp [D, Y]
      exact_mod_cast (by simpa using Nat.mul_le_mul_left (A ^ ell) htwo)
    have hDpos : 0 < D := hYpos.trans_le hDlower
    have hDpow : D ^ (1 - 2 * c) ≤ Y ^ (1 - 2 * c) :=
      Real.rpow_le_rpow_of_nonpos hYpos hDlower hexp
    have hCP0 : 0 ≤ maynardRaisedWidthConstant * PL :=
      mul_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le) hPL0
    have hGD : G * D ^ (1 - 2 * c) ≤
        (maynardRaisedWidthConstant * PL * Y) * Y ^ (1 - 2 * c) :=
      mul_le_mul hG' hDpow (Real.rpow_nonneg hDpos.le _)
        (mul_nonneg hCP0 hYpos.le)
    have hscaled := mul_le_mul_of_nonneg_right hGD hHFpos.le
    have htermEq : term r = G * HF * D ^ (1 - 2 * c) := by
      dsimp [term, D, HF, H, maynardHarmonicFactor]
      exact weighted_huxley_term_eq_amplitude (D := D) (G := G) (c := c)
        (delta := delta) (H := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
        (by positivity) hdelta
    rw [htermEq]
    calc
      G * HF * D ^ (1 - 2 * c) = G * D ^ (1 - 2 * c) * HF := by ring
      _ ≤ maynardRaisedWidthConstant * PL * Y * Y ^ (1 - 2 * c) * HF := hscaled
      _ = maynardRaisedWidthConstant * PL * Y * HF * Y ^ (1 - 2 * c) := by ring
  have hsum :
      (∑ r : Fin Q, term r) ≤
        (Q : ℝ) * (maynardRaisedWidthConstant * PL * Y * HF *
          Y ^ (1 - 2 * c)) := by
    calc
      (∑ r : Fin Q, term r) ≤
          ∑ _r : Fin Q,
            (maynardRaisedWidthConstant * PL * Y * HF * Y ^ (1 - 2 * c)) :=
        Finset.sum_le_sum fun r _ => hterm r
      _ = (Q : ℝ) * (maynardRaisedWidthConstant * PL * Y * HF *
          Y ^ (1 - 2 * c)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let p : ℝ := 2 - 2 * alpha
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpower : Y * Y ^ (1 - 2 * c) =
      Y ^ p * (Y ^ (alpha - c)) ^ 2 := by
    have hsquare : (Y ^ (alpha - c)) ^ 2 = Y ^ (2 * (alpha - c)) := by
      calc
        (Y ^ (alpha - c)) ^ 2 = Real.rpow (Y ^ (alpha - c)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ ((alpha - c) * 2) := (Real.rpow_mul hYpos.le _ _).symm
        _ = Y ^ (2 * (alpha - c)) := by congr 1; ring
    calc
      Y * Y ^ (1 - 2 * c) = Y ^ (1 : ℝ) * Y ^ (1 - 2 * c) := by simp
      _ = Y ^ (2 - 2 * c) := by
        rw [← Real.rpow_add hYpos]
        congr 1
        ring
      _ = Y ^ p * Y ^ (2 * (alpha - c)) := by
        rw [← Real.rpow_add hYpos]
        congr 1
        dsimp [p]
        ring
      _ = Y ^ p * (Y ^ (alpha - c)) ^ 2 := by rw [hsquare]
  have hHuxley' : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (Q : ℝ) * ∑ r : Fin Q, term r := by
    simpa [IsMaynardSelectedHuxleyBound, term, A, Y, G, H, Q, w,
      div_mul_eq_mul_div] using hHuxley
  have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hupper := hHuxley'.trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hQ0))
  have hQsq : (Q : ℝ) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hQ0 hQcast 2
  have hrest0 : 0 ≤ maynardRaisedWidthConstant * PL * HF *
      (Y * Y ^ (1 - 2 * c)) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le) hPL0)
        hHFpos.le)
      (mul_nonneg hYpos.le (Real.rpow_nonneg hYpos.le _))
  have hreplaceQ :
      2 * (Q : ℝ) * ((Q : ℝ) *
        (maynardRaisedWidthConstant * PL * Y * HF * Y ^ (1 - 2 * c))) ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := by
    rw [← hpower]
    calc
      2 * (Q : ℝ) * ((Q : ℝ) *
          (maynardRaisedWidthConstant * PL * Y * HF * Y ^ (1 - 2 * c))) =
      2 * (Q : ℝ) ^ 2 * (maynardRaisedWidthConstant * PL * HF *
          (Y * Y ^ (1 - 2 * c))) := by ring
      _ ≤ 2 * (6121 : ℝ) ^ 2 * (maynardRaisedWidthConstant * PL * HF *
          (Y * Y ^ (1 - 2 * c))) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQsq (by norm_num)) hrest0
      _ = _ := by ring
  have hmaster : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hupper.trans hreplaceQ
  have hthreshold : 0 < (Y ^ (alpha - c)) ^ 2 := by positivity
  have hcard : (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL * Y ^ p := by
    have hmaster' : (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) ≤
        (Y ^ (alpha - c)) ^ 2 *
          (2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL * Y ^ p) := by
      calc
        (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) =
            (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 := by ring
        _ ≤ 2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL *
            (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hmaster
        _ = (Y ^ (alpha - c)) ^ 2 *
            (2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL * Y ^ p) := by ring
    exact (mul_le_mul_iff_right₀ hthreshold).mp hmaster'
  simpa [HF, PL, e, w, Y, A, p] using hcard

end RHTower.Sieve
