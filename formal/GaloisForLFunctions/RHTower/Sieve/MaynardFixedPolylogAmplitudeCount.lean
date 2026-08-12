import GaloisForLFunctions.RHTower.Sieve.MaynardPerronAmplitude
import GaloisForLFunctions.RHTower.Sieve.MaynardFixedPolylogSelectedEnergy

/-!
# Rho-free Huxley count from fixed Maynard energy

Fixed convolution order turns selected Heath--Brown energy into length times one explicit
polylogarithm.  The Huxley large-values argument therefore retains exponent `2 - 2 * alpha`
without an auxiliary moving `rho` or a constant depending on the endpoint deficit.
-/

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

set_option maxHeartbeats 1000000 in
/-- **Rho-free Huxley amplitude count.**  Fixed selected-factor energy costs one explicit
polylogarithm but does not perturb the height exponent `2 - 2 * alpha`. -/
theorem card_le_of_huxley_at_amplitude_with_fixed_polylog
    {L X K : ℕ} {T0 c alpha delta : ℝ}
    (hT0 : 1 < T0) (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1)
    (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T0 ^ (9 / 16 : ℝ) ≤
      ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ))
    (hYhi : (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
      T0 ^ (1367 / 2160 : ℝ))
    (hHuxley :
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
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)))) :
    (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
        maynardHarmonicFactor K delta *
        (1 + Real.log
          (maynardRaisedWidthConstant *
            ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
          (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
            (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
        T0 ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha)) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let Q : ℕ := w * ell + 1
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  let H : ℝ := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let HF : ℝ := maynardHarmonicFactor K delta
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  let PL : ℝ :=
    (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e
  have hT0pos : 0 < T0 := by linarith
  have hY1 : 1 ≤ Y := by
    have hTpow1 : 1 ≤ T0 ^ (9 / 16 : ℝ) :=
      Real.one_le_rpow hT0.le (by norm_num)
    exact hTpow1.trans (by simpa [Y, A] using hYlo)
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
      (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) +
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
    simpa [term, A, Y, G, H, Q, w, div_mul_eq_mul_div] using hHuxley
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
  have hYheight : Y ^ p ≤ T0 ^ ((1367 / 2160 : ℝ) * p) := by
    have hYhi' : Y ≤ T0 ^ (1367 / 2160 : ℝ) := by
      simpa [Y, A, Nat.cast_pow] using hYhi
    have hp' := Real.rpow_le_rpow hYpos.le hYhi' hp
    calc
      Y ^ p ≤ (T0 ^ (1367 / 2160 : ℝ)) ^ p := hp'
      _ = T0 ^ ((1367 / 2160 : ℝ) * p) := by
        rw [← Real.rpow_mul hT0pos.le]
  have hconst0 : 0 ≤
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * HF * PL := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (le_trans (by norm_num) maynardRaisedWidthConstant_one_le))
        hHFpos.le)
      hPL0
  simpa [HF, PL, e, w, Y, A, p] using
    hcard.trans (mul_le_mul_of_nonneg_left hYheight hconst0)

/-- **Fixed-polylog Huxley-to-Maynard reserve law.**  With no power loss in coefficient energy,
the full reserve is `(mu - 2b) * (1 - alpha)`.  The harmonic spacing factor remains outside the
absorption, as required by the large-values target. -/
theorem card_le_maynard_first_alternative_of_huxley_at_amplitude_with_fixed_polylog
    {L X K : ℕ} {T0 c alpha delta mu : ℝ}
    (hT0 : 1 < T0) (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1)
    (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ)
    (ell : ℕ) (hell : 0 < ell) (hell51 : ell ≤ 51)
    (hYlo : T0 ^ (9 / 16 : ℝ) ≤
      ((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ))
    (hYhi : (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ≤
      T0 ^ (1367 / 2160 : ℝ))
    (hHuxley :
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
                  ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))))
    (hreserve :
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          (1 + Real.log
            (maynardRaisedWidthConstant *
              ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) ≤
        T0 ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha))) :
    (S.card : ℝ) ≤
      maynardHarmonicFactor K delta * T0 ^ (mu * (1 - alpha)) := by
  have hcount := card_le_of_huxley_at_amplitude_with_fixed_polylog
    hT0 hc halpha hdelta label S ell hell hell51 hYlo hYhi hHuxley
  have hT0pos : 0 < T0 := by linarith
  have hHF0 : 0 ≤ maynardHarmonicFactor K delta :=
    (maynardHarmonicFactor_pos K hdelta).le
  have hpow0 : 0 ≤ T0 ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha)) :=
    Real.rpow_nonneg hT0pos.le _
  calc
    (S.card : ℝ) ≤
        2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          maynardHarmonicFactor K delta *
          (1 + Real.log
            (maynardRaisedWidthConstant *
              ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)) *
          T0 ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha)) := hcount
    _ = maynardHarmonicFactor K delta *
        ((2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          (1 + Real.log
            (maynardRaisedWidthConstant *
              ((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ^
            (2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
              (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1))) *
          T0 ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha))) := by ring
    _ ≤ maynardHarmonicFactor K delta *
        (T0 ^ ((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) *
          T0 ^ ((1367 / 2160 : ℝ) * (2 - 2 * alpha))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hreserve hpow0) hHF0
    _ = maynardHarmonicFactor K delta * T0 ^ (mu * (1 - alpha)) := by
      rw [← Real.rpow_add hT0pos]
      congr 2
      ring

end RHTower.Sieve
