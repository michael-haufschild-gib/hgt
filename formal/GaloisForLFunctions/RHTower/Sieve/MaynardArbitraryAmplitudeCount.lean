import GaloisForLFunctions.RHTower.Sieve.MaynardPerronAmplitude
import GaloisForLFunctions.RHTower.Sieve.MaynardArbitraryEnergy

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Correct fibre count with arbitrary energy loss `rho`.  Dependence on `c` cancels, while
Maynard amplitude `alpha` survives as exponent `2 + rho - 2*alpha`. -/
theorem card_le_of_huxley_at_amplitude_with_rho
    {L X K : ℕ} {T0 c alpha delta rho : ℝ}
    (hT0 : 1 < T0) (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1)
    (hrho : 0 < rho) (hdelta : 0 < delta)
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
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho *
        maynardHarmonicFactor K delta *
          T0 ^ ((1367 / 2160 : ℝ) * (2 + rho - 2 * alpha)) := by
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let Q : ℕ := w * ell + 1
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  let H : ℝ := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)
  let HF : ℝ := maynardHarmonicFactor K delta
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
  have hG : G ≤ maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) := by
    simpa [G, heathBrownSelectedRaisedEnergy, Y, A, Nat.cast_pow] using
      (sum_normSq_convPow_heathBrownGrouped_le_arbitrary_subcritical hrho hw ell hell hell51
        L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label))
  have hHFpos : 0 < HF := maynardHarmonicFactor_pos K hdelta
  have hexp : 1 - 2 * c ≤ 0 := by linarith
  let term : Fin Q → ℝ := fun r =>
    (((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-c)) ^ 2 * G) *
      (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) +
        (12 * Real.pi * ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) / delta) * H)
  have hterm : ∀ r : Fin Q,
      term r ≤ maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
          Y ^ (1 - 2 * c) := by
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
    have hGD : G * D ^ (1 - 2 * c) ≤
        (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho)) * Y ^ (1 - 2 * c) :=
      mul_le_mul hG hDpow (Real.rpow_nonneg hDpos.le _)
        (mul_nonneg (maynardVariableUniformEnergyConstant_pos rho).le
          (Real.rpow_nonneg hYpos.le _))
    have hscaled := mul_le_mul_of_nonneg_right hGD hHFpos.le
    have htermEq : term r = G * HF * D ^ (1 - 2 * c) := by
      dsimp [term, D, HF, H, maynardHarmonicFactor]
      exact weighted_huxley_term_eq_amplitude (D := D) (G := G) (c := c)
        (delta := delta) (H := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
        (by positivity) hdelta
    rw [htermEq]
    calc
      G * HF * D ^ (1 - 2 * c) = G * D ^ (1 - 2 * c) * HF := by ring
      _ ≤ maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) *
          Y ^ (1 - 2 * c) * HF := hscaled
      _ = maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
          Y ^ (1 - 2 * c) := by ring
  have hsum :
      (∑ r : Fin Q, term r) ≤
        (Q : ℝ) * (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
          Y ^ (1 - 2 * c)) := by
    calc
      (∑ r : Fin Q, term r) ≤
          ∑ _r : Fin Q,
            (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
              Y ^ (1 - 2 * c)) := Finset.sum_le_sum fun r _ => hterm r
      _ = (Q : ℝ) * (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
          Y ^ (1 - 2 * c)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  let p : ℝ := 2 + rho - 2 * alpha
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hpower : Y ^ (1 + rho) * Y ^ (1 - 2 * c) =
      Y ^ p * (Y ^ (alpha - c)) ^ 2 := by
    have hsquare : (Y ^ (alpha - c)) ^ 2 = Y ^ (2 * (alpha - c)) := by
      calc
        (Y ^ (alpha - c)) ^ 2 = Real.rpow (Y ^ (alpha - c)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Y ^ ((alpha - c) * 2) := (Real.rpow_mul hYpos.le _ _).symm
        _ = Y ^ (2 * (alpha - c)) := by congr 1; ring
    rw [hsquare, ← Real.rpow_add hYpos, ← Real.rpow_add hYpos]
    congr 1
    dsimp [p]
    ring
  have hHuxley' : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (Q : ℝ) * ∑ r : Fin Q, term r := by
    simpa [term, A, Y, G, H, Q, w, div_mul_eq_mul_div] using hHuxley
  have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hupper := hHuxley'.trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hQ0))
  have hQsq : (Q : ℝ) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hQ0 hQcast 2
  have hrest0 : 0 ≤ maynardVariableUniformEnergyConstant rho * HF *
      (Y ^ (1 + rho) * Y ^ (1 - 2 * c)) := by
    exact mul_nonneg
      (mul_nonneg (maynardVariableUniformEnergyConstant_pos rho).le hHFpos.le)
      (mul_nonneg (Real.rpow_nonneg hYpos.le _) (Real.rpow_nonneg hYpos.le _))
  have hreplaceQ :
      2 * (Q : ℝ) * ((Q : ℝ) *
        (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
          Y ^ (1 - 2 * c))) ≤
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := by
    rw [← hpower]
    calc
      2 * (Q : ℝ) * ((Q : ℝ) *
          (maynardVariableUniformEnergyConstant rho * Y ^ (1 + rho) * HF *
            Y ^ (1 - 2 * c))) =
        2 * (Q : ℝ) ^ 2 * (maynardVariableUniformEnergyConstant rho * HF *
          (Y ^ (1 + rho) * Y ^ (1 - 2 * c))) := by ring
      _ ≤ 2 * (6121 : ℝ) ^ 2 * (maynardVariableUniformEnergyConstant rho * HF *
          (Y ^ (1 + rho) * Y ^ (1 - 2 * c))) := by gcongr
      _ = _ := by ring
  have hmaster : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF *
        (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hupper.trans hreplaceQ
  have hthreshold : 0 < (Y ^ (alpha - c)) ^ 2 := by positivity
  have hcard : (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF * Y ^ p := by
    have hmaster' : (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) ≤
        (Y ^ (alpha - c)) ^ 2 *
          (2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF * Y ^ p) := by
      calc
        (Y ^ (alpha - c)) ^ 2 * (S.card : ℝ) =
            (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 := by ring
        _ ≤ 2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF *
            (Y ^ p * (Y ^ (alpha - c)) ^ 2) := hmaster
        _ = (Y ^ (alpha - c)) ^ 2 *
            (2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF * Y ^ p) := by ring
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
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho * HF := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (maynardVariableUniformEnergyConstant_pos rho).le)
      hHFpos.le
  simpa [HF, p] using hcard.trans (mul_le_mul_of_nonneg_left hYheight hconst0)

/-- **Exact Huxley-to-Maynard reserve law.**  The Huxley length coefficient is
`b = 1367/2160`, so its amplitude slope is `2b < 4/3`.  Consequently the first Maynard
alternative has exponent reserve `(mu - 2b) * (1-alpha)`.  Only `b*rho` and the explicit
constant must be absorbed. -/
theorem card_le_maynard_first_alternative_of_huxley_at_amplitude_with_rho
    {L X K : ℕ} {T0 c alpha delta rho mu : ℝ}
    (hT0 : 1 < T0) (hc : 1 / 2 ≤ c) (halpha : alpha ≤ 1)
    (hrho : 0 < rho) (hdelta : 0 < delta)
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
      2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho *
          maynardHarmonicFactor K delta ≤
        T0 ^ (((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) -
          (1367 / 2160 : ℝ) * rho)) :
    (S.card : ℝ) ≤ T0 ^ (mu * (1 - alpha)) := by
  have hcount := card_le_of_huxley_at_amplitude_with_rho
    hT0 hc halpha hrho hdelta label S ell hell hell51 hYlo hYhi hHuxley
  have hT0pos : 0 < T0 := by linarith
  have hpow0 : 0 ≤ T0 ^ ((1367 / 2160 : ℝ) * (2 + rho - 2 * alpha)) :=
    Real.rpow_nonneg hT0pos.le _
  refine hcount.trans ?_
  calc
    2 * (6121 : ℝ) ^ 2 * maynardVariableUniformEnergyConstant rho *
          maynardHarmonicFactor K delta *
        T0 ^ ((1367 / 2160 : ℝ) * (2 + rho - 2 * alpha))
      ≤ T0 ^ (((mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha)) -
            (1367 / 2160 : ℝ) * rho) *
          T0 ^ ((1367 / 2160 : ℝ) * (2 + rho - 2 * alpha)) :=
        mul_le_mul_of_nonneg_right hreserve hpow0
    _ = T0 ^ (mu * (1 - alpha)) := by
      rw [← Real.rpow_add hT0pos]
      congr 1
      ring

/-- Energy loss matched to a known positive amplitude deficit.  Exact coefficient `73/1367`
is forced by the gap between Maynard's worst height ratio `4/3` and Huxley's slope
`2 * 1367/2160 = 1367/1080`. -/
def maynardPointwiseMatchedRho (d : ℝ) : ℝ := (73 / 1367 : ℝ) * d

theorem maynardPointwiseMatchedRho_pos {d : ℝ} (hd : 0 < d) :
    0 < maynardPointwiseMatchedRho d := by
  dsimp [maynardPointwiseMatchedRho]
  positivity

/-- **Quantitative elimination of the ultra band.**  A fixed product-amplitude deficit `d`
provides enough slope reserve to pay the matched arbitrary energy loss, uniformly over the full
Maynard range `mu ≥ 4/3`.  A positive reserve `73d/2160` remains for all constants and labels. -/
theorem maynard_huxley_reserve_of_pointwise_deficit
    {mu alpha d : ℝ} (hmu : 4 / 3 ≤ mu) (hd : 0 ≤ d)
    (halpha : alpha ≤ 1 - d) :
    (73 / 2160 : ℝ) * d ≤
      (mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha) -
        (1367 / 2160 : ℝ) * maynardPointwiseMatchedRho d := by
  have hgap : (73 / 1080 : ℝ) ≤
      mu - 2 * (1367 / 2160 : ℝ) := by
    linarith
  have hone : d ≤ 1 - alpha := by linarith
  have hone0 : 0 ≤ 1 - alpha := hd.trans hone
  have hmul : (73 / 1080 : ℝ) * d ≤
      (mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha) := by
    calc
      (73 / 1080 : ℝ) * d ≤ (73 / 1080 : ℝ) * (1 - alpha) := by
        gcongr
      _ ≤ (mu - 2 * (1367 / 2160 : ℝ)) * (1 - alpha) := by
        exact mul_le_mul_of_nonneg_right hgap hone0
  dsimp [maynardPointwiseMatchedRho]
  nlinarith

/-- Every fixed multiplicative loss is eventually absorbed by the positive reserve left after
matching `rho` to a pointwise deficit. -/
theorem eventually_maynard_pointwise_deficit_absorbs_constant
    (C : ℝ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ T : ℝ in Filter.atTop,
      1 < T ∧ C ≤ T ^ ((73 / 2160 : ℝ) * d) := by
  have hexp : 0 < (73 / 2160 : ℝ) * d := by positivity
  have hgrowth : Filter.Tendsto (fun T : ℝ => T ^ ((73 / 2160 : ℝ) * d))
      Filter.atTop Filter.atTop := tendsto_rpow_atTop hexp
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    hgrowth.eventually_ge_atTop C] with T hT hC
  exact ⟨hT, hC⟩

end RHTower.Sieve
