import GaloisForLFunctions.RHTower.Sieve.MaynardRouteTReadyHuxley

set_option maxRecDepth 10000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

def maynardHarmonicFactor (K : ℕ) (delta : ℝ) : ℝ :=
  1 + (12 * Real.pi / delta) *
    ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1)

theorem maynardHarmonicFactor_pos (K : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    0 < maynardHarmonicFactor K delta := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1) := by positivity
  dsimp [maynardHarmonicFactor]
  have hpi := Real.pi_pos
  positivity

private theorem weighted_huxley_term_eq
    {D G sigma delta H : ℝ} (hD : 0 < D) (hdelta : 0 < delta) :
    ((D ^ (-sigma)) ^ 2 * G) *
        (D + (12 * Real.pi * D / delta) * H) =
      G * (1 + (12 * Real.pi / delta) * H) * D ^ (1 - 2 * sigma) := by
  have hweight : (D ^ (-sigma)) ^ 2 * D = D ^ (1 - 2 * sigma) := by
    have hsquare : (D ^ (-sigma)) ^ 2 = D ^ (-2 * sigma) := by
      calc
        (D ^ (-sigma)) ^ 2 = Real.rpow (D ^ (-sigma)) (2 : ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = D ^ ((-sigma) * 2) := (Real.rpow_mul hD.le _ _).symm
        _ = D ^ (-2 * sigma) := by congr 1; ring
    rw [hsquare]
    calc
      D ^ (-2 * sigma) * D = D ^ (-2 * sigma) * D ^ (1 : ℝ) := by simp
      _ = D ^ (-2 * sigma + 1) := (Real.rpow_add hD _ _).symm
      _ = D ^ (1 - 2 * sigma) := by congr 1; ring
  have hfactor : D + (12 * Real.pi * D / delta) * H =
      D * (1 + (12 * Real.pi / delta) * H) := by
    field_simp
  rw [hfactor]
  calc
    (D ^ (-sigma)) ^ 2 * G *
        (D * (1 + (12 * Real.pi / delta) * H)) =
      G * ((D ^ (-sigma)) ^ 2 * D) *
        (1 + (12 * Real.pi / delta) * H) := by ring
    _ = G * D ^ (1 - 2 * sigma) *
        (1 + (12 * Real.pi / delta) * H) := by rw [hweight]
    _ = G * (1 + (12 * Real.pi / delta) * H) *
        D ^ (1 - 2 * sigma) := by ring

theorem card_le_of_maynardSelectionFibreHuxleyConclusion
    {L X K : ℕ} {T0 sigma delta : ℝ}
    (hT0 : 1 < T0) (hsigma : 1 / 2 ≤ sigma) (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ)
    (hconclusion : IsMaynardSelectionFibreHuxleyConclusion
      (K := K) (T0 := T0) (sigma := sigma) (delta := delta) label S) :
    (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
        maynardHarmonicFactor K delta * T0 ^ (1367 / 86400 : ℝ) := by
  rcases hconclusion with ⟨ell, hell, hell51, hYlo, hYhi, hHuxley⟩
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
    exact hTpow1.trans hYlo
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
  have hG : G ≤ maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) := by
    exact sum_normSq_convPow_heathBrownGrouped_le_subcritical hw ell hell hell51
      L X (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
  have hHFpos : 0 < HF := maynardHarmonicFactor_pos K hdelta
  have hexp : 1 - 2 * sigma ≤ 0 := by linarith
  let term : Fin Q → ℝ := fun r =>
    (((((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ)) ^ (-sigma)) ^ 2 * G) *
      (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) +
        (12 * Real.pi * ((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ) / delta) * H)
  have hterm : ∀ r : Fin Q,
      term r ≤
        maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * sigma) := by
    intro r
    let D : ℝ := (((A ^ ell * 2 ^ (r : ℕ) : ℕ) : ℝ))
    have htwo : 1 ≤ (2 ^ (r : ℕ) : ℕ) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hDlower : Y ≤ D := by
      dsimp [D, Y]
      exact_mod_cast (by
        simpa using Nat.mul_le_mul_left (A ^ ell) htwo)
    have hDpos : 0 < D := hYpos.trans_le hDlower
    have hDpow : D ^ (1 - 2 * sigma) ≤ Y ^ (1 - 2 * sigma) :=
      Real.rpow_le_rpow_of_nonpos hYpos hDlower hexp
    have hGD : G * D ^ (1 - 2 * sigma) ≤
        (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ)) *
          Y ^ (1 - 2 * sigma) :=
      mul_le_mul hG hDpow (Real.rpow_nonneg hDpos.le _)
        (mul_nonneg maynardUniformEnergyConstant_pos.le
          (Real.rpow_nonneg hYpos.le _))
    have hscaled := mul_le_mul_of_nonneg_right hGD hHFpos.le
    have htermEq : term r = G * HF * D ^ (1 - 2 * sigma) := by
      dsimp [term, D, HF, H, maynardHarmonicFactor]
      exact weighted_huxley_term_eq (D := D) (G := G) (sigma := sigma)
        (delta := delta) (H := ∑ i ∈ Finset.range K, 1 / ((i : ℝ) + 1))
        (by positivity) hdelta
    rw [htermEq]
    calc
      G * HF * D ^ (1 - 2 * sigma) =
          G * D ^ (1 - 2 * sigma) * HF := by ring
      _ ≤ maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) *
          Y ^ (1 - 2 * sigma) * HF := hscaled
      _ = maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * sigma) := by ring
  have hsum :
      (∑ r : Fin Q, term r) ≤
        (Q : ℝ) * (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * sigma)) := by
    calc
      (∑ r : Fin Q, term r)
          ≤ ∑ _r : Fin Q,
            (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
              Y ^ (1 - 2 * sigma)) := Finset.sum_le_sum fun r _ => hterm r
      _ = (Q : ℝ) * (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
          Y ^ (1 - 2 * sigma)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmaster : (S.card : ℝ) * (Y ^ (1 - sigma)) ^ 2 ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
        (Y ^ (1 / 40 : ℝ) * (Y ^ (1 - sigma)) ^ 2) := by
    have hHuxley' : (S.card : ℝ) * (Y ^ (1 - sigma)) ^ 2 ≤
        2 * (Q : ℝ) *
          ∑ r : Fin Q, term r := by
      simpa [term, A, Y, G, H, Q, w, div_mul_eq_mul_div] using hHuxley
    have hQ0 : 0 ≤ (Q : ℝ) := Nat.cast_nonneg _
    have hupper := hHuxley'.trans
      (mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hQ0))
    have hQsq : (Q : ℝ) ^ 2 ≤ (6121 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hQ0 hQcast 2
    have hconst0 : 0 ≤ maynardUniformEnergyConstant * HF :=
      mul_nonneg maynardUniformEnergyConstant_pos.le hHFpos.le
    have hreplaceQ :
        2 * (Q : ℝ) * ((Q : ℝ) *
          (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
            Y ^ (1 - 2 * sigma))) ≤
        2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
          (Y ^ (1 / 40 : ℝ) * (Y ^ (1 - sigma)) ^ 2) := by
      have hpower : Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * sigma) =
          Y ^ (1 / 40 : ℝ) * (Y ^ (1 - sigma)) ^ 2 := by
        have hsquare : (Y ^ (1 - sigma)) ^ 2 = Y ^ (2 * (1 - sigma)) := by
          calc
            (Y ^ (1 - sigma)) ^ 2 = Real.rpow (Y ^ (1 - sigma)) (2 : ℝ) :=
              (Real.rpow_natCast _ 2).symm
            _ = Y ^ ((1 - sigma) * 2) := (Real.rpow_mul hYpos.le _ _).symm
            _ = Y ^ (2 * (1 - sigma)) := by congr 1; ring
        rw [hsquare]
        rw [← Real.rpow_add hYpos, ← Real.rpow_add hYpos]
        congr 1
        ring
      rw [← hpower]
      have hrest0 : 0 ≤ maynardUniformEnergyConstant * HF *
          (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * sigma)) := by positivity
      calc
        2 * (Q : ℝ) * ((Q : ℝ) *
            (maynardUniformEnergyConstant * Y ^ (41 / 40 : ℝ) * HF *
              Y ^ (1 - 2 * sigma))) =
          2 * (Q : ℝ) ^ 2 * (maynardUniformEnergyConstant * HF *
            (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * sigma))) := by ring
        _ ≤ 2 * (6121 : ℝ) ^ 2 * (maynardUniformEnergyConstant * HF *
            (Y ^ (41 / 40 : ℝ) * Y ^ (1 - 2 * sigma))) := by
          gcongr
        _ = _ := by ring
    exact hupper.trans hreplaceQ
  have hthreshold : 0 < (Y ^ (1 - sigma)) ^ 2 := by positivity
  have hcard : (S.card : ℝ) ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
        Y ^ (1 / 40 : ℝ) := by
    have hmaster' : (Y ^ (1 - sigma)) ^ 2 * (S.card : ℝ) ≤
        (Y ^ (1 - sigma)) ^ 2 *
          (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
            Y ^ (1 / 40 : ℝ)) := by
      calc
        (Y ^ (1 - sigma)) ^ 2 * (S.card : ℝ) =
            (S.card : ℝ) * (Y ^ (1 - sigma)) ^ 2 := by ring
        _ ≤ 2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
            (Y ^ (1 / 40 : ℝ) * (Y ^ (1 - sigma)) ^ 2) := hmaster
        _ = (Y ^ (1 - sigma)) ^ 2 *
            (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF *
              Y ^ (1 / 40 : ℝ)) := by ring
    exact (mul_le_mul_iff_right₀ hthreshold).mp hmaster'
  have hYheight : Y ^ (1 / 40 : ℝ) ≤ T0 ^ (1367 / 86400 : ℝ) := by
    have hp := Real.rpow_le_rpow (by linarith) hYhi (by norm_num : (0 : ℝ) ≤ 1 / 40)
    have hcollapse : (T0 ^ (1367 / 2160 : ℝ)) ^ (1 / 40 : ℝ) =
        T0 ^ (1367 / 86400 : ℝ) := by
      rw [← Real.rpow_mul hT0pos.le]
      congr 1
      norm_num
    rw [hcollapse] at hp
    exact hp
  have hconst0 : 0 ≤
      2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant * HF :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
          maynardUniformEnergyConstant_pos.le) hHFpos.le
  simpa [HF] using
    hcard.trans (mul_le_mul_of_nonneg_left hYheight hconst0)

/-- **Uniform counting and summation closure.**  The complete large-ordinate set costs only the
finite degree-`60` selection-label multiplicity times the subcritical fibre exponent. -/
theorem exists_canonical_sixty_global_card_bound_of_ready_scale
    {X K : ℕ} {T0 t mu sigma V delta : ℝ}
    (hready : IsMaynardRouteTScaleReady T0)
    (hmu_lo : 4 / 3 ≤ mu) (hmu_hi : mu ≤ 19 / 9)
    (ht : t = mu / 120) (hX : 1 ≤ X) (hXscale : (X : ℝ) ≤ T0 ^ mu)
    (hsigma : 1 / 2 ≤ sigma) (hV : 0 < V) (hdelta : 0 < delta)
    (S : Finset ℕ) (hS : S ⊆ Finset.range K) (lam : ℕ → ℝ)
    (hband : ∀ r ∈ S, T0 ≤ lam r ∧ lam r ≤ 2 * T0)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T0)
    (haggregate : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ r ∈ S, V ≤ ‖heathBrownEligibleDyadicAggregate L X 60 T0 t
        ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖)
    (hreserve : ∀ L : ℕ, 1 ≤ L → X < (L + 1) ^ 60 →
      ∀ c : HeathBrownBoxChoice L X 60,
        IsHeathBrownBoxEligible L X 60 T0 t c →
          heathBrownEligibleBoxCost L X 60 *
            (groupedDyadicLower
              (heathBrownBoxFactorExponent c.a c.b c.q) : ℝ) ^ (1 - sigma) ≤ V) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧ (L : ℝ) ≤ T0 ^ (2 * t) ∧
      (S.card : ℝ) ≤
        (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) *
          (2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
            maynardHarmonicFactor K delta * T0 ^ (1367 / 86400 : ℝ)) := by
  obtain ⟨L, hL, hXL, hcut, color, _hcolor, hfibres⟩ :=
    exists_canonical_sixty_coloring_with_huxley_fibres_of_ready_scale
      hready hmu_lo hmu_hi ht hX hXscale (by linarith) hV hdelta
        S hS lam hband hgap hdiam haggregate hreserve
  refine ⟨L, hL, hXL, hcut, ?_⟩
  let B : ℝ := 2 * (6121 : ℝ) ^ 2 * maynardUniformEnergyConstant *
    maynardHarmonicFactor K delta * T0 ^ (1367 / 86400 : ℝ)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg _))
            maynardUniformEnergyConstant_pos.le)
          (maynardHarmonicFactor_pos K hdelta).le)
      (Real.rpow_nonneg (by linarith [hready.1.1]) _)
  have hfibreBound : ∀ label : HeathBrownSelectionLabel L X 60,
      (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤ B := by
    intro label
    by_cases hne : (S.filter fun r => color r = label).Nonempty
    · exact card_le_of_maynardSelectionFibreHuxleyConclusion
        hready.1.1 hsigma hdelta label (S.filter fun r => color r = label)
          (hfibres label hne)
    · have hempty : S.filter (fun r => color r = label) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, hB0]
  have hcast : (S.card : ℝ) =
      ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) := by
    exact_mod_cast card_eq_sum_color_fibres S color
  rw [hcast]
  calc
    ∑ label : HeathBrownSelectionLabel L X 60,
        (((S.filter fun r => color r = label).card : ℕ) : ℝ) ≤
      ∑ _label : HeathBrownSelectionLabel L X 60, B :=
        Finset.sum_le_sum fun label _ => hfibreBound label
    _ = (Fintype.card (HeathBrownSelectionLabel L X 60) : ℝ) * B := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = _ := rfl

end RHTower.Sieve
