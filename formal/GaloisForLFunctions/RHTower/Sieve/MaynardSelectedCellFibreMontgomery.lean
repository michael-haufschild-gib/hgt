import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellColoring
import GaloisForLFunctions.RHTower.Sieve.MaynardTunedRaise
import GaloisForLFunctions.RHTower.Sieve.MaynardRaisedMontgomeryFiniteSet
import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryFixedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryAmplitudeFibre
import GaloisForLFunctions.RHTower.Sieve.MaynardTunedCountExponents
import GaloisForLFunctions.RHTower.Sieve.MaynardFibreCount

/-!
# Literal selected-cell fibres at a tuned Montgomery scale

The lower Route-T strip cannot use endpoint Huxley absorption at its exact `3/4` boundary.
Instead every selected cell, including a cell containing one long atom, is first raised through
`T^(4/5)`.  Its exact overshoot remains below one additional cell exponent.  This file connects
that crossing to the literal raised Montgomery mean square; no complementary factor or zeta
moment is assumed.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Filter Topology

/-- Canonical raw Montgomery inequality for one raised selected cell. -/
def IsMaynardSelectedMontgomeryBound
    {L X : ℕ} (H c alpha delta : ℝ)
    (label : HeathBrownSelectionLabel L X 60) (S : Finset ℕ) (ell : ℕ) : Prop :=
  (S.card : ℝ) *
      (((((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^
        (alpha - c)) ^ 2) ≤
    (H + 4 * (((groupedDyadicUpper
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) *
        (1 + Real.log ((groupedDyadicUpper
          (heathBrownSelectedExponent label)) ^ ell))) *
      (1 / delta + 2 * Real.log ((groupedDyadicUpper
        (heathBrownSelectedExponent label)) ^ ell)) *
      ((((((groupedDyadicLower
        (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ) ^ (-c)) ^ 2) *
        heathBrownSelectedRaisedEnergy label ell)

/-- All constants and logarithms in the two-term Montgomery fibre count cost less than
`T^(1/400)`.  Uniformity includes every raised energy exponent and every raised length below
`T^(2 : ℕ)`; this is the quantitative budget later shared with label entropy. -/
theorem eventually_maynardMontgomery_fibre_cost_absorbed :
    ∀ᶠ T : ℝ in atTop,
      ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T ^ (2 : ℕ) →
      e ≤ maynardMontgomeryFixedPolylogExponentBound →
      24 * maynardMontgomeryRaisedWidthConstant ^ 2 *
          (1 + Real.log
            (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ (e + 2) ≤
        T ^ (1 / 400 : ℝ) := by
  let W : ℝ := maynardMontgomeryRaisedWidthConstant
  let E : ℕ := maynardMontgomeryFixedPolylogExponentBound + 2
  let C : ℝ := 24 * W ^ 2 * (W + 3) ^ E
  have hW1 : 1 ≤ W := by
    simpa only [W] using maynardMontgomeryRaisedWidthConstant_one_le
  have hWpos : 0 < W := zero_lt_one.trans_le hW1
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hWpos))
      (pow_pos (by linarith) E)
  have heps : (0 : ℝ) < 1 / 400 := by norm_num
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop (E : ℝ) heps).def
    (show (0 : ℝ) < 1 / (2 * C) by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with T hsmall hlogT hT
  intro N e hN hNscale he
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hTpow : 0 < T ^ (1 / 400 : ℝ) := Real.rpow_pos_of_pos hT0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog0 _), abs_of_nonneg hTpow.le] at hsmall
  have hlogpow : Real.log T ^ (E : ℝ) = Real.log T ^ E :=
    Real.rpow_natCast _ _
  rw [hlogpow] at hsmall
  have hsmallScaled : C * Real.log T ^ E ≤
      (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
    have hs := mul_le_mul_of_nonneg_left hsmall hC.le
    have hcancel : C * (1 / (2 * C)) = 1 / 2 := by
      field_simp [hC.ne']
    calc
      C * Real.log T ^ E ≤ C * (1 / (2 * C) * T ^ (1 / 400 : ℝ)) := hs
      _ = (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) := by
        rw [← mul_assoc, hcancel]
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNRpos : (0 : ℝ) < N := zero_lt_one.trans_le hNR1
  have hT2pos : 0 < T ^ (2 : ℕ) := pow_pos hT0 _
  have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log T := by
    have hlog := Real.log_le_log hNRpos hNscale
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hlogW : Real.log W ≤ W :=
    (Real.log_le_sub_one_of_pos hWpos).trans (by linarith)
  have hlogMul : Real.log (W * (N : ℝ)) = Real.log W + Real.log (N : ℝ) := by
    rw [Real.log_mul hWpos.ne' hNRpos.ne']
  have hbase1 : 1 ≤ 1 + Real.log (W * (N : ℝ)) := by
    have hprod1 : 1 ≤ W * (N : ℝ) :=
      one_le_mul_of_one_le_of_one_le hW1 hNR1
    linarith [Real.log_nonneg hprod1]
  have hbase : 1 + Real.log (W * (N : ℝ)) ≤
      (W + 3) * Real.log T := by
    have hnonneg : 0 ≤ (W + 1) * (Real.log T - 1) := by positivity
    rw [hlogMul]
    nlinarith
  have heE : e + 2 ≤ E := by
    dsimp only [E]
    omega
  have hpowExponent :
      (1 + Real.log (W * (N : ℝ))) ^ (e + 2) ≤
        (1 + Real.log (W * (N : ℝ))) ^ E :=
    pow_le_pow_right₀ hbase1 heE
  have hpowBase :
      (1 + Real.log (W * (N : ℝ))) ^ E ≤
        ((W + 3) * Real.log T) ^ E :=
    pow_le_pow_left₀ (zero_le_one.trans hbase1) hbase E
  have hcost : 24 * W ^ 2 *
      (1 + Real.log (W * (N : ℝ))) ^ (e + 2) ≤
        C * Real.log T ^ E := by
    calc
      24 * W ^ 2 * (1 + Real.log (W * (N : ℝ))) ^ (e + 2) ≤
          24 * W ^ 2 * ((W + 3) * Real.log T) ^ E := by
        gcongr
        exact hpowExponent.trans hpowBase
      _ = C * Real.log T ^ E := by
        rw [mul_pow]
        dsimp only [C]
        ring
  have hhalf : (1 / 2 : ℝ) * T ^ (1 / 400 : ℝ) ≤
      T ^ (1 / 400 : ℝ) := by nlinarith
  simpa only [W] using hcost.trans (hsmallScaled.trans hhalf)

/-- One fixed literal selected-cell fibre reaches the lower-strip tuned Montgomery scale. -/
theorem exists_maynardWindowRelevantSelectedCell_fibre_tuned_montgomery
    (L X : ℕ) {T mu N0 c alpha delta : ℝ}
    (hT : 1 < T) (hc : 0 ≤ c)
    (hmuLo : 4 / 3 ≤ mu) (_hmuHi : mu ≤ 19 / 9)
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
/-- Exact two-term count extracted from the literal selected-cell Montgomery inequality.  Unlike
the older height-dominated corollary, this statement does not assume the raised length exceeds
the observation height. -/
theorem card_le_of_selected_montgomery_two_term_fixed_polylog_raw
    {L X : ℕ} {T c alpha delta : ℝ}
    (hT : 0 < T) (hdelta : 0 < delta)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (ell : ℕ) (hell : 0 < ell) (hell90 : ell ≤ 90)
    (hMontgomery :
      IsMaynardSelectedMontgomeryBound (3 * T) c alpha delta label S ell) :
    let Y : ℝ := (((groupedDyadicLower
      (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)
    let W : ℝ := maynardMontgomeryRaisedWidthConstant
    let e : ℕ := 2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
      (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
    (S.card : ℝ) ≤
      W * (1 / delta + 2 * Real.log (W * Y)) *
        (1 + Real.log (W * Y)) ^ e *
          (3 * T * Y ^ (1 - 2 * alpha) +
            W * (4 * (1 + Real.log (W * Y))) * Y ^ (2 - 2 * alpha)) := by
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let M : ℕ := groupedDyadicUpper (heathBrownSelectedExponent label)
  let Y : ℝ := ((A ^ ell : ℕ) : ℝ)
  let Z : ℝ := ((M ^ ell : ℕ) : ℝ)
  let W : ℝ := maynardMontgomeryRaisedWidthConstant
  let e : ℕ := 2 * (Fintype.card (HeathBrownSelectedFactor label) * ell) +
    (2 ^ (2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1) * ell)) - 1)
  let PL : ℝ := (1 + Real.log (W * Y)) ^ e
  let D : ℝ := 4 * (1 + Real.log (W * Y))
  let B : ℝ := 1 / delta + 2 * Real.log (W * Y)
  let C : ℝ := (3 * T + 4 * Z * (1 + Real.log Z)) *
    (1 / delta + 2 * Real.log Z)
  let G : ℝ := heathBrownSelectedRaisedEnergy label ell
  have hY1 : 1 ≤ Y := by
    dsimp only [Y, A]
    exact_mod_cast Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hW1 : 1 ≤ W := by
    simpa only [W] using maynardMontgomeryRaisedWidthConstant_one_le
  have hW0 : 0 ≤ W := zero_le_one.trans hW1
  have hWY1 : 1 ≤ W * Y := one_le_mul_of_one_le_of_one_le hW1 hY1
  have hWYpos : 0 < W * Y := zero_lt_one.trans_le hWY1
  have hZwidth : Z ≤ W * Y := by
    simpa only [Z, M, W, Y, A] using
      heathBrownSelected_raisedUpper_le_montgomeryWidth label hell90
  have hZ1 : 1 ≤ Z := by
    dsimp only [Z, M]
    exact_mod_cast Nat.one_le_pow ell
      (groupedDyadicUpper (heathBrownSelectedExponent label))
      (one_le_groupedDyadicUpper _)
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ1
  have hlogZ0 : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have hlogWY0 : 0 ≤ Real.log (W * Y) := Real.log_nonneg hWY1
  have hlog : Real.log Z ≤ Real.log (W * Y) :=
    Real.log_le_log hZpos hZwidth
  have hlogOne : 1 + Real.log Z ≤ 1 + Real.log (W * Y) := by linarith
  have hlength : 4 * Z * (1 + Real.log Z) ≤ W * Y * D := by
    dsimp only [D]
    have hprod : Z * (1 + Real.log Z) ≤
        (W * Y) * (1 + Real.log (W * Y)) :=
      mul_le_mul hZwidth hlogOne (by linarith) hWYpos.le
    nlinarith
  have hsecond : 1 / delta + 2 * Real.log Z ≤ B := by
    dsimp only [B]
    linarith
  have hsecond0 : 0 ≤ 1 / delta + 2 * Real.log Z := by
    exact add_nonneg (one_div_nonneg.mpr hdelta.le)
      (mul_nonneg (by norm_num) hlogZ0)
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    exact add_nonneg (one_div_nonneg.mpr hdelta.le)
      (mul_nonneg (by norm_num) hlogWY0)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hC : C ≤ (3 * T + W * Y * D) * B := by
    dsimp only [C]
    exact mul_le_mul (add_le_add le_rfl hlength) hsecond hsecond0
      (add_nonneg (by positivity) (mul_nonneg (mul_nonneg hW0 hYpos.le) hD0))
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    exact heathBrownSelectedRaisedEnergy_nonneg label ell
  have hPL0 : 0 ≤ PL := by
    dsimp only [PL]
    positivity
  have hG : G ≤ W * Y * PL := by
    simpa only [G, W, Y, A, PL, e] using
      heathBrownSelectedRaisedEnergy_le_lower_montgomery_fixed_polylog
        label ell hell hell90
  have hraw : (S.card : ℝ) * (Y ^ (alpha - c)) ^ 2 ≤
      C * (Y ^ (-c)) ^ 2 * G := by
    simpa only [IsMaynardSelectedMontgomeryBound, C, G, Y, Z, A, M,
      Nat.cast_pow, mul_assoc] using hMontgomery
  simpa only [Y, W, e, PL, D, B, A, mul_assoc] using
    (montgomery_amplitude_two_term_cancellation hYpos hG0 (by positivity)
      hW0 hD0 hB0 hPL0 hC hG hraw)

set_option maxHeartbeats 1000000 in
/-- **Literal lower-strip selected-cell count.**  First crossing of `T^(4/5)`, exact two-term
Montgomery cancellation, and one fixed-polylog absorption put every selected-cell fibre with
`3/4 ≤ alpha ≤ 19/25` directly inside Route T's second alternative.  The theorem already
allows an external `T^(1/400)` multiplier for the later finite-label sum. -/
theorem eventually_maynardWindowRelevantSelectedCell_scaled_fibre_second_of_low_amplitude :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
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
    exists_maynardWindowRelevantSelectedCell_fibre_tuned_montgomery
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
    have hbeta : beta < 559 / 540 := by linarith
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
    routeT_wide_tunedMontgomery_exponents_with_polylog_le_second
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

end RHTower.Sieve
