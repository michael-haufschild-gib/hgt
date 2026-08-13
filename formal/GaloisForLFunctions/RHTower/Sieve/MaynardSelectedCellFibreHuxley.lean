import GaloisForLFunctions.RHTower.Sieve.MaynardOptimizerHuxley

/-!
# Literal selected-cell fibres at the Huxley optimizer

Above the proved order-four amplitude barrier, every selected cell is in the small branch.  Its
first optimizer-crossing power is common across a finite color fibre, raises the literal product
threshold, and reaches canonical Huxley once the explicit amplitude reserve pays fixed-polylog
energy.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- One fixed selected-cell fibre reaches optimizer-scale Huxley. -/
theorem exists_maynardWindowRelevantSelectedCell_fibre_optimizer_huxley
    (L X K : ℕ) {T mu N0 c alpha alpha0 delta : ℝ}
    (hT : 1 < T) (hc : 0 ≤ c)
    (halphaCritical : 997 / 1000 < alpha) (halphaHi : alpha ≤ 1)
    (halpha0Lo : 99 / 100 ≤ alpha0) (halpha0Hi : alpha0 < 1)
    (halpha0 : alpha0 = alpha - (1 - alpha) / 100)
    (hmuLo : 4 / 3 ≤ mu)
    (label : HeathBrownSelectionLabel L X 60)
    (S : Finset ℕ) (hSne : S.Nonempty) (hS : S ⊆ Finset.range K)
    (lam : ℕ → ℝ) (hdelta : 0 < delta)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T)
    (hselection : ∀ r ∈ S,
      IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label)
    (hcost : ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T →
      e ≤ maynardFixedPolylogExponentBound →
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          (1 + Real.log (maynardRaisedWidthConstant * (N : ℝ))) ^ e *
          maynardEnergyEnvelopeConstant ≤
        T ^ ((1 - alpha) / 100)) :
    ∃ ell : ℕ, 0 < ell ∧ ell ≤ 51 ∧
      let beta := maynardSubHeightSelectedExponent T label
      maynardHuxleyOptimizer alpha0 ≤ (ell : ℝ) * beta ∧
      (ell : ℝ) * beta < maynardHuxleyOptimizer alpha0 + beta ∧
      maynardHuxleyRaisedCountExponent alpha0 ((ell : ℝ) * beta) ≤
        (19 / 10 : ℝ) * (1 - alpha0) / alpha0 ∧
      IsMaynardSelectedHuxleyBound K c alpha delta label S ell := by
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig, _hrel, _hcore, _hune, _husub, hbetaT, _hbetaHi,
      hlength, _hlarge, hbranch⟩
  let beta := maynardSubHeightSelectedExponent T label
  have hbetaLo : 1 / 90 ≤ beta := by
    have : mu / 120 ≤ beta := by simpa [beta] using hbetaT
    linarith
  have hsmall : beta ≤ 5 / 12 := by
    rcases hbranch with hsmall | hmoderate | hoverweight
    · simpa [IsMaynardSelectedCellBranch, beta] using hsmall
    · have := hmoderate.2.2.1
      linarith
    · have := hoverweight.2.1
      linarith
  obtain ⟨ell, hell, hell51, hcross, hover, hexponent⟩ :=
    exists_maynard_small_crossing_raise_high_amplitude
      halpha0Lo halpha0Hi hbetaLo hsmall
  let A : ℝ :=
    (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ)
  let Y : ℝ :=
    (((groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)
  have hAeq : A = T ^ beta := by
    simpa [A, beta] using hlength
  have hYeq : Y = T ^ ((ell : ℝ) * beta) := by
    dsimp only [Y]
    rw [Nat.cast_pow, show
      (groupedDyadicLower (heathBrownSelectedExponent label) : ℝ) = A by rfl,
      hAeq, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T)]
    congr 1
    ring
  have hYlo : T ^ maynardHuxleyOptimizer alpha0 ≤ Y := by
    rw [hYeq]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hcross
  have hthetaUpper : maynardHuxleyOptimizer alpha0 ≤ 25 / 49 := by
    dsimp only [maynardHuxleyOptimizer]
    rw [div_le_iff₀ (by linarith : 0 < 4 * alpha0 - 2)]
    nlinarith
  have hrOne : (ell : ℝ) * beta ≤ 1 := by
    have hsum : maynardHuxleyOptimizer alpha0 + beta < 1 := by
      have hfixed : (25 / 49 : ℝ) + 5 / 12 < 1 := by norm_num
      linarith
    exact hover.le.trans hsum.le
  have hYhi : Y ≤ T := by
    rw [hYeq]
    have hpow := Real.rpow_le_rpow_of_exponent_le hT.le hrOne
    simpa using hpow
  have hlarge : ∀ r ∈ S,
      Y ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖ := by
    intro r hr
    rcases hselection r hr with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, _hbetaHi,
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
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  let PL : ℝ := (1 + Real.log (maynardRaisedWidthConstant * Y)) ^ e
  let C : ℝ := maynardRaisedWidthConstant * PL
  have hC0 : 0 ≤ C := by
    have hY1 : 1 ≤ Y := by
      dsimp only [Y]
      exact_mod_cast Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
    have hlog0 : 0 ≤ 1 + Real.log (maynardRaisedWidthConstant * Y) := by
      have hprod : 1 ≤ maynardRaisedWidthConstant * Y :=
        one_le_mul_of_one_le_of_one_le maynardRaisedWidthConstant_one_le hY1
      linarith [Real.log_nonneg hprod]
    exact mul_nonneg (le_trans (by norm_num) maynardRaisedWidthConstant_one_le)
      (pow_nonneg hlog0 e)
  have henergy : heathBrownSelectedRaisedEnergy label ell ≤ C * Y := by
    have hraw := heathBrownSelectedRaisedEnergy_le_lower_fixed_polylog
      label ell hell hell51
    calc
      heathBrownSelectedRaisedEnergy label ell ≤
          maynardRaisedWidthConstant * Y * PL := by
        simpa [PL, e, w, Y] using hraw
      _ = C * Y := by dsimp only [C]; ring
  let N : ℕ :=
    (groupedDyadicLower (heathBrownSelectedExponent label)) ^ ell
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hNY : (N : ℝ) = Y := by rfl
  have heBound : e ≤ maynardFixedPolylogExponentBound := by
    dsimp only [e, w]
    exact heathBrownSelected_fixedPolylogExponent_le label hell51
  have hcostT :
      2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant *
          PL * maynardEnergyEnvelopeConstant ≤ T ^ ((1 - alpha) / 100) := by
    simpa [N, PL, e, w, Y] using hcost N e hN (by simpa [hNY] using hYhi) heBound
  have hthetaHalf : (1 / 2 : ℝ) < maynardHuxleyOptimizer alpha0 := by
    dsimp only [maynardHuxleyOptimizer]
    rw [lt_div_iff₀ (by linarith : 0 < 4 * alpha0 - 2)]
    linarith
  have hhalfOpt : T ^ (1 / 2 : ℝ) ≤ T ^ maynardHuxleyOptimizer alpha0 :=
    Real.rpow_le_rpow_of_exponent_le hT.le hthetaHalf.le
  have hhalfY := hhalfOpt.trans hYlo
  have hgap0 : 0 ≤ (1 - alpha) / 50 := by linarith
  have hreservePower : T ^ ((1 - alpha) / 100) ≤
      Y ^ (2 * (alpha - alpha0)) := by
    have hraise := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith : 0 ≤ T) _)
      hhalfY hgap0
    have hleft : (T ^ (1 / 2 : ℝ)) ^ ((1 - alpha) / 50) =
        T ^ ((1 - alpha) / 100) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
      congr 1
      ring
    have hright : Y ^ ((1 - alpha) / 50) = Y ^ (2 * (alpha - alpha0)) := by
      congr 1
      rw [halpha0]
      ring
    calc
      T ^ ((1 - alpha) / 100) =
          (T ^ (1 / 2 : ℝ)) ^ ((1 - alpha) / 50) := hleft.symm
      _ ≤ Y ^ ((1 - alpha) / 50) := hraise
      _ = Y ^ (2 * (alpha - alpha0)) := hright
  have henergyReserve :
      2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant ≤
        Y ^ (2 * (alpha - alpha0)) := by
    calc
      2 * (6121 : ℝ) ^ 2 * C * maynardEnergyEnvelopeConstant =
          2 * (6121 : ℝ) ^ 2 * maynardRaisedWidthConstant * PL *
            maynardEnergyEnvelopeConstant := by dsimp only [C]; ring
      _ ≤ T ^ ((1 - alpha) / 100) := hcostT
      _ ≤ Y ^ (2 * (alpha - alpha0)) := hreservePower
  have hscale :
      2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
          heathBrownSelectedRaisedEnergy label ell *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              ((((groupedDyadicUpper (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
        Y ^ (2 * alpha) := by
    have hraw := maynard_huxley_energy_scale_of_optimizer_reserve
      (groupedDyadicLower (heathBrownSelectedExponent label)) w ell
      hT halpha0Lo hC0 (heathBrownSelectedRaisedEnergy_nonneg label ell)
      (card_heathBrownSelectedFactor_sixty_le label) hell hell51
      (by simpa [Y] using hYlo) (by simpa [C, Y] using henergy)
      henergyReserve
    simpa [w, Y, groupedDyadicUpper_eq_lower_mul_twoPow] using hraw
  have hheight : T ≤ 8 * Real.pi * Y ^ 2 := by
    have hsquare := pow_le_pow_left₀ (Real.rpow_nonneg (by linarith : 0 ≤ T) _) hhalfY 2
    have hcollapse : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T)]
      norm_num
    rw [hcollapse] at hsquare
    have hpi : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    calc
      T ≤ Y ^ 2 := hsquare
      _ = 1 * Y ^ 2 := by ring
      _ ≤ (8 * Real.pi) * Y ^ 2 :=
        mul_le_mul_of_nonneg_right hpi (sq_nonneg Y)
  have hHuxley : IsMaynardSelectedHuxleyBound K c alpha delta label S ell := by
    unfold IsMaynardSelectedHuxleyBound
    apply huxley_heathBrown_grouped_large_values_finset_at_amplitude
      (c := c) (alpha := alpha) (S := S) (lam := lam) (delta := delta) (T := T)
      L X ell K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
      hc (heathBrownSelectedRaisedEnergy label ell)
      (heathBrownSelectedRaisedEnergy_nonneg label ell)
    · exact le_rfl
    · exact hS
    · exact hdelta
    · linarith
    · exact hgap
    · exact hdiam
    · simpa [Y] using hheight
    · simpa [Y] using hlarge
    · simpa [Y] using hscale
  exact ⟨ell, hell, hell51, hcross, hover, hexponent, hHuxley⟩

end RHTower.Sieve
