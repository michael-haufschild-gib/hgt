import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellMiddleHuxley

/-!
# Middle-strip overweight selected cell

The unique spill cell has exponent `beta >= 1`.  It already lies beyond Huxley's optimizer, so no
ordinate windows or raising are needed.  The distinguished zeta/log atom in the selection branch
forces `alpha <= 983/1000`; the resulting receiver margin accommodates the literal `1 + mu/60`
packing cap.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

/-- Literal global Huxley count for the selected spill cell. -/
theorem eventually_maynardWindowRelevantSelectedCell_middle_overweight_count :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 19 / 9 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60),
      1 ≤ maynardSubHeightSelectedExponent T label →
      ∀ (S : Finset ℕ), S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      let beta := maynardSubHeightSelectedExponent T label
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (beta * (2 - 2 * alpha) + maynardLongGlobalAmplitudeDeficit / 100000) := by
  filter_upwards [eventually_maynardMiddleFixedLogCost_absorbed
      maynardMiddleHuxleyEnergyCostConstant
      maynardMiddleHuxleyEnergyCostConstant_pos 0 100000 (by norm_num),
    eventually_maynardMiddleFixedLogCost_absorbed
      maynardMiddleHuxleyCountCostConstant
      maynardMiddleHuxleyCountCostConstant_pos 0 100000 (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with T henergyCost hcountCost hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaHi hdelta
    label hbetaLo S hSne hS lam hgap hband hselection
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let alpha0 : ℝ := maynardMiddleReferenceAmplitude alpha
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let N : ℕ := A
  let Y : ℝ := (N : ℝ)
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let e : ℕ := 2 * w + (2 ^ (2 * (w + 1)) - 1)
  let PL : ℝ := (1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y)) ^ e
  let C : ℝ := maynardMontgomeryRaisedWidthConstant * PL
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have ha0Range := maynardMiddleReferenceAmplitude_range halphaLo halphaHi
  have ha0pos : 0 < alpha0 := lt_of_lt_of_le (by norm_num) ha0Range.1
  have ha0le : alpha0 ≤ alpha := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    linarith
  have hT0 : 0 < T := zero_lt_one.trans hT
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig0, _hrel0, _hcore0, _hune0, _husub0, _hbetaT,
      hbetaUpper, hlength0, _hlarge0, hbranch0⟩
  have hbetaHi : beta < 1 + mu / 60 := by
    have hbetaUpper' : beta < 1 + 2 * (mu / 120) := by
      simpa only [beta] using hbetaUpper
    linarith
  have hbeta0 : 0 < beta := lt_of_lt_of_le zero_lt_one hbetaLo
  have hbeta90 : beta ≤ 90 := by linarith
  have halpha99 : alpha ≤ 99 / 100 := by
    rcases hbranch0 with hsmall | hmoderate | hoverweight
    · have hsmall' : beta ≤ 5 / 12 := by
        simpa only [IsMaynardSelectedCellBranch, beta] using hsmall
      linarith
    · have hmoderate' : beta < 1 := by
        simpa only [IsMaynardSelectedCellBranch, beta] using hmoderate.2.1
      linarith
    · have halpha983 : alpha ≤ 983 / 1000 := by
        simpa only [IsMaynardSelectedCellBranch, beta] using hoverweight.2.1
      linarith
  have hAeq : (A : ℝ) = T ^ beta := by
    simpa only [A, beta] using hlength0
  have hYeq : Y = T ^ beta := by
    simpa only [Y, N] using hAeq
  have hN : 1 ≤ N := by
    dsimp only [N, A]
    exact one_le_groupedDyadicLower _
  have hY1 : 1 ≤ Y := by
    dsimp only [Y]
    exact_mod_cast hN
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hNscale : (N : ℝ) ≤ T ^ (90 : ℕ) := by
    rw [show (N : ℝ) = Y by rfl, hYeq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hbeta90
  have heBound : e ≤ maynardMontgomeryFixedPolylogExponentBound := by
    have hraw := heathBrownSelected_montgomeryFixedPolylogExponent_le label
      (by norm_num : 1 ≤ 90)
    simpa only [e, w, Nat.mul_one, Nat.one_mul] using hraw
  have henergyCostRaw := henergyCost N e hN hNscale heBound
  have hcountCostRaw := hcountCost N e hN hNscale heBound
  have henergyFixed :
      maynardMiddleHuxleyEnergyCostConstant * PL ≤ T ^ (d / 100000) := by
    norm_num at henergyCostRaw ⊢
    simpa only [PL, Y, d] using henergyCostRaw
  have hcountFixed :
      maynardMiddleHuxleyCountCostConstant * PL ≤ T ^ (d / 100000) := by
    norm_num at hcountCostRaw ⊢
    simpa only [PL, Y, d] using hcountCostRaw
  have hdiff : alpha - alpha0 = d / 100000 := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    ring
  have hreserveExponent : d / 100000 ≤ beta * (2 * (alpha - alpha0)) := by
    rw [hdiff]
    nlinarith
  have hreservePower : T ^ (d / 100000) ≤ Y ^ (2 * (alpha - alpha0)) := by
    rw [hYeq, ← Real.rpow_mul hT0.le]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hreserveExponent
  have henergyReserve :
      2 * (10801 : ℝ) ^ 2 * C * maynardWideHuxleyEnergyEnvelopeConstant ≤
        Y ^ (2 * (alpha - alpha0)) := by
    calc
      2 * (10801 : ℝ) ^ 2 * C * maynardWideHuxleyEnergyEnvelopeConstant =
          maynardMiddleHuxleyEnergyCostConstant * PL := by
        dsimp only [C, maynardMiddleHuxleyEnergyCostConstant]
        ring
      _ ≤ T ^ (d / 100000) := henergyFixed
      _ ≤ Y ^ (2 * (alpha - alpha0)) := hreservePower
  have henergy : heathBrownSelectedRaisedEnergy label 1 ≤ C * Y := by
    have hraw := heathBrownSelectedRaisedEnergy_le_lower_montgomery_fixed_polylog
      label 1 (by norm_num) (by norm_num)
    calc
      heathBrownSelectedRaisedEnergy label 1 ≤
          maynardMontgomeryRaisedWidthConstant * Y * PL := by
        simpa only [Y, N, A, PL, e, w, pow_one, Nat.mul_one, Nat.one_mul] using hraw
      _ = C * Y := by dsimp only [C]; ring
  have hC0 : 0 ≤ C := by
    dsimp only [C, PL]
    have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * Y :=
      one_le_mul_of_one_le_of_one_le maynardMontgomeryRaisedWidthConstant_one_le hY1
    exact mul_nonneg (zero_le_one.trans maynardMontgomeryRaisedWidthConstant_one_le)
      (pow_nonneg (by linarith [Real.log_nonneg hprod]) e)
  have hoptimizerOne : maynardHuxleyOptimizer alpha0 ≤ 1 := by
    dsimp only [maynardHuxleyOptimizer]
    rw [div_le_iff₀ (by linarith : 0 < 4 * alpha0 - 2)]
    linarith
  have hoptimizerBeta : maynardHuxleyOptimizer alpha0 ≤ beta :=
    hoptimizerOne.trans hbetaLo
  have hYlo : T ^ maynardHuxleyOptimizer alpha0 ≤ Y := by
    rw [hYeq]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hoptimizerBeta
  have henergyReserve' :
      2 * (10801 : ℝ) ^ 2 * C * maynardWideHuxleyEnergyEnvelopeConstant ≤
        (((A ^ 1 : ℕ) : ℝ)) ^ (2 * (alpha - alpha0)) := by
    simpa only [Y, N, pow_one] using henergyReserve
  have hscaleRaw := maynard_wide_huxley_energy_scale_of_optimizer_reserve
    A w 1 (alpha := alpha) (alpha0 := alpha0) hT ha0Range.1 hC0
    (heathBrownSelectedRaisedEnergy_nonneg label 1)
    (card_heathBrownSelectedFactor_sixty_le label) (by norm_num) (by norm_num)
    (by simpa only [Y, N, pow_one] using hYlo)
    (by simpa only [Y, N, pow_one] using henergy) henergyReserve'
  have hscale :
      2 * ((Fintype.card (HeathBrownSelectedFactor label) + 1 : ℕ) : ℝ) ^ 2 *
          heathBrownSelectedRaisedEnergy label 1 *
          (1 + 256 * (Real.sqrt T +
            8 * Real.sqrt
              ((groupedDyadicUpper (heathBrownSelectedExponent label) : ℕ) : ℝ))) ≤
        Y ^ (2 * alpha) := by
    simpa only [A, w, Y, N, pow_one, Nat.mul_one,
      groupedDyadicUpper_eq_lower_mul_twoPow] using hscaleRaw
  have hlarge : ∀ r ∈ S,
      Y ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ 1‖ := by
    intro s hs
    rcases hselection s hs with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, _hbetaUpper,
        _hlength, hbaseLarge, _hbranch⟩
    simpa only [Y, N, A, pow_one] using hbaseLarge
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hheight : T ≤ 8 * Real.pi * Y ^ 2 := by
    have hTY : T ≤ Y := by
      calc
        T = T ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ ≤ T ^ beta := Real.rpow_le_rpow_of_exponent_le hT.le hbetaLo
        _ = Y := hYeq.symm
    have hYsq : Y ≤ Y ^ 2 := by nlinarith
    have hpi : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact hTY.trans (hYsq.trans (by nlinarith [sq_nonneg Y]))
  have hHuxley : IsMaynardSelectedHuxleyBound K c alpha delta label S 1 := by
    unfold IsMaynardSelectedHuxleyBound
    exact huxley_heathBrown_grouped_large_values_finset_at_amplitude
      L X 1 K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hc)
      (heathBrownSelectedRaisedEnergy label 1)
      (heathBrownSelectedRaisedEnergy_nonneg label 1) le_rfl hS hdelta hT0.le
      hgap hdiam (by simpa only [Y, N, A, pow_one] using hheight)
      (by simpa only [Y, N, A, pow_one] using hlarge)
      (by simpa only [Y, N, A, pow_one, Nat.mul_one] using hscale)
  have hraw := card_le_of_selected_wide_huxley_with_fixed_polylog_raw
    hc (halphaHi.trans (by norm_num)) hdelta label S 1 (by norm_num) (by norm_num) hHuxley
  have hcostSmall :
      (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant) * PL ≤
        T ^ (d / 100000) := by
    have hPL0 : 0 ≤ PL := by
      dsimp only [PL]
      have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * Y :=
        one_le_mul_of_one_le_of_one_le maynardMontgomeryRaisedWidthConstant_one_le hY1
      exact pow_nonneg (by linarith [Real.log_nonneg hprod]) e
    have hbase0 : 0 ≤
        2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (zero_le_one.trans maynardMontgomeryRaisedWidthConstant_one_le)) hPL0
    have hid : maynardMiddleHuxleyCountCostConstant * PL =
        3 * (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL) := by
      unfold maynardMiddleHuxleyCountCostConstant
      ring
    have hthree :
        2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL ≤
          maynardMiddleHuxleyCountCostConstant * PL := by
      rw [hid]
      nlinarith
    exact hthree.trans hcountFixed
  have hpowCost := mul_le_mul_of_nonneg_right hcostSmall
    (Real.rpow_nonneg hT0.le (beta * (2 - 2 * alpha)))
  have hcombine : T ^ (d / 100000) * T ^ (beta * (2 - 2 * alpha)) =
      T ^ (beta * (2 - 2 * alpha) + d / 100000) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  dsimp only
  calc
    (S.card : ℝ) ≤
        2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
          maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha) := by
      simpa only [PL, e, w, Y, N, A, Nat.mul_one, Nat.one_mul, pow_one] using hraw
    _ = maynardHarmonicFactor K delta *
        ((2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL) *
          T ^ (beta * (2 - 2 * alpha))) := by
      rw [hYeq, ← Real.rpow_mul hT0.le]
      ring
    _ ≤ maynardHarmonicFactor K delta *
        (T ^ (d / 100000) * T ^ (beta * (2 - 2 * alpha))) :=
      mul_le_mul_of_nonneg_left hpowCost (maynardHarmonicFactor_pos K hdelta).le
    _ = maynardHarmonicFactor K delta *
        T ^ (beta * (2 - 2 * alpha) + d / 100000) := by rw [hcombine]

end RHTower.Sieve
