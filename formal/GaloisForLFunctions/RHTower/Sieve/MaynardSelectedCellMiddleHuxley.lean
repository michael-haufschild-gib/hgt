import GaloisForLFunctions.RHTower.Sieve.MaynardMiddleFixedCost
import GaloisForLFunctions.RHTower.Sieve.MaynardMiddleScalar
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedCellFibreHuxley
import GaloisForLFunctions.RHTower.Sieve.MaynardSelectedWindowHuxleyCount

/-!
# Middle-strip selected cells: global-or-windowed Huxley

For a selected cell of exponent `beta < 1`, choose an adjacent optimizer power at the slightly
lower reference amplitude `alpha0`.  If that power crosses the optimizer, the global Huxley first
term applies.  Otherwise local absorption on canonical ordinate windows gives the cubic term.
The adjacent-power scalar theorem controls both cases with one exponent.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

noncomputable section
namespace RHTower.Sieve

open Finset ArithmeticFunction Complex Filter Topology

def maynardMiddleHuxleyEnergyCostConstant : ℝ :=
  2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
    maynardWideHuxleyEnergyEnvelopeConstant

def maynardMiddleHuxleyCountCostConstant : ℝ :=
  3 * (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant)

theorem maynardMiddleHuxleyEnergyCostConstant_pos :
    0 < maynardMiddleHuxleyEnergyCostConstant := by
  dsimp only [maynardMiddleHuxleyEnergyCostConstant]
  positivity [maynardMontgomeryRaisedWidthConstant_one_le,
    maynardWideHuxleyEnergyEnvelopeConstant_pos]

theorem maynardMiddleHuxleyCountCostConstant_pos :
    0 < maynardMiddleHuxleyCountCostConstant := by
  dsimp only [maynardMiddleHuxleyCountCostConstant]
  positivity [maynardMontgomeryRaisedWidthConstant_one_le]

/-- **Literal middle-strip count for every selected cell with exponent below one.** -/
theorem eventually_maynardWindowRelevantSelectedCell_middle_adjacent_count :
    ∀ᶠ T : ℝ in atTop,
      ∀ {L X K : ℕ} {mu N0 c alpha delta : ℝ},
      4 / 3 ≤ mu → mu ≤ 8 →
      1 / 2 ≤ c → 19 / 25 ≤ alpha → alpha ≤ 997 / 1000 →
      0 < delta →
      ∀ (label : HeathBrownSelectionLabel L X 60),
      maynardSubHeightSelectedExponent T label < 1 →
      ∀ (S : Finset ℕ), S.Nonempty → S ⊆ Finset.range K →
      ∀ (lam : ℕ → ℝ),
      (∀ i, lam i + delta ≤ lam (i + 1)) →
      (∀ r ∈ S, T ≤ lam r ∧ lam r ≤ 2 * T) →
      (∀ r ∈ S, IsMaynardWindowRelevantSelectedCell
        L X T mu N0 c (lam r) alpha label) →
      (S.card : ℝ) ≤ maynardHarmonicFactor K delta *
        T ^ (2 * (1 - maynardMiddleReferenceAmplitude alpha) /
          maynardMiddleReferenceAmplitude alpha +
          maynardLongGlobalAmplitudeDeficit / 100000) := by
  filter_upwards [eventually_maynardMiddleFixedLogCost_absorbed
      maynardMiddleHuxleyEnergyCostConstant
      maynardMiddleHuxleyEnergyCostConstant_pos 0 100000 (by norm_num),
    eventually_maynardMiddleFixedLogCost_absorbed
      maynardMiddleHuxleyCountCostConstant
      maynardMiddleHuxleyCountCostConstant_pos 0 100000 (by norm_num),
    eventually_gt_atTop (1 : ℝ)] with T henergyCost hcountCost hT
  intro L X K mu N0 c alpha delta hmuLo hmuHi hc halphaLo halphaHi hdelta
    label hbetaHi S hSne hS lam hgap hband hselection
  let d : ℝ := maynardLongGlobalAmplitudeDeficit
  let alpha0 : ℝ := maynardMiddleReferenceAmplitude alpha
  let beta : ℝ := maynardSubHeightSelectedExponent T label
  have hd : 0 < d := maynardLongGlobalAmplitudeDeficit_pos
  have ha0Range := maynardMiddleReferenceAmplitude_range halphaLo halphaHi
  have ha0pos : 0 < alpha0 := lt_of_lt_of_le (by norm_num) ha0Range.1
  have ha0One : alpha0 < 1 := ha0Range.2
  have halpha0 : 0 < alpha := by linarith
  have ha0le : alpha0 ≤ alpha := by
    dsimp only [alpha0, maynardMiddleReferenceAmplitude, d]
    linarith
  obtain ⟨r0, hr0⟩ := hSne
  rcases hselection r0 hr0 with
    ⟨_helig0, _hrel0, _hcore0, _hune0, _husub0, hbetaT,
      _hbetaUpper0, hlength0, _hlarge0, _hbranch0⟩
  have hbetaLo : 1 / 90 ≤ beta := by
    have : mu / 120 ≤ beta := by simpa only [beta] using hbetaT
    linarith
  have hbeta0 : 0 < beta := lt_of_lt_of_le (by norm_num) hbetaLo
  have hbetaOne : beta ≤ 1 := hbetaHi.le
  obtain ⟨ell, hell, hell90, hrHalf, hexponent⟩ :=
    exists_maynard_adjacent_optimizer_raise ha0Range.1 ha0One hbetaLo hbetaOne
  let rExp : ℝ := (ell : ℝ) * beta
  let A : ℕ := groupedDyadicLower (heathBrownSelectedExponent label)
  let N : ℕ := A ^ ell
  let Y : ℝ := (N : ℝ)
  let w : ℕ := Fintype.card (HeathBrownSelectedFactor label)
  let e : ℕ := 2 * (w * ell) + (2 ^ (2 * ((w + 1) * ell)) - 1)
  let PL : ℝ :=
    (1 + Real.log (maynardMontgomeryRaisedWidthConstant * Y)) ^ e
  let C : ℝ := maynardMontgomeryRaisedWidthConstant * PL
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hAeq : (A : ℝ) = T ^ beta := by
    simpa only [A, beta] using hlength0
  have hYeq : Y = T ^ rExp := by
    dsimp only [Y, N]
    rw [Nat.cast_pow, hAeq, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    congr 1
    dsimp only [rExp]
    ring
  have hN : 1 ≤ N := by
    dsimp only [N, A]
    exact Nat.one_le_pow ell _ (one_le_groupedDyadicLower _)
  have hY1 : 1 ≤ Y := by
    dsimp only [Y]
    exact_mod_cast hN
  have hYpos : 0 < Y := zero_lt_one.trans_le hY1
  have hrNonneg : 0 ≤ rExp := by
    dsimp only [rExp]
    positivity
  have hr90 : rExp ≤ 90 := by
    have hellCast : (ell : ℝ) ≤ 90 := by exact_mod_cast hell90
    dsimp only [rExp]
    nlinarith
  have hNscale : (N : ℝ) ≤ T ^ (90 : ℕ) := by
    rw [show (N : ℝ) = Y by rfl, hYeq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hr90
  have heBound : e ≤ maynardMontgomeryFixedPolylogExponentBound := by
    dsimp only [e, w]
    exact heathBrownSelected_montgomeryFixedPolylogExponent_le label hell90
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
  have hreserveExponent : d / 100000 ≤ rExp * (2 * (alpha - alpha0)) := by
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
  have henergy : heathBrownSelectedRaisedEnergy label ell ≤ C * Y := by
    have hraw := heathBrownSelectedRaisedEnergy_le_lower_montgomery_fixed_polylog
      label ell hell hell90
    calc
      heathBrownSelectedRaisedEnergy label ell ≤
          maynardMontgomeryRaisedWidthConstant * Y * PL := by
        simpa only [Y, N, A, PL, e, w] using hraw
      _ = C * Y := by dsimp only [C]; ring
  have hC0 : 0 ≤ C := by
    dsimp only [C, PL]
    have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * Y :=
      one_le_mul_of_one_le_of_one_le
        maynardMontgomeryRaisedWidthConstant_one_le hY1
    exact mul_nonneg (zero_le_one.trans maynardMontgomeryRaisedWidthConstant_one_le)
      (pow_nonneg (by linarith [Real.log_nonneg hprod]) e)
  have hlarge : ∀ r ∈ S,
      Y ^ (alpha - c) ≤
        ‖(∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam r : ℝ) * Complex.I)) ^ ell‖ := by
    intro s hs
    rcases hselection s hs with
      ⟨_helig, _hrel, _hcore, _hune, _husub, _hbetaT, _hbetaUpper,
        _hlength, hbaseLarge, _hbranch⟩
    have hbase : (A : ℝ) ^ (alpha - c) ≤
        ‖∏ i : HeathBrownSelectedFactor label, LSeries
          (complexCoeff (arithmeticDyadicBlock
            (heathBrownFactorBase L X (heathBrownSelectedKind label i))
            (heathBrownSelectedExponent label i)))
              ((c : ℂ) + (lam s : ℝ) * Complex.I)‖ := by
      simpa only [A] using hbaseLarge
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (by positivity : 0 ≤ (A : ℝ)) _)
      hbase ell
    have hrewrite : Y ^ (alpha - c) = ((A : ℝ) ^ (alpha - c)) ^ ell := by
      dsimp only [Y, N]
      rw [Nat.cast_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : 0 ≤ (A : ℝ)), mul_comm,
        Real.rpow_mul (by positivity : 0 ≤ (A : ℝ)), Real.rpow_natCast]
    calc
      Y ^ (alpha - c) = ((A : ℝ) ^ (alpha - c)) ^ ell := hrewrite
      _ ≤ ‖∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i)))
                ((c : ℂ) + (lam s : ℝ) * Complex.I)‖ ^ ell := hpow
      _ = ‖(∏ i : HeathBrownSelectedFactor label, LSeries
            (complexCoeff (arithmeticDyadicBlock
              (heathBrownFactorBase L X (heathBrownSelectedKind label i))
              (heathBrownSelectedExponent label i)))
                ((c : ℂ) + (lam s : ℝ) * Complex.I)) ^ ell‖ := by rw [norm_pow]
  have hdiam : ∀ r ∈ S, ∀ s ∈ S, |lam s - lam r| ≤ T := by
    intro r hr s hs
    have hrb := hband r hr
    have hsb := hband s hs
    rw [abs_le]
    constructor <;> linarith
  have hhalfY : T ^ (1 / 2 : ℝ) ≤ Y := by
    rw [hYeq]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hrHalf
  have hheightGlobal : T ≤ 8 * Real.pi * Y ^ 2 := by
    have hsquare := pow_le_pow_left₀ (Real.rpow_nonneg hT0.le _) hhalfY 2
    have hcollapse : (T ^ (1 / 2 : ℝ)) ^ 2 = T := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
      norm_num
    rw [hcollapse] at hsquare
    have hpi : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact hsquare.trans (by nlinarith [sq_nonneg Y])
  have hscaleOf : ∀ {H : ℝ}, 1 < H →
      H ^ maynardHuxleyOptimizer alpha0 ≤ Y →
      2 * ((Fintype.card (HeathBrownSelectedFactor label) * ell + 1 : ℕ) : ℝ) ^ 2 *
          heathBrownSelectedRaisedEnergy label ell *
          (1 + 256 * (Real.sqrt H +
            8 * Real.sqrt
              ((((groupedDyadicUpper
                (heathBrownSelectedExponent label)) ^ ell : ℕ) : ℝ)))) ≤
        Y ^ (2 * alpha) := by
    intro H hH hHY
    have hraw := maynard_wide_huxley_energy_scale_of_optimizer_reserve
      A w ell hH ha0Range.1 hC0
      (heathBrownSelectedRaisedEnergy_nonneg label ell)
      (card_heathBrownSelectedFactor_sixty_le label) hell hell90
      (by simpa only [Y, N] using hHY)
      (by simpa only [C, Y] using henergy) henergyReserve
    simpa only [A, w, Y, N, groupedDyadicUpper_eq_lower_mul_twoPow] using hraw
  let K0 : ℝ := 2 * (1 - alpha0) / alpha0
  have hwidth0 : rExp * (2 - 2 * alpha0) ≤ K0 := by
    have := (max_le_iff.mp (by simpa only [maynardHuxleyRaisedCountExponent, rExp,
      K0] using hexponent)).1
    exact this
  have hsecond0 : 1 + rExp * (4 - 6 * alpha0) ≤ K0 := by
    have := (max_le_iff.mp (by simpa only [maynardHuxleyRaisedCountExponent, rExp,
      K0] using hexponent)).2
    exact this
  by_cases hcross : maynardHuxleyOptimizer alpha0 ≤ rExp
  · have hYlo : T ^ maynardHuxleyOptimizer alpha0 ≤ Y := by
      rw [hYeq]
      exact Real.rpow_le_rpow_of_exponent_le hT.le hcross
    have hscale := hscaleOf hT hYlo
    have hHuxley : IsMaynardSelectedHuxleyBound K c alpha delta label S ell := by
      unfold IsMaynardSelectedHuxleyBound
      exact huxley_heathBrown_grouped_large_values_finset_at_amplitude
        L X ell K (heathBrownSelectedKind label) (heathBrownSelectedExponent label)
        (by linarith) (heathBrownSelectedRaisedEnergy label ell)
        (heathBrownSelectedRaisedEnergy_nonneg label ell) le_rfl hS hdelta hT0.le
        hgap hdiam hheightGlobal (by simpa only [Y, N, A] using hlarge)
        (by simpa only [Y, N, A] using hscale)
    have hraw := card_le_of_selected_wide_huxley_with_fixed_polylog_raw
      hc (by linarith) hdelta label S ell hell hell90 hHuxley
    have hcostSmall :
        (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant) * PL ≤
          T ^ (d / 100000) := by
      have hcoeff0 : 0 ≤
          2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL := by
        have hPL0 : 0 ≤ PL := by
          dsimp only [PL]
          have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * Y :=
            one_le_mul_of_one_le_of_one_le
              maynardMontgomeryRaisedWidthConstant_one_le hY1
          exact pow_nonneg (by linarith [Real.log_nonneg hprod]) e
        exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
            (zero_le_one.trans maynardMontgomeryRaisedWidthConstant_one_le)) hPL0
      have hthree :
          2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL ≤
            maynardMiddleHuxleyCountCostConstant * PL := by
        have hid : maynardMiddleHuxleyCountCostConstant * PL =
            3 * (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL) := by
          unfold maynardMiddleHuxleyCountCostConstant
          ring
        rw [hid]
        nlinarith
      exact hthree.trans hcountFixed
    have hwidth : rExp * (2 - 2 * alpha) ≤ K0 := by
      have hcoef := mul_le_mul_of_nonneg_left (by linarith : 2 - 2 * alpha ≤
        2 - 2 * alpha0) hrNonneg
      exact hcoef.trans hwidth0
    have hpowCost := mul_le_mul hcostSmall
      (Real.rpow_le_rpow_of_exponent_le hT.le hwidth)
      (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hT0.le _)
    have hcombine : T ^ (d / 100000) * T ^ K0 =
        T ^ (K0 + d / 100000) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    calc
      (S.card : ℝ) ≤
          2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
            maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha) := by
        simpa only [PL, e, w, Y, N, A] using hraw
      _ = maynardHarmonicFactor K delta *
          ((2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant * PL) *
            T ^ (rExp * (2 - 2 * alpha))) := by
        rw [hYeq, ← Real.rpow_mul hT0.le]
        ring
      _ ≤ maynardHarmonicFactor K delta *
          (T ^ (d / 100000) * T ^ K0) :=
        mul_le_mul_of_nonneg_left hpowCost
          (maynardHarmonicFactor_pos K hdelta).le
      _ = maynardHarmonicFactor K delta *
          T ^ (K0 + d / 100000) := by rw [hcombine]
      _ = maynardHarmonicFactor K delta *
          T ^ (2 * (1 - maynardMiddleReferenceAmplitude alpha) /
            maynardMiddleReferenceAmplitude alpha + d / 100000) := by rfl
  · have hbelow : rExp < maynardHuxleyOptimizer alpha0 := lt_of_not_ge hcross
    let omega : ℝ := rExp * (4 * alpha0 - 2)
    let W : ℝ := T ^ omega
    have hfactor : 0 < 4 * alpha0 - 2 := by linarith
    have homega0 : 0 < omega := by
      dsimp only [omega]
      exact mul_pos (by linarith [hrHalf]) hfactor
    have homegaOne : omega < 1 := by
      have hopt : maynardHuxleyOptimizer alpha0 = 1 / (4 * alpha0 - 2) := rfl
      rw [hopt] at hbelow
      have hmul := mul_lt_mul_of_pos_right hbelow hfactor
      dsimp only [omega]
      field_simp [hfactor.ne'] at hmul
      exact hmul
    have hW : 1 < W := by
      dsimp only [W]
      exact Real.one_lt_rpow hT homega0
    have hWopt : W ^ maynardHuxleyOptimizer alpha0 = Y := by
      dsimp only [W, omega, maynardHuxleyOptimizer]
      rw [← Real.rpow_mul hT0.le, hYeq]
      congr 1
      field_simp [hfactor.ne']
    have hscale := hscaleOf hW hWopt.le
    have hheightW : W ≤ 8 * Real.pi * Y ^ 2 := by
      have hfactorTwo : 4 * alpha0 - 2 ≤ 2 := by linarith
      have homegaTwo : omega ≤ 2 * rExp := by
        dsimp only [omega]
        nlinarith
      have hpow := Real.rpow_le_rpow_of_exponent_le hT.le homegaTwo
      have hYsq : T ^ (2 * rExp) = Y ^ 2 := by
        rw [hYeq, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        congr 1
        ring
      rw [hYsq] at hpow
      have hpi : (1 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
      exact hpow.trans (by nlinarith [sq_nonneg Y])
    have hband' : ∀ r ∈ S, 0 ≤ lam r ∧ lam r ≤ 2 * T := by
      intro s hs
      exact ⟨(by linarith [(hband s hs).1, hT0]), (hband s hs).2⟩
    have hraw := card_le_of_selected_wide_huxley_windows
      (T := 2 * T) (W := W)
      hc (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hc)
      (halphaHi.trans (by norm_num : (997 / 1000 : ℝ) ≤ 1))
      hdelta (by positivity : 0 ≤ 2 * T) (zero_lt_one.trans hW)
      label S hS lam hgap hband' ell hell hell90
      (by simpa only [W, Y, N, A] using hheightW)
      (by simpa only [Y, N, A] using hlarge)
      (by simpa only [W, Y, N, A] using hscale)
    have hwindowCast := huxleyWindowCount_cast_le (T := 2 * T) (W := W)
      (by positivity) (zero_lt_one.trans hW)
    have hquot : 2 * T / W = 2 * T ^ (1 - omega) := by
      dsimp only [W]
      rw [Real.rpow_sub hT0, Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hT0 omega).ne']
    have hpowOne : 1 ≤ T ^ (1 - omega) :=
      Real.one_le_rpow hT.le (by linarith : 0 ≤ 1 - omega)
    have hwindow : (huxleyWindowCount (2 * T) W : ℝ) ≤
        3 * T ^ (1 - omega) := by
      rw [hquot] at hwindowCast
      linarith
    have hlocalExponent :
        1 - omega + rExp * (2 - 2 * alpha) ≤ K0 := by
      have hcompare :
          1 - omega + rExp * (2 - 2 * alpha) ≤
            1 + rExp * (4 - 6 * alpha0) := by
        dsimp only [omega]
        have hmul := mul_le_mul_of_nonneg_left ha0le hrNonneg
        nlinarith
      exact hcompare.trans hsecond0
    have hnonnegRaw : 0 ≤
        2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
          maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha) := by
      have hPL0 : 0 ≤ PL := by
        dsimp only [PL]
        have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * Y :=
          one_le_mul_of_one_le_of_one_le
            maynardMontgomeryRaisedWidthConstant_one_le hY1
        exact pow_nonneg (by linarith [Real.log_nonneg hprod]) e
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
              (zero_le_one.trans maynardMontgomeryRaisedWidthConstant_one_le))
            (maynardHarmonicFactor_pos K hdelta).le) hPL0)
        (Real.rpow_nonneg hYpos.le _)
    have hwindowMul := mul_le_mul_of_nonneg_right hwindow hnonnegRaw
    have hpowCost := mul_le_mul hcountFixed
      (Real.rpow_le_rpow_of_exponent_le hT.le hlocalExponent)
      (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hT0.le _)
    have hcombine : T ^ (d / 100000) * T ^ K0 =
        T ^ (K0 + d / 100000) := by
      rw [← Real.rpow_add hT0]
      congr 1
      ring
    have hpows : T ^ (1 - omega) * T ^ (rExp * (2 - 2 * alpha)) =
        T ^ (1 - omega + rExp * (2 - 2 * alpha)) := by
      rw [← Real.rpow_add hT0]
    calc
      (S.card : ℝ) ≤
          (huxleyWindowCount (2 * T) W : ℝ) *
            (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
              maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha)) := by
        simpa only [PL, e, w, Y, N, A] using hraw
      _ ≤ (3 * T ^ (1 - omega)) *
            (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant *
              maynardHarmonicFactor K delta * PL * Y ^ (2 - 2 * alpha)) :=
        hwindowMul
      _ = maynardHarmonicFactor K delta *
          ((maynardMiddleHuxleyCountCostConstant * PL) *
            T ^ (1 - omega + rExp * (2 - 2 * alpha))) := by
        rw [hYeq, ← Real.rpow_mul hT0.le]
        rw [show maynardMiddleHuxleyCountCostConstant =
          3 * (2 * (10801 : ℝ) ^ 2 * maynardMontgomeryRaisedWidthConstant) by
            rfl]
        rw [← hpows]
        ring
      _ ≤ maynardHarmonicFactor K delta *
          (T ^ (d / 100000) * T ^ K0) :=
        mul_le_mul_of_nonneg_left hpowCost
          (maynardHarmonicFactor_pos K hdelta).le
      _ = maynardHarmonicFactor K delta * T ^ (K0 + d / 100000) := by
        rw [hcombine]
      _ = maynardHarmonicFactor K delta *
          T ^ (2 * (1 - maynardMiddleReferenceAmplitude alpha) /
            maynardMiddleReferenceAmplitude alpha + d / 100000) := by rfl

end RHTower.Sieve
