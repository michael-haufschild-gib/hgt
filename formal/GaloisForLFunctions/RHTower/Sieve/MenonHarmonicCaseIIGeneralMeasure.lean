import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIICountNumerator
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicExternalFrequencyAssembly

/-!
# A two-regime scalar envelope for Menon's Case-II measure

The literal order-four-hundred estimate contains the large-value denominator
`min T (a^kappa)`, followed by a fixed loss of 307 logarithms.  This file keeps the minimum
instead of restricting to its `T` branch.  The resulting bound is the form needed when the
frequency shells cross the Case-II core scale.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Absolute constant in the two-regime Case-II measure envelope. -/
def menonHarmonicCaseIIGeneralMeasureConstant : ℝ :=
  8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
    menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) + 8

theorem menonHarmonicCaseIIGeneralMeasureConstant_nonneg :
    0 ≤ menonHarmonicCaseIIGeneralMeasureConstant := by
  rw [menonHarmonicCaseIIGeneralMeasureConstant]
  rw [menonHarmonicCaseIIMeasureNumeratorConstant,
    menonHarmonicCaseIICoreDenominatorConstant,
    menonHarmonicCaseIIComplementConstant]
  positivity

set_option maxRecDepth 10000 in
/-- The raw scheduled Case-II measure is controlled on both sides of the physical
`T = a^kappa` crossover. -/
theorem menonHarmonicCaseII_generalMeasureEnvelope_le
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 1 ≤ T) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Vexp : ℝ :=
      min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) / ((D : ℝ) * 8))
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    2 * (2 * Real.pi)⁻¹ *
        (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) ≤
      menonHarmonicCaseIIGeneralMeasureConstant *
        ((Real.log (a : ℝ)) ^ (1855 : ℕ) * (T + 1) /
            (min T ((a : ℝ) ^ menonHarmonicCaseIICoreExponent)) ^ 2 + 1) := by
  dsimp only
  let la : ℝ := Real.log (a : ℝ)
  let core : ℝ := (a : ℝ) ^ menonHarmonicCaseIICoreExponent
  let M : ℝ := min T core
  let den : ℝ := menonHarmonicCaseIICoreDenominatorConstant * la ^ (307 : ℕ)
  let factor : ℝ :=
    1 / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
      ((2 * la ^ (-300 : ℝ)) /
        (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
            (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))
  let cells := menonHarmonicCaseIICells a
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  let Vexp : ℝ :=
    min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope (4 * Y)) *
      ((2 * la ^ (-300 : ℝ)) / ((D : ℝ) * 8))
  let Hmax : ℝ :=
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hcore0 : 0 < core := by dsimp only [core]; positivity
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hM0 : 0 < M := by dsimp only [M]; positivity
  have hden0 : 0 < den := by
    dsimp only [den, menonHarmonicCaseIICoreDenominatorConstant]
    positivity
  have hfactorLower : 1 / den ≤ factor := by
    simpa only [den, factor, la] using
      menonHarmonicCaseII_VexpFactor_lower ha hlog haY hYa
  have hfactor0 : 0 < factor := lt_of_lt_of_le (by positivity : 0 < 1 / den) hfactorLower
  have hcoreEq :
      (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) = core := by
    dsimp only [core, menonHarmonicCaseIICoreExponent]
    exact (Real.rpow_mul ha0.le _ _).symm
  have hVeq : Vexp = M * factor := by
    dsimp only [Vexp, M, factor, D, la]
    rw [hcoreEq]
    ring
  have hVlower : M / den ≤ Vexp := by
    rw [hVeq]
    have h := mul_le_mul_of_nonneg_left hfactorLower hM0.le
    simpa only [div_eq_mul_inv, one_mul] using h
  have hV0 : 0 < Vexp := by rw [hVeq]; positivity
  have hVsq : (M / den) ^ 2 ≤ Vexp ^ 2 :=
    pow_le_pow_left₀ (by positivity) hVlower 2
  have hnum : ((cells : ℝ) * (D : ℝ) * 12) * Hmax ≤
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := by
    simpa only [cells, D, Hmax, la] using
      menonHarmonicCaseII_countNumerator_le ha hlog haY hYa hT0.le
  have hnum0 : 0 ≤ ((cells : ℝ) * (D : ℝ) * 12) * Hmax := by
    have harg : (1 : ℝ) ≤
        menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ) := by
      rw [menonHeathBrownCaseIIComplementWidthConstant]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reducePow]
      exact_mod_cast (show 1 ≤ 32 * (4 * Y) by omega)
    have hpoly : 0 ≤ 1 + Real.log
        (menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ)) :=
      add_nonneg zero_le_one (Real.log_nonneg harg)
    have hpref : 0 ≤
        12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log
            (menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ))) ^
              (menonHeathBrownCaseIIComplementPolylogExponent + 2) := by
      exact mul_nonneg (by positivity) (pow_nonneg hpoly _)
    have hrpow : 0 ≤
        ((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y) :=
      Real.rpow_nonneg (by positivity) _
    have hHmax0 : 0 ≤ Hmax := by
      dsimp only [Hmax]
      exact mul_nonneg (mul_nonneg hpref (by linarith)) hrpow
    dsimp only [cells, D, Hmax]
    exact mul_nonneg (by positivity) hHmax0
  have hquot : ((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 ≤
      (menonHarmonicCaseIIMeasureNumeratorConstant *
        menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) *
          la ^ (1855 : ℕ) * (T + 1) / M ^ 2 := by
    have hstep1 : ((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 ≤
        ((cells : ℝ) * (D : ℝ) * 12) * Hmax / (M / den) ^ 2 :=
      div_le_div_of_nonneg_left hnum0 (by positivity) hVsq
    have hstep2 : ((cells : ℝ) * (D : ℝ) * 12) * Hmax / (M / den) ^ 2 ≤
        (menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) *
          (T + 1)) / (M / den) ^ 2 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    refine hstep1.trans (hstep2.trans (le_of_eq ?_))
    dsimp only [den]
    field_simp [hM0.ne', hla0.ne']
  have hinv : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hbracket0 : 0 ≤ 4 *
      (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1) := by
    positivity
  have hcross0 : 0 ≤ menonHarmonicCaseIIMeasureNumeratorConstant *
      menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ) := by
    rw [menonHarmonicCaseIIMeasureNumeratorConstant,
      menonHarmonicCaseIICoreDenominatorConstant,
      menonHarmonicCaseIIComplementConstant]
    positivity
  have hterm0 : 0 ≤ la ^ (1855 : ℕ) * (T + 1) / M ^ 2 := by positivity
  calc
    2 * (2 * Real.pi)⁻¹ *
        (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) ≤
      8 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1) := by
        have hcoef : 2 * (2 * Real.pi)⁻¹ ≤ 2 := by nlinarith
        nlinarith
    _ ≤ 8 * ((menonHarmonicCaseIIMeasureNumeratorConstant *
          menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) *
          la ^ (1855 : ℕ) * (T + 1) / M ^ 2 + 1) := by gcongr
    _ ≤ (8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
          menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) + 8) *
          (la ^ (1855 : ℕ) * (T + 1) / M ^ 2 + 1) := by
      let K : ℝ := menonHarmonicCaseIIMeasureNumeratorConstant *
        menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)
      let R : ℝ := la ^ (1855 : ℕ) * (T + 1) / M ^ 2
      have hK : 0 ≤ K := by simpa only [K] using hcross0
      have hR : 0 ≤ R := by simpa only [R] using hterm0
      have hsmall : K * R + 1 ≤ (K + 1) * (R + 1) := by
        nlinarith [mul_nonneg hK hR]
      have hscaled := mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ 8 by norm_num)
      calc
        8 * ((menonHarmonicCaseIIMeasureNumeratorConstant *
              menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) *
            la ^ (1855 : ℕ) * (T + 1) / M ^ 2 + 1) =
            8 * (K * R + 1) := by dsimp only [K, R]; ring
        _ ≤ 8 * ((K + 1) * (R + 1)) := hscaled
        _ = (8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
              menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)) + 8) *
            (la ^ (1855 : ℕ) * (T + 1) / M ^ 2 + 1) := by
              dsimp only [K, R]
              ring
    _ = menonHarmonicCaseIIGeneralMeasureConstant *
          (la ^ (1855 : ℕ) * (T + 1) / M ^ 2 + 1) := by
      rw [menonHarmonicCaseIIGeneralMeasureConstant]

/-- Literal threshold attached to one actual final-range block. -/
def menonFinalRangeActualCaseIIThreshold (C0 x : ℝ) (j : ℕ) : ℝ :=
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let H := menonHarmonicCaseIISmoothingWidth a
  let B := menonHarmonicCaseIIBudget C0 a Y
  (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
      primePowerDefectIoc a Y) / Real.log ((a + 1 : ℕ) : ℝ)) /
    ((a + 1 : ℕ) : ℝ)

/-- Literal two-sided Gallagher exceptional set attached to one actual final-range block. -/
def menonFinalRangeActualCaseIIExceptionalSet
    (C0 x : ℝ) (j : ℕ) (T : ℝ) : Set ℝ :=
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let B := menonHarmonicCaseIIBudget C0 a Y
  menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet
    a (4 * Y) Y H B T ((cells : ℝ) / 2)

/-- Interior physical-frequency band on which the Case-II exceptional-set theorem is literal. -/
def menonFinalRangeActualCaseIIBand (x : ℝ) (j : ℕ) (T : ℝ) : Set ℝ :=
  let cells := menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j)
  {w : ℝ | T + (cells : ℝ) / 2 ≤ 2 * Real.pi * |w| ∧
    2 * Real.pi * |w| ≤ 2 * T - (cells : ℝ) / 2}

/-- On an interior physical-frequency band, the receiver's strict block-large set is contained in
the literal two-sided Case-II exceptional set. -/
theorem menonHarmonicPrimeBlockLargeOn_subset_actualCaseIIExceptional
    {C0 x T : ℝ} {j : ℕ} (heta : 0 ≤ menonFinalRangeLadderEta x)
    {E : Set ℝ} (hE : E ⊆ menonFinalRangeActualCaseIIBand x j T) :
    menonHarmonicPrimeBlockLargeOn E
        (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
          (1 + menonFinalRangeLadderEta x) j)
        (menonFinalRangeActualCaseIIThreshold C0 x j) ⊆
      menonFinalRangeActualCaseIIExceptionalSet C0 x j T := by
  intro w hw
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let B := menonHarmonicCaseIIBudget C0 a Y
  have hband := hE hw.1
  change T + (cells : ℝ) / 2 ≤ 2 * Real.pi * |w| ∧
    2 * Real.pi * |w| ≤ 2 * T - (cells : ℝ) / 2 at hband
  have hlarge := norm_harmonicPrimeBlockPoly_gt_of_mem_largeOn hw
  rw [geomBlock_menonFinalRangePrimes_eq_actualBlock heta] at hlarge
  have hlarge' :
      (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
            primePowerDefectIoc a Y) / Real.log ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) w‖ := by
    simpa only [menonFinalRangeActualCaseIIThreshold, a, Y, H, B] using hlarge
  rcases le_total 0 w with hw0 | hw0
  · have hband' : T + (cells : ℝ) / 2 ≤ (2 * Real.pi) * w ∧
        (2 * Real.pi) * w ≤ 2 * T - (cells : ℝ) / 2 := by
      simpa only [menonFinalRangeActualCaseIIBand, a, cells, abs_of_nonneg hw0] using hband
    simpa only [menonFinalRangeActualCaseIIExceptionalSet, a, Y, cells, H, B] using
      (mem_menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet_of_pos
        hband' hlarge')
  · have habs : |w| = -w := abs_of_nonpos hw0
    have hband' : T + (cells : ℝ) / 2 ≤ -(2 * Real.pi) * w ∧
        -(2 * Real.pi) * w ≤ 2 * T - (cells : ℝ) / 2 := by
      rw [habs] at hband
      convert hband using 1 <;> ring
    simpa only [menonFinalRangeActualCaseIIExceptionalSet, a, Y, cells, H, B] using
      (mem_menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet_of_neg
        hband' hlarge')

set_option maxHeartbeats 800000 in
/-- Every literal final-range block satisfies the two-regime Case-II volume envelope. -/
theorem exists_absolute_eventually_volume_menonFinalRangeActualCaseIIExceptionalSet_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x), ∀ {T : ℝ},
        1 ≤ T →
        (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        volume.real (menonFinalRangeActualCaseIIExceptionalSet C0 x j T) ≤
          menonHarmonicCaseIIGeneralMeasureConstant *
            ((Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (1855 : ℕ) * (T + 1) /
                (min T ((menonFinalRangeBlockLowerNat x j : ℝ) ^
                  menonHarmonicCaseIICoreExponent)) ^ 2 + 1) := by
  obtain ⟨C0, hC0, hvolume⟩ :=
    exists_absolute_eventually_volume_real_menonFinalRangeActualBlock_caseII_scheduled_le
  have hcut := tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop 256
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hvolume, eventually_menonFinalRangeActualBlock_caseII_endpoints,
    eventually_menonFinalRangeLadder_basic, hcut] with x hvol hend hbasic hcutx
  intro j hj T hT hcellsT h2T
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  have hbaseLe : menonFinalRangePrimeCutoffNat x ≤ a := by
    rcases hbasic with ⟨_hx, _hH, _hQ, _htop, heta, _hL⟩
    dsimp only [a]
    rw [menonFinalRangeBlockLowerNat, ← Nat.floor_natCast (R := ℝ)
      (menonFinalRangePrimeCutoffNat x)]
    apply Nat.floor_mono
    rw [menonFinalRangeLadderBase]
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hstep)
  have ha256 : 256 ≤ a := hcutx.trans hbaseLe
  have hends := hend j hj
  rcases hends with ⟨_ha64, haY, hYa⟩
  have hlog : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have h := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
    simpa using h
  have hraw := hvol j hj hT hcellsT h2T
  have hscalar := menonHarmonicCaseII_generalMeasureEnvelope_le
    ha256 hlog (by simpa only [a, Y] using haY) (by simpa only [a, Y] using hYa) hT
  exact hraw.trans (by
    simpa only [menonFinalRangeActualCaseIIExceptionalSet, a, Y] using hscalar)

set_option maxHeartbeats 800000 in
/-- Receiver-ready form: every strict large-value subset of an interior Case-II band inherits the
same two-regime volume envelope. -/
theorem exists_absolute_eventually_volume_menonHarmonicPrimeBlockLargeOn_caseII_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x), ∀ {T : ℝ},
        1 ≤ T →
        (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        ∀ {E : Set ℝ}, E ⊆ menonFinalRangeActualCaseIIBand x j T →
        volume.real
            (menonHarmonicPrimeBlockLargeOn E
              (geomBlock (menonFinalRangePrimes x) (menonFinalRangeLadderBase x)
                (1 + menonFinalRangeLadderEta x) j)
              (menonFinalRangeActualCaseIIThreshold C0 x j)) ≤
          menonHarmonicCaseIIGeneralMeasureConstant *
            ((Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (1855 : ℕ) * (T + 1) /
                (min T ((menonFinalRangeBlockLowerNat x j : ℝ) ^
                  menonHarmonicCaseIICoreExponent)) ^ 2 + 1) := by
  obtain ⟨C0, hC0, hvolume⟩ :=
    exists_absolute_eventually_volume_menonFinalRangeActualCaseIIExceptionalSet_le
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hvolume, eventually_menonFinalRangeLadder_basic] with x hvol hbasic
  intro j hj T hT hcellsT h2T E hE
  have hsub := menonHarmonicPrimeBlockLargeOn_subset_actualCaseIIExceptional
    (C0 := C0) (x := x) (T := T) (j := j) hbasic.2.2.2.2.1 hE
  have hexcSub : menonFinalRangeActualCaseIIExceptionalSet C0 x j T ⊆
      Set.Icc (-T) T := by
    intro w hw
    let a := menonFinalRangeBlockLowerNat x j
    let cells := menonHarmonicCaseIICells a
    have hcells0 : (0 : ℝ) ≤ (cells : ℝ) := by positivity
    rw [menonFinalRangeActualCaseIIExceptionalSet,
      menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet] at hw
    rcases hw with hw | hw
    · have hband := hw.1
      have hw0 : w ≤ 0 := by
        have hcoef : -(2 * Real.pi) < 0 := neg_neg_of_pos (by positivity)
        have hpositive : 0 < -(2 * Real.pi) * w := by
          dsimp only [a, cells] at hband
          have : 0 < T + (menonHarmonicCaseIICells
              (menonFinalRangeBlockLowerNat x j) : ℝ) / 2 := by
            have hcast : (0 : ℝ) ≤ (menonHarmonicCaseIICells
                (menonFinalRangeBlockLowerNat x j) : ℝ) := by positivity
            nlinarith
          exact this.trans_le hband.1
        by_contra hwnot
        have hwpos : 0 < w := lt_of_not_ge hwnot
        have hnegative : -(2 * Real.pi) * w < 0 :=
          mul_neg_of_neg_of_pos hcoef hwpos
        exact (not_lt_of_ge hpositive.le) hnegative
      have hscale : -2 * w ≤ -(2 * Real.pi) * w := by
        have hpi1 : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
        have hmul := mul_le_mul_of_nonneg_right hpi1 (neg_nonneg.mpr hw0)
        nlinarith
      have hupper : -(2 * Real.pi) * w ≤ 2 * T := by
        dsimp only [a, cells] at hband
        have hbandUpper := hband.2
        have hcast : (0 : ℝ) ≤ (menonHarmonicCaseIICells
            (menonFinalRangeBlockLowerNat x j) : ℝ) := by positivity
        linarith
      exact ⟨by nlinarith, by linarith⟩
    · have hband := hw.1
      have hw0 : 0 ≤ w := by
        have hcoef : 0 < 2 * Real.pi := by positivity
        have hpositive : 0 < (2 * Real.pi) * w := by
          dsimp only [a, cells] at hband
          have : 0 < T + (menonHarmonicCaseIICells
              (menonFinalRangeBlockLowerNat x j) : ℝ) / 2 := by
            have hcast : (0 : ℝ) ≤ (menonHarmonicCaseIICells
                (menonFinalRangeBlockLowerNat x j) : ℝ) := by positivity
            nlinarith
          exact this.trans_le hband.1
        by_contra hwnot
        have hwneg : w < 0 := lt_of_not_ge hwnot
        have hnegative : (2 * Real.pi) * w < 0 :=
          mul_neg_of_pos_of_neg hcoef hwneg
        exact (not_lt_of_ge hpositive.le) hnegative
      have hscale : 2 * w ≤ (2 * Real.pi) * w := by
        have hpi1 : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
        have hmul := mul_le_mul_of_nonneg_right hpi1 hw0
        nlinarith
      have hupper : (2 * Real.pi) * w ≤ 2 * T := by
        dsimp only [a, cells] at hband
        have hbandUpper := hband.2
        have hcast : (0 : ℝ) ≤ (menonHarmonicCaseIICells
            (menonFinalRangeBlockLowerNat x j) : ℝ) := by positivity
        linarith
      exact ⟨by linarith, by nlinarith⟩
  have hfiniteIcc : volume (Set.Icc (-T) T) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hfinite : volume (menonFinalRangeActualCaseIIExceptionalSet C0 x j T) ≠ ⊤ := by
    intro htop
    have hmono : volume (menonFinalRangeActualCaseIIExceptionalSet C0 x j T) ≤
        volume (Set.Icc (-T) T) := measure_mono hexcSub
    rw [htop] at hmono
    exact hfiniteIcc (top_le_iff.mp hmono)
  exact (MeasureTheory.measureReal_mono hsub hfinite).trans (hvol j hj hT hcellsT h2T)

end

end RHTower.Sieve
