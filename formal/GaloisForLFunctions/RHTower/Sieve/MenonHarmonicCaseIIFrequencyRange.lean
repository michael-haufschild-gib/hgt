import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIICountNumerator
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIThresholdBound
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimeBlockSymmetry

/-!
# Menon harmonic prime blocks: the Case-II frequency range

This module turns the Case-II block estimate for Menon's harmonic prime polynomial
`harmonicPrimeBlockPoly B w = ∑_{p ∈ B} μ(p) p^(-1) exp(2πi w log p)` into a bound that holds on an
explicit frequency interval. For a block with lower endpoint `a` it defines the frequency floor
`6 (K + 1) (log a)^1856 + 3 · cells(a)` and ceiling `(3/4) a^((1/8) δ)`, where
`δ = maynardDerivativeDeficit 26 = 1/(3·2^26)` and `K = menonHarmonicCaseIICrossConstant`. For `u`
between floor and ceiling, the choice `T = 2u/3` satisfies every scalar side condition of the
Case-II threshold theorem, so the block polynomial is `O((log a)^(-20))` throughout the range.

## Main results

- `menonHarmonicCaseII_scalar_geometry`: if `1 ≤ a`, `1 ≤ log a` and `u` lies between the Case-II
  floor and ceiling, then `T = 2u/3` satisfies `1 ≤ T`, `cells/4 ≤ T`, `T + cells/2 ≤ u ≤ 2T - cells/2`,
  `2T ≤ a^3` and `K (log a)^1855 (T + 1) < min(T, a^(δ/8))^2`.
- `exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_caseII_range`: there is
  an absolute `C0 ≥ 0` such that for all large `x`, every final-range block `(a_j, Y_j]` and every
  real `w` with `2π|w|` in the Case-II range of `a_j`, the harmonic prime polynomial of the primes in
  `(a_j, Y_j]` at frequency `w` has norm at most `menonHarmonicCaseIIThresholdConstant C0 / (log a_j)^20`.

## Hypotheses

The main results are unconditional. The scalar-geometry lemma assumes `1 ≤ a`, `1 ≤ log a` and the
frequency range `floor(a) ≤ u ≤ ceiling(a)`; the block bound only restricts `2π|w|` to that range.
-/

namespace RHTower.Sieve

open Filter Finset

noncomputable section

/-- The cross constant `K` of the Case-II budget: the measure numerator constant times the square of
the core denominator constant. -/
def menonHarmonicCaseIICrossConstant : ℝ :=
  menonHarmonicCaseIIMeasureNumeratorConstant *
    menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ)

/-- Lower end of the Case-II frequency range for a block with lower endpoint `a`:
`6 (K + 1) (log a)^1856 + 3 · menonHarmonicCaseIICells a`. -/
def menonHarmonicCaseIIFrequencyFloor (a : ℕ) : ℝ :=
  6 * (menonHarmonicCaseIICrossConstant + 1) *
      (Real.log (a : ℝ)) ^ (1856 : ℕ) +
    3 * (menonHarmonicCaseIICells a : ℝ)

/-- Upper end of the Case-II frequency range: `(3/4) a^e` with `e = menonHarmonicCaseIICoreExponent`. -/
def menonHarmonicCaseIIFrequencyCeiling (a : ℕ) : ℝ :=
  (3 / 4 : ℝ) * (a : ℝ) ^ menonHarmonicCaseIICoreExponent

theorem menonHarmonicCaseIICrossConstant_nonneg :
    0 ≤ menonHarmonicCaseIICrossConstant := by
  rw [menonHarmonicCaseIICrossConstant,
    menonHarmonicCaseIIMeasureNumeratorConstant,
    menonHarmonicCaseIICoreDenominatorConstant,
    menonHarmonicCaseIIComplementConstant]
  positivity

theorem menonHarmonicCaseIICoreExponent_pos :
    0 < menonHarmonicCaseIICoreExponent := by
  rw [menonHarmonicCaseIICoreExponent, maynardDerivativeDeficit]
  positivity

private theorem caseII_core_power_eq (a : ℕ) :
    (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) =
      (a : ℝ) ^ menonHarmonicCaseIICoreExponent := by
  by_cases ha : a = 0
  · subst a
    simp [menonHarmonicCaseIICoreExponent, maynardDerivativeDeficit]
  · rw [menonHarmonicCaseIICoreExponent, Real.rpow_mul (by positivity)]

/-- For `1 ≤ a`, `1 ≤ log a` and `u` in the Case-II frequency range, `T = 2u/3` meets all scalar
side conditions of the Case-II threshold theorem, including the strict cross inequality
`K (log a)^1855 (T + 1) < min(T, a^(δ/8))^2`. -/
theorem menonHarmonicCaseII_scalar_geometry
    {a : ℕ} (ha : 1 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ)) {u : ℝ}
    (hfloor : menonHarmonicCaseIIFrequencyFloor a ≤ u)
    (hceiling : u ≤ menonHarmonicCaseIIFrequencyCeiling a) :
    let T := 2 * u / 3
    1 ≤ T ∧
      (menonHarmonicCaseIICells a : ℝ) / 4 ≤ T ∧
      T + (menonHarmonicCaseIICells a : ℝ) / 2 ≤ u ∧
      u ≤ 2 * T - (menonHarmonicCaseIICells a : ℝ) / 2 ∧
      2 * T ≤ (a : ℝ) ^ (3 : ℕ) ∧
      menonHarmonicCaseIICrossConstant *
          (Real.log (a : ℝ)) ^ (1855 : ℕ) * (T + 1) <
        (min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26)) ^ 2 := by
  dsimp only
  let K := menonHarmonicCaseIICrossConstant
  let la := Real.log (a : ℝ)
  let cells : ℝ := menonHarmonicCaseIICells a
  let T : ℝ := 2 * u / 3
  have hK0 : 0 ≤ K := by simpa only [K] using menonHarmonicCaseIICrossConstant_nonneg
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hL0 : 0 ≤ la ^ (1855 : ℕ) := by positivity
  have hL1 : 1 ≤ la ^ (1855 : ℕ) := one_le_pow₀ (by simpa only [la] using hlog)
  have hLmono : la ^ (1855 : ℕ) ≤ la ^ (1856 : ℕ) := by
    calc
      la ^ (1855 : ℕ) = la ^ (1855 : ℕ) * 1 := by ring
      _ ≤ la ^ (1855 : ℕ) * la :=
        mul_le_mul_of_nonneg_left (by simpa only [la] using hlog) hL0
      _ = la ^ (1856 : ℕ) := by
        rw [show (1856 : ℕ) = 1855 + 1 by omega]
        exact (pow_succ la 1855).symm
  have hcells0 : 0 ≤ cells := by dsimp only [cells]; positivity
  have hmain : 6 * (K + 1) * la ^ (1856 : ℕ) ≤ u := by
    dsimp only [menonHarmonicCaseIIFrequencyFloor] at hfloor
    simpa only [K, la, cells] using (show
      6 * (K + 1) * la ^ (1856 : ℕ) ≤ u by nlinarith)
  have hu6 : 6 ≤ u := by
    have hK1 : 1 ≤ K + 1 := by linarith
    have hL1856 : 1 ≤ la ^ (1856 : ℕ) := one_le_pow₀ (by simpa only [la] using hlog)
    nlinarith [mul_le_mul hK1 hL1856 (by norm_num : 0 ≤ (1 : ℝ)) (by linarith : 0 ≤ K + 1)]
  have hcell : 3 * cells ≤ u := by
    dsimp only [menonHarmonicCaseIIFrequencyFloor] at hfloor
    have : 0 ≤ 6 * (K + 1) * la ^ (1856 : ℕ) := by positivity
    simpa only [K, la, cells] using (show 3 * cells ≤ u by linarith)
  have hT4 : 4 ≤ T := by dsimp only [T]; linarith
  have hT0 : 0 < T := by linarith
  have hcellT : cells / 4 ≤ T := by dsimp only [T]; nlinarith
  have hbandLo : T + cells / 2 ≤ u := by dsimp only [T]; nlinarith
  have hbandHi : u ≤ 2 * T - cells / 2 := by dsimp only [T]; nlinarith
  have hcoreEq := caseII_core_power_eq a
  have hpow0 : 0 ≤ (a : ℝ) ^ menonHarmonicCaseIICoreExponent := by positivity
  have hTcore : T ≤ (a : ℝ) ^ menonHarmonicCaseIICoreExponent := by
    dsimp only [menonHarmonicCaseIIFrequencyCeiling] at hceiling
    dsimp only [T]
    nlinarith
  have hcore3 : (a : ℝ) ^ menonHarmonicCaseIICoreExponent ≤ (a : ℝ) ^ (3 : ℕ) := by
    rw [show (a : ℝ) ^ (3 : ℕ) = (a : ℝ) ^ (3 : ℝ) by
      simpa only [Nat.cast_ofNat] using (Real.rpow_natCast (a : ℝ) 3).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast ha)
      (by
        rw [menonHarmonicCaseIICoreExponent, maynardDerivativeDeficit]
        norm_num)
  have h2T : 2 * T ≤ (a : ℝ) ^ (3 : ℕ) := by
    dsimp only [menonHarmonicCaseIIFrequencyCeiling] at hceiling
    have : 2 * T ≤ (a : ℝ) ^ menonHarmonicCaseIICoreExponent := by
      dsimp only [T]
      nlinarith
    exact this.trans hcore3
  have htwoKL : 2 * K * la ^ (1855 : ℕ) < T := by
    have hTlower : 4 * (K + 1) * la ^ (1856 : ℕ) ≤ T := by
      dsimp only [T]
      nlinarith
    have hstrict : 2 * K * la ^ (1855 : ℕ) <
        4 * (K + 1) * la ^ (1856 : ℕ) := by
      nlinarith [hLmono, hL1]
    exact hstrict.trans_le hTlower
  have hTplus : T + 1 ≤ 2 * T := by linarith
  have hcross : K * la ^ (1855 : ℕ) * (T + 1) < T ^ 2 := by
    calc
      K * la ^ (1855 : ℕ) * (T + 1) ≤
          K * la ^ (1855 : ℕ) * (2 * T) := by
            exact mul_le_mul_of_nonneg_left hTplus (mul_nonneg hK0 hL0)
      _ = (2 * K * la ^ (1855 : ℕ)) * T := by ring
      _ < T * T := mul_lt_mul_of_pos_right htwoKL hT0
      _ = T ^ 2 := by ring
  have hmin : min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) = T := by
    rw [hcoreEq]
    exact min_eq_left hTcore
  refine ⟨by linarith, hcellT, hbandLo, hbandHi, h2T, ?_⟩
  rw [hmin]
  simpa only [K, la, T] using hcross

private theorem norm_harmonicPrimeBlockPoly_eq_neg_abs (B : Finset ℕ) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B w‖ = ‖harmonicPrimeBlockPoly B (-|w|)‖ := by
  rcases le_total w 0 with hw | hw
  · simp only [abs_of_nonpos hw, neg_neg]
  · rw [abs_of_nonneg hw]
    exact (norm_harmonicPrimeBlockPoly_neg B w).symm

set_option maxHeartbeats 800000 in
/-- Unconditional Case-II bound: for an absolute `C0 ≥ 0`, eventually in `x`, every final-range
harmonic prime block has norm at most `menonHarmonicCaseIIThresholdConstant C0 / (log a_j)^20` at
every frequency `w` with `2π|w|` between the Case-II floor and ceiling of `a_j`. -/
theorem exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_logPow_of_caseII_range :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ w : ℝ,
        menonHarmonicCaseIIFrequencyFloor (menonFinalRangeBlockLowerNat x j) ≤
            2 * Real.pi * |w| →
        2 * Real.pi * |w| ≤
            menonHarmonicCaseIIFrequencyCeiling (menonFinalRangeBlockLowerNat x j) →
        ‖harmonicPrimeBlockPoly
            (primesRange (menonFinalRangeBlockLowerNat x j)
              (menonFinalRangeActualBlockUpperNat x j)) w‖ ≤
          menonHarmonicCaseIIThresholdConstant C0 /
            (Real.log (menonFinalRangeBlockLowerNat x j : ℝ)) ^ (20 : ℕ) := by
  obtain ⟨C0, hC0, hcaseII⟩ :=
    exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_threshold_of_caseII
  have hthreshold := eventually_menonHarmonicCaseII_threshold_le C0 hC0
  rw [eventually_atTop] at hthreshold
  obtain ⟨N, hthreshold⟩ := hthreshold
  have hcut := tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop N
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hcaseII, eventually_menonFinalRangeLadder_basic, hcut,
    eventually_menonFinalRangeActualBlock_caseII_endpoints] with x hcase hbasic hcut hendpoints
  intro j hj w hfloor hceiling
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let u : ℝ := 2 * Real.pi * |w|
  have hcutA : menonFinalRangePrimeCutoffNat x ≤ a := by
    rcases hbasic with ⟨_hx, _hH, hbase, _htop, heta, _hL⟩
    dsimp only [a]
    rw [menonFinalRangeBlockLowerNat, ← Nat.floor_natCast (R := ℝ)
      (menonFinalRangePrimeCutoffNat x)]
    apply Nat.floor_mono
    rw [menonFinalRangeLadderBase]
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
    have hpow : 1 ≤ (1 + menonFinalRangeLadderEta x) ^ j := one_le_pow₀ hstep
    have hbase0 : 0 ≤ (menonFinalRangePrimeCutoffNat x : ℝ) := by positivity
    exact le_mul_of_one_le_right hbase0 hpow
  have hNa : N ≤ a := hcut.trans hcutA
  have hend := hendpoints j hj
  rcases hend with ⟨ha64, haY, hYa⟩
  have ha1 : 1 ≤ a := by omega
  have hlog : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact (by
      have hlog' := Real.log_le_log (Real.exp_pos 1) (hexpThree.le.trans haThree)
      simpa using hlog')
  have hgeometry := menonHarmonicCaseII_scalar_geometry ha1 hlog
    (u := u) (by simpa only [a, u] using hfloor) (by simpa only [a, u] using hceiling)
  rcases hgeometry with ⟨hT, hcellsT, hbandLo, hbandHi, h2T, hcross⟩
  let T : ℝ := 2 * u / 3
  have hblock := hcase j hj (T := T) (u := u)
    (by simpa only [T] using hT)
    (by simpa only [a, T] using hcellsT)
    (by simpa only [a, T] using hbandLo)
    (by simpa only [a, T] using hbandHi)
    (by simpa only [a, T] using h2T)
    (by simpa only [a, T, menonHarmonicCaseIICrossConstant] using hcross)
  have hthresholdA := hthreshold a hNa (Y := Y) haY hYa
  have hsmall := hblock.trans hthresholdA
  have hfreq : -u / (2 * Real.pi) = -|w| := by
    dsimp only [u]
    field_simp
  rw [hfreq] at hsmall
  rw [norm_harmonicPrimeBlockPoly_eq_neg_abs]
  simpa only [a, Y] using hsmall

end

end RHTower.Sieve
