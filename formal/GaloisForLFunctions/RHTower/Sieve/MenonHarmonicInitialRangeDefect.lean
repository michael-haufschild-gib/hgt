import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicInitialRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicLadderErrorSharp

/-!
# Exact initial-range ladder defect at Menon's receiver height

The generic harmonic ladder estimate becomes too coarse if the initial prime endpoint is replaced
by the ambient source scale.  Here its literal endpoint `hN` is retained.  This exposes the
subpower ratio `hN / x` needed by Menon's growing-window schedule and bounds every other factor by
the exact initial-range parameters.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Explicit uniform bound for the initial Ramaré ladder's single global support defect. -/
theorem eventually_integral_Icc_normSq_menonInitialRange_ladderDefect_le_explicit
    {a c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W : ℝ),
      ((highBase a x : ℕ) : ℝ) < (hN : ℝ) →
      (hN : ℝ) ≤ x → 1 ≤ W → W * ((hN : ℝ) + 1) ≤ 2 * x →
      (∫ w in Set.Icc (-W) W,
        ‖harmonicLadderProductDefect (menonInitialRangePrimes a c x hN) ⌈x⌉₊
          (menonFinalRangeTopNat x) ((highBase a x : ℕ) : ℝ) (lowEta c x)
          (menonInitialRangeSteps a c x hN) w‖ ^ 2) ≤
        (4 / x ^ 2) * ((5 * Real.pi + 15 * Real.exp 1) * x) *
          (Real.log (6 * x) / (Real.log x) ^ a) *
          ((2 * Real.log (hN : ℝ) * (Real.log x) ^ c) *
            (5 * x * lowEta c x ^ 2 + 10 * lowEta c x * (hN : ℝ) +
              8 * x * lowEta c x / ((highBase a x : ℕ) : ℝ) + 5 +
              3 * x / ((highBase a x : ℕ) : ℝ) ^ 2)) := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxexp
  intro hN W hQh hhx hW hWh
  let P := menonInitialRangePrimes a c x hN
  let Q : ℝ := ((highBase a x : ℕ) : ℝ)
  let eta := lowEta c x
  let L := menonInitialRangeSteps a c x hN
  let A0 := ⌈x⌉₊
  let B0 := menonFinalRangeTopNat x
  have hx1 : 1 < x := by
    have he : (1 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
    exact he.trans_le hxexp
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxexp
    simpa using h
  have hQ : 1 < Q := by
    have hcard : 1 < cardLength a x := by
      rw [cardLength]
      simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr (Real.rpow_pos_of_pos hlogx a))
    have hbase := (highBase_bounds (a := a) hx1).1
    dsimp only [Q]
    linarith
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have heta0 : 0 ≤ eta := (lowEta_pos (c := c) hx1).le
  have heta1 : eta ≤ 1 := by
    dsimp only [eta, lowEta]
    have hpow := Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith : -c ≤ 0)
    simpa using hpow
  have hhN1 : 1 ≤ hN := by
    have : (1 : ℝ) < (hN : ℝ) := hQ.trans hQh
    exact_mod_cast this.le
  have hhN0 : (0 : ℝ) < (hN : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hhN1)
  have hQnat : highBase a x ≤ hN := by exact_mod_cast hQh.le
  have hA0 : 0 < A0 := by
    dsimp only [A0]
    exact Nat.one_le_ceil_iff.mpr hx0
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact (mem_primesRange.mp (by simpa only [P, menonInitialRangePrimes] using hp)).1
  have hPge : ∀ p ∈ P, Q ≤ (p : ℝ) := by
    intro p hp
    have hr :=
      (mem_primesRange.mp (by simpa only [P, menonInitialRangePrimes] using hp)).2.1
    dsimp only [Q]
    exact_mod_cast hr.le
  have hrawTop : Q * (1 + eta) ^ L ≤ 2 * (hN : ℝ) := by
    have hfloor : Q * (1 + eta) ^ L <
        (menonInitialRangeTop a c x hN : ℝ) + 1 := by
      simpa only [Q, eta, L, menonInitialRangeTop] using
        (Nat.lt_floor_add_one (Q * (1 + eta) ^ L))
    have htopNat := menonInitialRangeTop_le (a := a) (c := c) hx1 hQh
    have htop : (menonInitialRangeTop a c x hN : ℝ) ≤ (hN : ℝ) := by
      exact_mod_cast htopNat
    nlinarith [show (1 : ℝ) ≤ (hN : ℝ) by exact_mod_cast hhN1]
  have hclosed := integral_Icc_normSq_harmonicLadderProductDefect_le_closed
    (P := P) (A₀ := A0) (B₀ := B0) (L := L) hA0 hQ heta0 hW hPprime hPge
  have hsharp := menonHarmonicLadderErrorBudget_le_top
    (A₀ := A0) (B₀ := B0) hQ heta0 (by linarith : 0 ≤ W) hrawTop
  have hbase := hclosed.trans hsharp
  have hAceilLower : x ≤ (A0 : ℝ) := by
    dsimp only [A0]
    exact Nat.le_ceil x
  have hAceilUpper : (A0 : ℝ) ≤ 2 * x := by
    have hceil := Nat.ceil_lt_add_one hx0.le
    dsimp only [A0]
    nlinarith
  have hBupper : (B0 : ℝ) ≤ 3 * x := by
    dsimp only [B0, menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hB1 : 1 ≤ B0 := by
    dsimp only [B0, menonFinalRangeTopNat]
    exact Nat.floor_pos.mpr (by nlinarith)
  let N0 : ℕ := ⌊(B0 : ℝ) * (1 + eta)⌋₊
  have hN0one : 1 ≤ N0 := by
    dsimp only [N0]
    refine Nat.floor_pos.mpr ?_
    have hB0one : (1 : ℝ) ≤ (B0 : ℝ) := by exact_mod_cast hB1
    nlinarith [mul_le_mul hB0one (show (1 : ℝ) ≤ 1 + eta by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg B0)]
  have hN0upper : (N0 : ℝ) ≤ 6 * x := by
    have hfloor : (N0 : ℝ) ≤ (B0 : ℝ) * (1 + eta) := by
      dsimp only [N0]
      exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg B0) (by linarith))
    have htwo : 1 + eta ≤ 2 := by linarith
    have hfac : (B0 : ℝ) * (1 + eta) ≤ (3 * x) * 2 := by gcongr
    linarith
  have hWupper : W ≤ 2 * x := by
    have hfac : W ≤ W * ((hN : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ W by linarith,
        show (1 : ℝ) ≤ (hN : ℝ) by exact_mod_cast hhN1]
    exact hfac.trans hWh
  have hscale : ((1 + eta) / (A0 : ℝ)) ^ 2 ≤ 4 / x ^ 2 := by
    have hfrac : (1 + eta) / (A0 : ℝ) ≤ 2 / x := by
      exact div_le_div₀ (by linarith) (by linarith) hx0 hAceilLower
    have hleft0 : 0 ≤ (1 + eta) / (A0 : ℝ) := by positivity
    have hsq := pow_le_pow_left₀ hleft0 hfrac 2
    calc
      ((1 + eta) / (A0 : ℝ)) ^ 2 ≤ (2 / x) ^ 2 := hsq
      _ = 4 / x ^ 2 := by ring
  have hmean : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N0 : ℝ) ≤
      (5 * Real.pi + 15 * Real.exp 1) * x := by
    calc
      5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N0 : ℝ) ≤
          5 * Real.pi / 2 * (2 * x) + 5 * Real.exp 1 / 2 * (6 * x) := by gcongr
      _ = (5 * Real.pi + 15 * Real.exp 1) * x := by ring
  have hlogQlower : (Real.log x) ^ a ≤ Real.log Q := by
    have hbaseQ := (highBase_bounds (a := a) hx1).1
    have hlog := Real.log_le_log (cardLength_pos a x) hbaseQ
    simpa only [Q, log_cardLength] using hlog
  have hlogNupper : Real.log (N0 : ℝ) ≤ Real.log (6 * x) := by
    exact Real.log_le_log
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN0one)) hN0upper
  have hlogratio : Real.log (N0 : ℝ) / Real.log Q ≤
      Real.log (6 * x) / (Real.log x) ^ a := by
    have h6x : (1 : ℝ) ≤ 6 * x := by nlinarith only [hx1]
    have hlog6 : 0 ≤ Real.log (6 * x) := Real.log_nonneg h6x
    have hrpow : 0 < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    rw [div_le_div_iff₀ (Real.log_pos hQ) hrpow]
    calc
      Real.log (N0 : ℝ) * (Real.log x) ^ a ≤
          Real.log (6 * x) * (Real.log x) ^ a :=
        mul_le_mul_of_nonneg_right hlogNupper hrpow.le
      _ ≤ Real.log (6 * x) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlogQlower hlog6
  have hLbound : (L : ℝ) ≤ 2 * Real.log (hN : ℝ) * (Real.log x) ^ c := by
    simpa only [L] using menonInitialRangeSteps_le hxexp hc hQnat
  have hgap :
      ((A0 : ℝ) + (B0 : ℝ)) * eta ^ 2 + 5 * eta * (2 * (hN : ℝ)) +
          (((A0 : ℝ) + 2 * (B0 : ℝ)) * eta) / Q + 5 + (B0 : ℝ) / Q ^ 2 ≤
        5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
          8 * x * eta / Q + 5 + 3 * x / Q ^ 2 := by
    have hAB : (A0 : ℝ) + (B0 : ℝ) ≤ 5 * x := by
      linarith only [hAceilUpper, hBupper]
    have hA2B : (A0 : ℝ) + 2 * (B0 : ℝ) ≤ 8 * x := by
      linarith only [hAceilUpper, hBupper]
    have ht1 := mul_le_mul_of_nonneg_right hAB (sq_nonneg eta)
    have ht3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hA2B heta0) hQpos.le
    have ht5 := div_le_div_of_nonneg_right hBupper (sq_nonneg Q)
    linarith only [ht1, ht3, ht5]
  dsimp only [N0] at hmean hlogratio
  have hmajor :
      ((1 + eta) / (A0 : ℝ)) ^ 2 *
          (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 *
            ((⌊(B0 : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ)) *
          (Real.log ((⌊(B0 : ℝ) * (1 + eta)⌋₊ : ℕ) : ℝ) / Real.log Q) *
          ((L : ℝ) * (((A0 : ℝ) + (B0 : ℝ)) * eta ^ 2 +
            5 * eta * (2 * (hN : ℝ)) + (((A0 : ℝ) + 2 * (B0 : ℝ)) * eta) / Q +
            5 + (B0 : ℝ) / Q ^ 2)) ≤
        (4 / x ^ 2) * ((5 * Real.pi + 15 * Real.exp 1) * x) *
          (Real.log (6 * x) / (Real.log x) ^ a) *
          ((2 * Real.log (hN : ℝ) * (Real.log x) ^ c) *
            (5 * x * eta ^ 2 + 10 * eta * (hN : ℝ) +
              8 * x * eta / Q + 5 + 3 * x / Q ^ 2)) := by
    have h6x : (1 : ℝ) ≤ 6 * x := by nlinarith only [hx1]
    have hlog6 : 0 ≤ Real.log (6 * x) := Real.log_nonneg h6x
    have hlogh : 0 ≤ Real.log (hN : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hhN1)
    gcongr
  exact hbase.trans (by simpa only [P, Q, eta, L, A0, B0] using hmajor)

end

end RHTower.Sieve
