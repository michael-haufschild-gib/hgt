import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability
import GaloisForLFunctions.RHTower.Sieve.MaynardMontgomeryFixedPolylogEnergy
import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightCountExponents

/-!
# Fixed-cost absorption in the middle Route-T strip

Unlike the moving endpoint, the middle strip has the fixed positive deficit
`maynardLongGlobalAmplitudeDeficit`.  Consequently every degree-60/order-90 coefficient,
coloring, harmonic, and window-count logarithm is absorbed by any prescribed positive fraction of
that deficit.  This module records the uniform statement with the actual order-90 exponent bound.
-/

noncomputable section
namespace RHTower.Sieve

open Filter Topology

/-- Every fixed order-90 Maynard polylogarithm, together with `q` additional logarithms, is
eventually absorbed by `1/m` of the fixed middle-strip amplitude deficit. -/
theorem eventually_maynardMiddleFixedLogCost_absorbed
    (C : ℝ) (hC : 0 < C) (q m : ℕ) (hm : 0 < m) :
    ∀ᶠ T : ℝ in atTop,
      ∀ N e : ℕ, 1 ≤ N → (N : ℝ) ≤ T ^ (90 : ℕ) →
      e ≤ maynardMontgomeryFixedPolylogExponentBound →
      C * (Real.log T) ^ q *
          (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
        T ^ (maynardLongGlobalAmplitudeDeficit / m) := by
  let E : ℕ := maynardMontgomeryFixedPolylogExponentBound
  let B0 : ℝ := 91 + |Real.log maynardMontgomeryRaisedWidthConstant|
  let C0 : ℝ := C * B0 ^ E
  let eps : ℝ := maynardLongGlobalAmplitudeDeficit / (2 * (m : ℝ))
  have hd : 0 < maynardLongGlobalAmplitudeDeficit := maynardLongGlobalAmplitudeDeficit_pos
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hB0 : 1 ≤ B0 := by
    dsimp only [B0]
    linarith [abs_nonneg (Real.log maynardMontgomeryRaisedWidthConstant)]
  have hC0 : 0 < C0 := by
    dsimp only [C0]
    exact mul_pos hC (pow_pos (lt_of_lt_of_le zero_lt_one hB0) E)
  have hconst : ∀ᶠ T : ℝ in atTop, C0 ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop C0
  filter_upwards [RHTower.burnolEventually_log_pow_le_rpow heps (q + E),
    hconst, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with T hlogPow hconstT hlogT hT
  intro N e hN hNscale he
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog0 : 0 ≤ Real.log T := le_trans (by norm_num) hlogT
  have hNRpos : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hwidthPos : 0 < maynardMontgomeryRaisedWidthConstant :=
    lt_of_lt_of_le zero_lt_one maynardMontgomeryRaisedWidthConstant_one_le
  have hlogN : Real.log (N : ℝ) ≤ 90 * Real.log T := by
    have hlog := Real.log_le_log hNRpos hNscale
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    exact hlog
  have hprod : 1 ≤ maynardMontgomeryRaisedWidthConstant * (N : ℝ) :=
    one_le_mul_of_one_le_of_one_le maynardMontgomeryRaisedWidthConstant_one_le
      (by exact_mod_cast hN)
  have hbase1 : 1 ≤
      1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ)) := by
    linarith [Real.log_nonneg hprod]
  have hbase :
      1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ)) ≤
        B0 * Real.log T := by
    have hlogMul :
        Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ)) =
          Real.log maynardMontgomeryRaisedWidthConstant + Real.log (N : ℝ) := by
      rw [Real.log_mul hwidthPos.ne' hNRpos.ne']
    have hwidthLog : Real.log maynardMontgomeryRaisedWidthConstant ≤
        |Real.log maynardMontgomeryRaisedWidthConstant| * Real.log T := by
      calc
        Real.log maynardMontgomeryRaisedWidthConstant ≤
            |Real.log maynardMontgomeryRaisedWidthConstant| := le_abs_self _
        _ ≤ |Real.log maynardMontgomeryRaisedWidthConstant| * Real.log T := by
          nlinarith [abs_nonneg (Real.log maynardMontgomeryRaisedWidthConstant)]
    rw [hlogMul]
    dsimp only [B0]
    nlinarith
  have hBLog1 : 1 ≤ B0 * Real.log T :=
    one_le_mul_of_one_le_of_one_le hB0 hlogT
  have hpowBase :
      (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
        (B0 * Real.log T) ^ E := by
    calc
      (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
          (B0 * Real.log T) ^ e :=
        pow_le_pow_left₀ (zero_le_one.trans hbase1) hbase e
      _ ≤ (B0 * Real.log T) ^ E := pow_le_pow_right₀ hBLog1 he
  have hpoly :
      C * (Real.log T) ^ q *
          (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
        C0 * (Real.log T) ^ (q + E) := by
    have hleft0 : 0 ≤ C * (Real.log T) ^ q :=
      mul_nonneg hC.le (pow_nonneg hlog0 q)
    calc
      C * (Real.log T) ^ q *
          (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
          C * (Real.log T) ^ q * (B0 * Real.log T) ^ E :=
        mul_le_mul_of_nonneg_left hpowBase hleft0
      _ = C0 * (Real.log T) ^ (q + E) := by
        dsimp only [C0]
        rw [mul_pow, pow_add]
        ring
  have hpowNonneg : 0 ≤ T ^ eps := Real.rpow_nonneg hTpos.le _
  calc
    C * (Real.log T) ^ q *
        (1 + Real.log (maynardMontgomeryRaisedWidthConstant * (N : ℝ))) ^ e ≤
        C0 * (Real.log T) ^ (q + E) := hpoly
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogPow (pow_nonneg hlog0 _) hpowNonneg
    _ = T ^ (maynardLongGlobalAmplitudeDeficit / m) := by
      rw [← Real.rpow_add hTpos]
      dsimp only [eps]
      congr 1
      field_simp
      ring

end RHTower.Sieve
