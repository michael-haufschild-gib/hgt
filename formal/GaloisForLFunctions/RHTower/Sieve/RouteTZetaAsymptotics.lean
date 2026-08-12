import GaloisForLFunctions.RHTower.Sieve.RouteTMoebiusSharp

/-!
# Explicit asymptotic envelopes for Route-T contour parameters

These estimates expose the analytic scale hidden behind Route T's discrete binary shell.  They are
proved from the exact `clog`/`nthRoot` definitions, so later endpoint absorption uses no informal
replacement of integer parameters by logarithms.
-/

namespace RHTower.Sieve

open Complex Filter Topology

noncomputable section

/-- Continuous logarithmic envelope for the discrete binary height. -/
def routeTLogHeightEnvelope (t : ℝ) : ℝ :=
  2 * Real.log (t + 2) + 1

/-- Above height two, the binary height is nonzero. -/
theorem routeTBinaryHeight_pos {t : ℝ} (ht : 2 ≤ t) :
    1 ≤ routeTBinaryHeight t := by
  unfold routeTBinaryHeight
  apply Nat.clog_pos (by norm_num)
  have hceil : 2 ≤ ⌈t⌉₊ := by
    have : (2 : ℝ) ≤ (⌈t⌉₊ : ℝ) := ht.trans (Nat.le_ceil t)
    exact_mod_cast this
  omega

/-- The logarithmic envelope is at least one on the positive-height range. -/
theorem routeTLogHeightEnvelope_one_le {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ routeTLogHeightEnvelope t := by
  have harg : (1 : ℝ) ≤ t + 2 := by linarith
  have hlog : 0 ≤ Real.log (t + 2) := Real.log_nonneg harg
  unfold routeTLogHeightEnvelope
  linarith

/-- Binary height is at most twice the natural logarithmic height, up to one unit. -/
theorem routeTBinaryHeight_cast_lt_two_log_add_one
    {t : ℝ} (ht : 2 ≤ t) :
    (routeTBinaryHeight t : ℝ) < routeTLogHeightEnvelope t := by
  let n : ℕ := ⌈t⌉₊
  let L : ℕ := Nat.clog 2 n
  have hn2 : 2 ≤ n := by
    dsimp only [n]
    have hreal : (2 : ℝ) ≤ (⌈t⌉₊ : ℝ) := ht.trans (Nat.le_ceil t)
    exact_mod_cast hreal
  have hL0 : 0 < L := Nat.clog_pos (by norm_num) (by omega)
  have hpowNat : 2 ^ L.pred < n := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hpow0 : (0 : ℝ) < ((2 ^ L.pred : ℕ) : ℝ) := by positivity
  have hnreal : (n : ℝ) < t + 1 := by
    dsimp only [n]
    exact Nat.ceil_lt_add_one (by linarith)
  have ht2pos : 0 < t + 2 := by linarith
  have hpowReal : ((2 ^ L.pred : ℕ) : ℝ) < t + 2 := by
    have : ((2 ^ L.pred : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hpowNat
    linarith
  have hlog := Real.log_lt_log hpow0 hpowReal
  have hlogPow : Real.log (((2 ^ L.pred : ℕ) : ℝ)) =
      (L.pred : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hpred : (L.pred : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  rw [hlogPow, hpred] at hlog
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hLcast : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL0
  have hmul : ((L : ℝ) - 1) / 2 ≤ ((L : ℝ) - 1) * Real.log 2 := by
    have hnonneg : 0 ≤ (L : ℝ) - 1 := by linarith
    have := mul_le_mul_of_nonneg_left hlog2.le hnonneg
    nlinarith
  have hmain : (L : ℝ) < 2 * Real.log (t + 2) + 1 := by
    nlinarith
  simpa only [routeTBinaryHeight, routeTLogHeightEnvelope, n, L] using hmain

private theorem routeT_nthRoot_nine_le_rpow
    {L : ℕ} (hL : 1 ≤ L) :
    ((Nat.nthRoot 10 L : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (L : ℝ) ^ ((9 : ℝ) / 10) := by
  let r : ℕ := Nat.nthRoot 10 L
  have hr1 : 1 ≤ r := by
    apply (Nat.le_nthRoot_iff (by norm_num)).2
    simpa using hL
  have hrpowNat : r ^ 10 ≤ L := by
    dsimp only [r]
    exact Nat.pow_nthRoot_le (Or.inl (by norm_num))
  have hrpow : ((r : ℝ) ^ (10 : ℕ)) ≤ (L : ℝ) := by exact_mod_cast hrpowNat
  have hr0 : 0 ≤ (r : ℝ) ^ (10 : ℕ) := by positivity
  have hmono := Real.rpow_le_rpow hr0 hrpow (by norm_num : (0 : ℝ) ≤ 9 / 10)
  have hcollapse : (((r : ℝ) ^ (10 : ℕ)) : ℝ) ^ ((9 : ℝ) / 10) =
      (r : ℝ) ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r)]
    norm_num
  rw [hcollapse] at hmono
  simpa only [r] using hmono

/-- The ninth power entering every Route-T strip parameter preserves the exact `9/10` exponent. -/
theorem routeTBandShell_add_one_pow_nine_le
    {t : ℝ} (hL : 1 ≤ routeTBinaryHeight t) :
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTBinaryHeight t : ℝ) ^ ((9 : ℝ) / 10) := by
  let L : ℕ := routeTBinaryHeight t
  let r : ℕ := Nat.nthRoot 10 L
  have hr1 : 1 ≤ r := by
    apply (Nat.le_nthRoot_iff (by norm_num)).2
    simpa only [one_pow, L] using hL
  have hadd : r + 3 ≤ 4 * r := by omega
  have hpowNat : (r + 3) ^ 9 ≤ (4 * r) ^ 9 := Nat.pow_le_pow_left hadd 9
  have hpowReal : ((r + 3 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      ((4 * r : ℕ) : ℝ) ^ (9 : ℕ) := by exact_mod_cast hpowNat
  have hroot := routeT_nthRoot_nine_le_rpow (L := L) hL
  calc
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) =
        ((r + 3 : ℕ) : ℝ) ^ (9 : ℕ) := by rfl
    _ ≤ ((4 * r : ℕ) : ℝ) ^ (9 : ℕ) := hpowReal
    _ = (4 : ℝ) ^ (9 : ℕ) * (r : ℝ) ^ (9 : ℕ) := by
      push_cast
      rw [mul_pow]
    _ ≤ (4 : ℝ) ^ (9 : ℕ) * (L : ℝ) ^ ((9 : ℝ) / 10) :=
      mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = (4 : ℝ) ^ (9 : ℕ) *
        (routeTBinaryHeight t : ℝ) ^ ((9 : ℝ) / 10) := by rfl

/-- The exact shell denominator is controlled by the continuous logarithmic envelope. -/
theorem routeTBandShell_add_one_pow_nine_le_logHeight
    {t : ℝ} (ht : 2 ≤ t) :
    ((routeTBandShell t + 1 : ℕ) : ℝ) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
  have hL1 := routeTBinaryHeight_pos ht
  have hshell := routeTBandShell_add_one_pow_nine_le hL1
  have hL0 : (0 : ℝ) ≤ routeTBinaryHeight t := by positivity
  have hLenvelope := (routeTBinaryHeight_cast_lt_two_log_add_one ht).le
  have hrpow := Real.rpow_le_rpow hL0 hLenvelope (by norm_num : (0 : ℝ) ≤ 9 / 10)
  exact hshell.trans (mul_le_mul_of_nonneg_left hrpow (by positivity))

/-- Route T's strip width retains a quantitative `log(t)^(-9/10)` lower envelope. -/
theorem routeTStripWidth_logHeight_lower
    {t : ℝ} (ht : 2 ≤ t) :
    1 / ((routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10)) ≤
      routeTStripWidth (routeTBandShell t) := by
  have hshell := routeTBandShell_add_one_pow_nine_le_logHeight ht
  have hshell' : ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) ≤
      (4 : ℝ) ^ (9 : ℕ) *
        (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hshell
  have hden :
      ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) ≤
        (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
          (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    calc
      (routeTStripDenominator : ℝ) *
          ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) ≤
          (routeTStripDenominator : ℝ) *
            ((4 : ℝ) ^ (9 : ℕ) *
              (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_left hshell' (by positivity)
      _ = (routeTStripDenominator : ℝ) * (4 : ℝ) ^ (9 : ℕ) *
          (routeTLogHeightEnvelope t) ^ ((9 : ℝ) / 10) := by ring
  have hactual :
      (0 : ℝ) < ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos routeTStripDenominator_pos
      (pow_pos (by omega : 0 < routeTBandShell t + 1) 9)
  unfold routeTStripWidth
  exact one_div_le_one_div_of_le hactual hden

end

end RHTower.Sieve
