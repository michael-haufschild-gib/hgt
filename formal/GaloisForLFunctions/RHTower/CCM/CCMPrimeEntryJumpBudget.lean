import GaloisForLFunctions.RHTower.Sieve.VonMangoldtHarmonicSquareAsymptotic

/-!
# Exact scale of the prime-entry jump budget

The squared normalized von Mangoldt jumps accumulate quadratically in
logarithmic time. Both sides of this estimate are unconditional; the
budget cannot itself be replaced by a constant.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeEntryJumpBudget (T : ℝ) : ℝ :=
  2 * Sieve.vonMangoldtHarmonicSquareSum ⌊Real.exp T⌋₊

theorem ccmPrimeEntryJumpBudget_eq_sum {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryJumpBudget T =
      2 * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        ArithmeticFunction.vonMangoldt n ^ 2 / (n : ℝ) := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  exact congrArg (2 * ·) (Sieve.vonMangoldtHarmonicSquareSum_eq_Icc_one _ hN)

theorem ccmPrimeEntryJumpBudget_nonneg (T : ℝ) : 0 ≤ ccmPrimeEntryJumpBudget T := by
  unfold ccmPrimeEntryJumpBudget Sieve.vonMangoldtHarmonicSquareSum
  positivity

theorem ccmPrimeEntryJumpBudget_le_quadratic {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryJumpBudget T ≤ T ^ 2 + 78 * T + 50 := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ ⌊Real.exp T⌋₊ := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (⌊Real.exp T⌋₊ : ℝ) := Real.log_nonneg hNR
  have hlogT : Real.log (⌊Real.exp T⌋₊ : ℝ) ≤ T :=
    (Real.log_le_iff_le_exp (zero_lt_one.trans_le hNR)).mpr (Nat.floor_le (Real.exp_pos T).le)
  have hm := (abs_le.mp (Sieve.abs_vonMangoldtHarmonicSquareSum_sub_le _ hN)).2
  have hs : Real.log (⌊Real.exp T⌋₊ : ℝ) ^ 2 ≤ T ^ 2 := by gcongr
  unfold ccmPrimeEntryJumpBudget
  linarith only [hm, hs, hlogT]

/-- Moving from the integer cutoff to real logarithmic time costs at most
one logarithmic unit, hence only a linear error in the square budget. -/
theorem quadratic_le_ccmPrimeEntryJumpBudget {T : ℝ} (hT : 0 ≤ T) :
    T ^ 2 - 80 * T - 50 ≤ ccmPrimeEntryJumpBudget T := by
  let N := ⌊Real.exp T⌋₊
  have hN : 1 ≤ N :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos := zero_lt_one.trans_le hNR
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hlogT : Real.log (N : ℝ) ≤ T :=
    (Real.log_le_iff_le_exp hpos).mpr (Nat.floor_le (Real.exp_pos T).le)
  have hfloor : Real.exp T < 2 * (N : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.exp T)
    dsimp only [N]
    linarith
  have hclose : T ≤ Real.log (N : ℝ) + 1 := by
    have h := (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < 2 * N)).mpr hfloor
    rw [Real.log_mul (by norm_num) (ne_of_gt hpos)] at h
    have htwo : Real.log (2 : ℝ) ≤ 1 := by
      have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at hb
      exact hb
    linarith
  have hs : T ^ 2 ≤ Real.log (N : ℝ) ^ 2 + 2 * T := by
    have hp := mul_le_mul_of_nonneg_right
      (show T - Real.log (N : ℝ) ≤ 1 by linarith) (add_nonneg hT hlog0)
    nlinarith only [hp, hlogT]
  have hm := (abs_le.mp (Sieve.abs_vonMangoldtHarmonicSquareSum_sub_le N hN)).1
  change T ^ 2 - 80 * T - 50 ≤ 2 * Sieve.vonMangoldtHarmonicSquareSum N
  linarith only [hm, hs, hlogT]

theorem abs_ccmPrimeEntryJumpBudget_sub_sq_le {T : ℝ} (hT : 0 ≤ T) :
    |ccmPrimeEntryJumpBudget T - T ^ 2| ≤ 80 * T + 50 := by
  rw [abs_le]
  constructor
  · linarith only [quadratic_le_ccmPrimeEntryJumpBudget hT]
  · linarith only [ccmPrimeEntryJumpBudget_le_quadratic hT, hT]

end RHTower
