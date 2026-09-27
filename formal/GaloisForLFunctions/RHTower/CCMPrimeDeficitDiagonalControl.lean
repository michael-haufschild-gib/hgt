import GaloisForLFunctions.RHTower.CCMPrimeDeficitPairEnergy
import GaloisForLFunctions.RHTower.CCMPrimeEntryJumpBudget

/-!
# Polynomial control of the actual prime-entry diagonal

The self-interactions in the critical prime-pair energy are bounded by twice
the harmonic von Mangoldt square moment. The corpus' sharp moment estimate
therefore gives an explicit quadratic bound in logarithmic time. The
remaining centered off-diagonal keeps the continuous and mixed terms with
their signs; no upper bound on it is asserted.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace RHTower

def ccmPrimeEntryDiagonal (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ArithmeticFunction.vonMangoldt n ^ 2 *
    ccmPrimeEntryOverlap T (Real.log n) (Real.log n)

def ccmPrimeEntryCenteredOffDiagonal (T : ℝ) : ℝ :=
  Real.exp T - Real.exp (-T) - 2 * T -
    2 * ccmPrimeEntryBackgroundPrefix T ⌊Real.exp T⌋₊ +
      (ccmPrimeEntryPairPrefix T ⌊Real.exp T⌋₊ - ccmPrimeEntryDiagonal T)

theorem ccmPrimeEntryDiagonal_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ ccmPrimeEntryDiagonal T :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _)
    (ccmPrimeEntryOverlap_nonneg hT _ _)

theorem ccmPrimeEntryDiagonal_le_harmonic_square {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryDiagonal T ≤ 2 * Sieve.vonMangoldtHarmonicSquareSum ⌊Real.exp T⌋₊ := by
  have hN : 1 ≤ ⌊Real.exp T⌋₊ :=
    (Nat.le_floor_iff (Real.exp_pos T).le).mpr (by simpa using Real.one_le_exp_iff.mpr hT)
  rw [Sieve.vonMangoldtHarmonicSquareSum_eq_Icc_one _ hN, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hlogT : Real.log n ≤ T := (Real.log_le_iff_le_exp (zero_lt_one.trans_le hnR)).mpr
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT)
  have hb := ccmPrimeEntryOverlap_le_limit (by simpa only [max_self] using hlog0) hlogT hlogT
  rw [ccmPrimeEntryOverlapLimit_log_self (Nat.zero_lt_one.trans_le hn1)] at hb
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n ^ 2 * (2 / n) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

/-- Actual unconditional polynomial bound for every diagonal interaction.
It retains the full prime-power von Mangoldt weights. -/
theorem ccmPrimeEntryDiagonal_le_quadratic {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryDiagonal T ≤ T ^ 2 + 78 * T + 50 := by
  exact (ccmPrimeEntryDiagonal_le_harmonic_square hT).trans
    (ccmPrimeEntryJumpBudget_le_quadratic hT)

/-- The full energy splits into its controlled diagonal and its signed
centered off-diagonal. The latter retains both large background terms. -/
theorem ccmPrimeDeficitCriticalEnergy_integral_eq_diagonal_add_centered {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      ccmPrimeEntryDiagonal T + ccmPrimeEntryCenteredOffDiagonal T := by
  rw [ccmPrimeDeficitCriticalEnergy_integral_eq_pair hT]
  unfold ccmPrimeEntryCenteredOffDiagonal
  ring

theorem ccmPrimeEntryDiagonal_eq_zero_before_first_prime {T : ℝ} (hT : T < Real.log 2) :
    ccmPrimeEntryDiagonal T = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn1, hnT⟩ := Finset.mem_Icc.mp hn
  have he : Real.exp T < 2 := (Real.lt_log_iff_exp_lt (by norm_num)).mp hT
  have hnR : (n : ℝ) < 2 :=
    ((Nat.le_floor_iff (Real.exp_pos T).le).mp hnT).trans_lt he
  have hn2 : n < 2 := by exact_mod_cast hnR
  have hn : n = 1 := by omega
  simp only [hn, ArithmeticFunction.vonMangoldt_apply_one, zero_pow (by norm_num : 2 ≠ 0), zero_mul]

/-- The strongest proposed cancellation sign already fails before the
first prime. Any viable upper bound must allow a positive finite budget. -/
theorem ccmPrimeEntryCenteredOffDiagonal_pos_before_first_prime {T : ℝ}
    (hT : 0 < T) (hfirst : T < Real.log 2) :
    0 < ccmPrimeEntryCenteredOffDiagonal T := by
  have he := ccmPrimeDeficitCriticalEnergy_integral_eq_diagonal_add_centered hT.le
  rw [ccmPrimeEntryDiagonal_eq_zero_before_first_prime hfirst, zero_add] at he
  rw [← he]
  apply intervalIntegral.integral_pos hT continuous_ccmPrimeDeficitCriticalEnergy.continuousOn
    (fun t _ => ccmPrimeDeficitCriticalEnergy_nonneg t)
  refine ⟨T / 2, ⟨by linarith, by linarith⟩, ?_⟩
  exact ccmPrimeDeficitCriticalEnergy_pos_before_first_prime (by linarith) (by linarith)

end RHTower
