import GaloisForLFunctions.RHTower.Sieve.MaynardWeightedFiniteSet

/-!
# Canonical Huxley frequency schedule

For a dyadic block of length `N`, choose switch frequency `U=N` and take the exact second-
derivative envelope, clipped below by one.  This removes all free schedule choices from the
all-short large-values theorem.  Its only regime condition is the transparent inequality
`T <= 8*pi*N^(2 : ℕ)`.
-/

noncomputable section

namespace RHTower.Sieve

/-- Natural first/second derivative switch for a dyadic block. -/
def maynardHuxleyU (N : ℕ) : ℝ := N

/-- Exact canonical second-derivative envelope, with Schur's required lower bound. -/
def maynardHuxleyB (N : ℕ) (T : ℝ) : ℝ :=
  max 1 (logDyadicSecondEnvelope N N T)

theorem maynardHuxleyU_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < maynardHuxleyU N := by
  dsimp [maynardHuxleyU]
  exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN

theorem maynardHuxleyU_near {N : ℕ} :
    3 * maynardHuxleyU N ≤ 4 * Real.pi * (N : ℝ) := by
  dsimp [maynardHuxleyU]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.pi_gt_three]

theorem logDyadicLambda_eq (N : ℕ) (T : ℝ) :
    logDyadicLambda N T = T / (8 * Real.pi * (N : ℝ) ^ 2) := by
  simp only [logDyadicLambda]
  norm_num
  ring

theorem logDyadicLambda_le_one_of_height_le
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ}
    (hT : T ≤ 8 * Real.pi * (N : ℝ) ^ 2) :
    logDyadicLambda N T ≤ 1 := by
  rw [logDyadicLambda_eq]
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hden : 0 < 8 * Real.pi * (N : ℝ) ^ 2 := by positivity
  exact (div_le_one hden).2 hT

theorem logDyadicSecondEnvelope_le_maynardHuxleyB (N : ℕ) (T : ℝ) :
    logDyadicSecondEnvelope N (maynardHuxleyU N) T ≤ maynardHuxleyB N T := by
  exact le_max_right _ _

theorem one_le_maynardHuxleyB (N : ℕ) (T : ℝ) :
    1 ≤ maynardHuxleyB N T := by
  exact le_max_left _ _

/-- Canonical envelope has square-root size in height and block length. -/
theorem logDyadicSecondEnvelope_self_le
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    logDyadicSecondEnvelope N (N : ℝ) T ≤
      256 * (Real.sqrt T + 8 * Real.sqrt (N : ℝ)) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hpi2 : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have hpi4 : Real.pi ≤ (4 : ℝ) := Real.pi_le_four
  have hfirstBase : 16 * logDyadicLambda N T ≤ T / (N : ℝ) ^ 2 := by
    rw [logDyadicLambda_eq]
    have hN2 : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hNR
    have hpi : 0 < Real.pi := Real.pi_pos
    field_simp
    nlinarith
  have hfirstBase0 : 0 ≤ 16 * logDyadicLambda N T := by
    rw [logDyadicLambda_eq]
    positivity
  have hquot0 : 0 ≤ T / (N : ℝ) ^ 2 := by positivity
  have hfirstPow : (16 * logDyadicLambda N T) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (T / (N : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hfirstBase0 hfirstBase (by norm_num)
  have hfirst : (N : ℝ) * (16 * logDyadicLambda N T) ^ (1 / 2 : ℝ) ≤
      Real.sqrt T := by
    calc
      (N : ℝ) * (16 * logDyadicLambda N T) ^ (1 / 2 : ℝ)
          ≤ (N : ℝ) * Real.sqrt (T / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hfirstPow hNR.le
      _ = Real.sqrt T := by
        rw [Real.sqrt_div hT, Real.sqrt_sq_eq_abs, abs_of_pos hNR]
        field_simp
  have hlamSelf : logDyadicLambda N (N : ℝ) =
      1 / (8 * Real.pi * (N : ℝ)) := by
    rw [logDyadicLambda_eq]
    field_simp
  have hsecondEq : (logDyadicLambda N (N : ℝ)) ^ (-(1 / 2 : ℝ)) =
      Real.sqrt (8 * Real.pi * (N : ℝ)) := by
    rw [hlamSelf, Real.rpow_neg_eq_inv_rpow, ← Real.sqrt_eq_rpow]
    congr 1
    field_simp
  have hsecond : (logDyadicLambda N (N : ℝ)) ^ (-(1 / 2 : ℝ)) ≤
      8 * Real.sqrt (N : ℝ) := by
    rw [hsecondEq]
    calc
      Real.sqrt (8 * Real.pi * (N : ℝ)) ≤ Real.sqrt (64 * (N : ℝ)) := by
        have hgap0 : 0 ≤ (8 : ℝ) - Real.pi := by linarith
        exact Real.sqrt_le_sqrt (by
          nlinarith [mul_nonneg hgap0 (Nat.cast_nonneg N)])
      _ = 8 * Real.sqrt (N : ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
        norm_num
  unfold logDyadicSecondEnvelope
  gcongr

/-- Explicit upper bound for the clipped canonical envelope. -/
theorem maynardHuxleyB_le
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    maynardHuxleyB N T ≤
      1 + 256 * (Real.sqrt T + 8 * Real.sqrt (N : ℝ)) := by
  apply max_le
  · nlinarith [Real.sqrt_nonneg T, Real.sqrt_nonneg (N : ℝ)]
  · exact (logDyadicSecondEnvelope_self_le hN hT).trans (by linarith)

end RHTower.Sieve
