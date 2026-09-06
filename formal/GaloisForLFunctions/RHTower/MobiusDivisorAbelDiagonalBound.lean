import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Harmonic bound for the literal Möbius–divisor Abel diagonal

Every actual dilation channel obeys `sqrt d * |C_d(M)| <= 12 M`. Squaring and
summing gives the unconditional bound `sum C_d(M)^2 <= 144 M^2 sum_(d<=M) 1/d`.
The proof uses the existing analytic divisor-defect envelope, square-root algebra,
and finite sums. Exact channel and diagonal successor laws retain the signed mixed
term responsible for changes of the diagonal. No numerical certificate enters the proof.

This bounds only the diagonal. It does not prove source diagonal dominance
`(sum C_d(M))^2 <= sum C_d(M)^2`, or any RH-bearing cross-term estimate.
-/

noncomputable section
open Finset
namespace RHTower

private theorem sqrt_step_nonneg (k : ℕ) :
    0 ≤ Real.sqrt (k + 1 : ℕ) - Real.sqrt k := by
  apply sub_nonneg.mpr
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ k)

private theorem sqrt_step_mul_sqrt_le_half (k : ℕ) :
    (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * Real.sqrt k ≤ 1 / 2 := by
  have hk := Real.sq_sqrt (show (0 : ℝ) ≤ k from Nat.cast_nonneg k)
  have hk1 := Real.sq_sqrt (show (0 : ℝ) ≤ (k + 1 : ℕ) from Nat.cast_nonneg _)
  have hn := sq_nonneg (Real.sqrt (k + 1 : ℕ) - Real.sqrt k)
  push_cast at hk1 hn ⊢
  nlinarith

private theorem scaled_divisor_defect_step_le
    {d k : ℕ} (hd : 1 ≤ d) (hdk : d ≤ k) :
    Real.sqrt d * ((Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
      |primeFreeDivisorDefect (k / d)|) ≤ 12 := by
  have hq : 1 ≤ k / d := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hdk)
  have hD := abs_primeFreeDivisorDefect_le hq
  have hroot : Real.sqrt d * Real.sqrt (k / d : ℕ) ≤ Real.sqrt k := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show d * (k / d) ≤ k by simpa [Nat.mul_comm] using Nat.div_mul_le_self k d)
  have hscaled : Real.sqrt d * |primeFreeDivisorDefect (k / d)| ≤ 24 * Real.sqrt k := by
    have hmul := mul_le_mul_of_nonneg_left hD (Real.sqrt_nonneg d)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hscaled (sqrt_step_nonneg k)
  have hhalf := sqrt_step_mul_sqrt_le_half k
  nlinarith

/-- Every literal dilation channel has a square-root-weighted absolute ceiling. -/
theorem sqrt_mul_abs_mobiusDivisorDilationChannel_le (M d : ℕ) (hd : 1 ≤ d) :
    Real.sqrt d * |mobiusDivisorDilationChannel M d| ≤ 12 * M := by
  have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  let f : ℕ → ℝ := fun k => (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
    primeFreeDivisorDefect (k / d)
  have hsum : Real.sqrt d * |∑ k ∈ Icc d (M - 1), f k| ≤ 12 * M := by
    calc
      _ ≤ Real.sqrt d * ∑ k ∈ Icc d (M - 1), |f k| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (Real.sqrt_nonneg d)
      _ = ∑ k ∈ Icc d (M - 1), Real.sqrt d * |f k| := by
        rw [Finset.mul_sum]
      _ ≤ ∑ _k ∈ Icc d (M - 1), (12 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        dsimp [f]
        rw [abs_mul, abs_of_nonneg (sqrt_step_nonneg k)]
        exact scaled_divisor_defect_step_le hd (Finset.mem_Icc.mp hk).1
      _ ≤ 12 * M := by
        simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        have hcard : M - 1 + 1 - d ≤ M := by omega
        have hcast : ((M - 1 + 1 - d : ℕ) : ℝ) ≤ M := by exact_mod_cast hcard
        nlinarith
  have hraw : |mobiusDivisorDilationChannel M d| ≤ |∑ k ∈ Icc d (M - 1), f k| := by
    rw [mobiusDivisorDilationChannel, abs_mul]
    change |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |∑ k ∈ Icc d (M - 1), f k| ≤ _
    simpa using mul_le_mul_of_nonneg_right hmu (abs_nonneg (∑ k ∈ Icc d (M - 1), f k))
  exact (mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg d)).trans hsum

/-- Unconditional harmonic ceiling for the complete arithmetic diagonal. This does not
control the signed off-diagonal sum required by source diagonal dominance. -/
theorem sum_mobiusDivisorDilationChannel_sq_le_harmonic (M : ℕ) :
    (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d ^ 2) ≤
      144 * (M : ℝ) ^ 2 * ∑ d ∈ Icc 1 M, (1 : ℝ) / d := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 M) :
      mobiusDivisorDilationChannel M d ^ 2 ≤ 144 * (M : ℝ) ^ 2 / d := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have h := sqrt_mul_abs_mobiusDivisorDilationChannel_le M d hd1
    have hsq : (d : ℝ) * mobiusDivisorDilationChannel M d ^ 2 ≤ 144 * (M : ℝ) ^ 2 := by
      calc
        _ = (Real.sqrt d * |mobiusDivisorDilationChannel M d|) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d), sq_abs]
        _ ≤ (12 * (M : ℝ)) ^ 2 := by gcongr
        _ = _ := by ring
    exact (le_div_iff₀ hdpos).mpr (by simpa [mul_comm] using hsq)
  calc
    _ ≤ ∑ d ∈ Icc 1 M, 144 * (M : ℝ) ^ 2 / d := Finset.sum_le_sum hpoint
    _ = _ := by simp only [div_eq_mul_inv, one_mul, Finset.mul_sum]


/-- Each existing dilation channel gains its literal next-time divisor-defect increment. -/
theorem mobiusDivisorDilationChannel_succ_of_le {M d : ℕ} (hd : 1 ≤ d) (hdM : d ≤ M) :
    mobiusDivisorDilationChannel (M + 1) d = mobiusDivisorDilationChannel M d +
      (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d) := by
  have hpred : M - 1 + 1 = M := by omega
  let f : ℕ → ℝ := fun k => (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) *
    primeFreeDivisorDefect (k / d)
  have hs : (∑ k ∈ Icc d M, f k) = (∑ k ∈ Icc d (M - 1), f k) + f M := by
    simpa only [hpred] using
      (Finset.sum_Icc_succ_top (f := f) (show d ≤ M - 1 + 1 by omega))
  simp only [mobiusDivisorDilationChannel, Nat.add_sub_cancel]
  change _ * (∑ k ∈ Icc d M, f k) = _ * (∑ k ∈ Icc d (M - 1), f k) + _
  rw [hs]
  dsimp [f]
  ring

/-- Exact change of the complete arithmetic diagonal. Its signed mixed term is retained;
nonnegativity of the pointwise squares does not determine the sign of this change. -/
theorem sum_mobiusDivisorDilationChannel_sq_succ_sub (M : ℕ) :
    (∑ d ∈ Icc 1 (M + 1), mobiusDivisorDilationChannel (M + 1) d ^ 2) -
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d ^ 2) =
    2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d *
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d))) +
    (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ 2 *
      ∑ d ∈ Icc 1 M,
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ 2 := by
  have hzero : mobiusDivisorDilationChannel (M + 1) (M + 1) = 0 := by
    simp [mobiusDivisorDilationChannel]
  rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega), hzero]
  simp only [zero_pow (show 2 ≠ 0 by decide), add_zero]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ d ∈ Icc 1 M,
        (2 * (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) *
          (mobiusDivisorDilationChannel M d *
            (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d))) +
        (Real.sqrt (M + 1 : ℕ) - Real.sqrt M) ^ 2 *
          (((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (M / d)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [mobiusDivisorDilationChannel_succ_of_le (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

end RHTower
