import GaloisForLFunctions.HTGeometry.FejerKernel

/-!
# Convex cancellation of geometric phases

Twice-cumulative coefficients of a geometric phase chain are nonnegative.
Two finite summations by parts therefore pay every unequal phase against
nonnegative second differences of the coefficient sequence.
-/

open Complex Finset
open scoped ComplexConjugate
noncomputable section
namespace HTGeometry

private theorem finite_abel (u f : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ range (N + 1), u k * f k) =
      f N * (∑ k ∈ range (N + 1), u k) +
        ∑ k ∈ range N, (f k - f (k + 1)) * (∑ j ∈ range (k + 1), u j) := by
  induction N with
  | zero => simp [mul_comm]
  | succ N ih =>
    rw [sum_range_succ (fun k => u k * f k) (N + 1), ih,
      sum_range_succ u (N + 1),
      sum_range_succ (fun k => (f k - f (k + 1)) * (∑ j ∈ range (k + 1), u j)) N]
    ring

/-- Ordered-pair phases with a fixed total exponent. -/
def geometricDiagonal (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => z ^ (n + 1) + conj z * geometricDiagonal z n

/-- First cumulative real phase coefficient. -/
def geometricDiagonalPrefix (z : ℂ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), (geometricDiagonal z k).re

/-- Second cumulative real phase coefficient. -/
def geometricDiagonalCumulative (z : ℂ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), geometricDiagonalPrefix z k

theorem geometricDiagonal_eq_sum (z : ℂ) (n : ℕ) :
    geometricDiagonal z n = ∑ k ∈ range (n + 1), z ^ k * conj z ^ (n - k) := by
  induction n with
  | zero => simp [geometricDiagonal]
  | succ n ih =>
    rw [geometricDiagonal, ih]
    conv_rhs => rw [sum_range_succ]
    rw [mul_sum]
    simp only [Nat.sub_self, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring

theorem geometricDiagonal_recurrence {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    geometricDiagonal z (n + 2) =
      (z + conj z) * geometricDiagonal z (n + 1) - geometricDiagonal z n := by
  have hzz : z * conj z = 1 := by
    rw [Complex.mul_conj', hz]
    norm_num
  rw [show n + 2 = (n + 1) + 1 by omega, geometricDiagonal,
    geometricDiagonal, pow_succ]
  linear_combination -(geometricDiagonal z n) * hzz

theorem geometricDiagonal_re_recurrence {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    (geometricDiagonal z (n + 2)).re =
      2 * z.re * (geometricDiagonal z (n + 1)).re - (geometricDiagonal z n).re := by
  rw [geometricDiagonal_recurrence hz]
  simp only [Complex.sub_re, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, add_neg_cancel, zero_mul, sub_zero]
  ring

theorem geometricDiagonal_norm_le {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    ‖geometricDiagonal z n‖ ≤ (n : ℝ) + 1 := by
  induction n with
  | zero => simp [geometricDiagonal]
  | succ n ih =>
    rw [geometricDiagonal]
    calc
      _ ≤ ‖z ^ (n + 1)‖ + ‖conj z * geometricDiagonal z n‖ := norm_add_le _ _
      _ = 1 + ‖geometricDiagonal z n‖ := by
        rw [norm_pow, norm_mul, Complex.norm_conj, hz, one_pow, one_mul]
      _ ≤ (↑(n + 1) : ℝ) + 1 := by push_cast; linarith only [ih]

theorem geometricDiagonalPrefix_factor {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    (2 - 2 * z.re) * geometricDiagonalPrefix z n =
      1 + (geometricDiagonal z n).re - (geometricDiagonal z (n + 1)).re := by
  induction n with
  | zero => simp [geometricDiagonalPrefix, geometricDiagonal]; ring
  | succ n ih =>
    rw [geometricDiagonalPrefix, sum_range_succ]
    change (2 - 2 * z.re) *
      (geometricDiagonalPrefix z n + (geometricDiagonal z (n + 1)).re) = _
    rw [mul_add, ih, geometricDiagonal_re_recurrence hz]
    ring

theorem geometricDiagonalCumulative_factor {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    (2 - 2 * z.re) * geometricDiagonalCumulative z n =
      (n : ℝ) + 2 - (geometricDiagonal z (n + 1)).re := by
  induction n with
  | zero => simp [geometricDiagonalCumulative, geometricDiagonalPrefix, geometricDiagonal]; ring
  | succ n ih =>
    rw [geometricDiagonalCumulative, sum_range_succ]
    change (2 - 2 * z.re) *
      (geometricDiagonalCumulative z n + geometricDiagonalPrefix z (n + 1)) = _
    rw [mul_add, ih, geometricDiagonalPrefix_factor hz]
    push_cast
    ring

theorem geometricDiagonal_re_of_re_one {z : ℂ} (hz : ‖z‖ = 1) (hc : z.re = 1)
    (n : ℕ) : (geometricDiagonal z n).re = (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [geometricDiagonal]
  | one => simp [geometricDiagonal, hc]
  | more n ih0 ih1 =>
    rw [geometricDiagonal_re_recurrence hz, hc, ih0, ih1]
    push_cast
    ring

/-- Twice-cumulative multiplicative-chain phases are nonnegative at every frequency. -/
theorem geometricDiagonalCumulative_nonneg {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) :
    0 ≤ geometricDiagonalCumulative z n := by
  have hc : z.re ≤ 1 := (Complex.re_le_norm z).trans_eq hz
  rcases lt_or_eq_of_le hc with hc | hc
  · have hfactor := geometricDiagonalCumulative_factor hz n
    have hupper := (Complex.re_le_norm (geometricDiagonal z (n + 1))).trans
      (geometricDiagonal_norm_le hz (n + 1))
    have hn : 0 ≤ (2 - 2 * z.re) * geometricDiagonalCumulative z n := by
      rw [hfactor]
      push_cast at hupper
      linarith only [hupper]
    exact nonneg_of_mul_nonneg_right hn (by linarith only [hc])
  · apply sum_nonneg
    intro k _
    apply sum_nonneg
    intro j _
    rw [geometricDiagonal_re_of_re_one hz hc]
    positivity

/-- Exact second-difference payment of all phases, with each coefficient used once. -/
theorem geometricDiagonal_weighted_eq_secondDifference (z : ℂ) (f : ℕ → ℝ) (N : ℕ)
    (hN : f N = 0) (hN1 : f (N + 1) = 0) :
    (∑ k ∈ range (N + 1), f k * (geometricDiagonal z k).re) =
      ∑ k ∈ range N, (f k - 2 * f (k + 1) + f (k + 2)) *
        geometricDiagonalCumulative z k := by
  let g : ℕ → ℝ := fun k => f k - f (k + 1)
  have hfirst := finite_abel (fun k => (geometricDiagonal z k).re) f N
  rw [hN, zero_mul, zero_add] at hfirst
  have hsecond := finite_abel (geometricDiagonalPrefix z) g N
  have hgN : g N = 0 := by simp only [g, hN, hN1, sub_self]
  rw [hgN, zero_mul, zero_add, sum_range_succ, hgN, mul_zero, add_zero] at hsecond
  calc
    _ = ∑ k ∈ range N, g k * geometricDiagonalPrefix z k := by
      simpa only [mul_comm, g, geometricDiagonalPrefix] using hfirst
    _ = ∑ k ∈ range N, (g k - g (k + 1)) * geometricDiagonalCumulative z k := by
      simpa only [mul_comm, geometricDiagonalCumulative] using hsecond
    _ = _ := by
      apply sum_congr rfl
      intro k _
      dsimp only [g]
      rw [show k + 1 + 1 = k + 2 by omega]
      ring

/-- A finite convex weight cancels every unequal phase of a multiplicative chain. -/
theorem geometricDiagonal_weighted_nonneg {z : ℂ} (hz : ‖z‖ = 1)
    (f : ℕ → ℝ) (N : ℕ) (hN : f N = 0) (hN1 : f (N + 1) = 0)
    (hf : ∀ k < N, 0 ≤ f k - 2 * f (k + 1) + f (k + 2)) :
    0 ≤ ∑ k ∈ range (N + 1), f k * (geometricDiagonal z k).re := by
  rw [geometricDiagonal_weighted_eq_secondDifference z f N hN hN1]
  exact sum_nonneg fun k hk => mul_nonneg (hf k (mem_range.mp hk))
    (geometricDiagonalCumulative_nonneg hz k)

/-- Strict convexity at the first coefficient leaves mass at every frequency. -/
theorem geometricDiagonal_weighted_pos {z : ℂ} (hz : ‖z‖ = 1)
    (f : ℕ → ℝ) (N : ℕ) (hNpos : 0 < N) (hN : f N = 0) (hN1 : f (N + 1) = 0)
    (hf : ∀ k < N, 0 ≤ f k - 2 * f (k + 1) + f (k + 2))
    (hf0 : 0 < f 0 - 2 * f 1 + f 2) :
    0 < ∑ k ∈ range (N + 1), f k * (geometricDiagonal z k).re := by
  rw [geometricDiagonal_weighted_eq_secondDifference z f N hN hN1]
  apply sum_pos'
  · intro k hk
    exact mul_nonneg (hf k (mem_range.mp hk)) (geometricDiagonalCumulative_nonneg hz k)
  · refine ⟨0, mem_range.mpr hNpos, ?_⟩
    simpa only [Nat.zero_add, geometricDiagonalCumulative, geometricDiagonalPrefix, geometricDiagonal,
      sum_range_one, Complex.one_re, mul_one] using hf0


theorem geometricDiagonal_exp_re (θ : ℝ) (n : ℕ) :
    (geometricDiagonal (Complex.exp ((θ : ℂ) * I)) n).re =
      ∑ j ∈ range (n + 1), Real.cos ((2 * (j : ℝ) - n) * θ) := by
  rw [geometricDiagonal_eq_sum, Complex.re_sum]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.le_of_lt_succ (mem_range.mp hj)
  have hpow (k : ℕ) : Complex.exp ((θ : ℂ) * I) ^ k =
      Complex.exp (((k : ℝ) * θ : ℝ) * I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hconj : conj (Complex.exp ((θ : ℂ) * I)) ^ (n - j) =
      Complex.exp ((-((n - j : ℕ) : ℝ) * θ : ℝ) * I) := by
    rw [← map_pow, hpow, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hpow, hconj, ← Complex.exp_add]
  have hexp : (((j : ℝ) * θ : ℝ) : ℂ) * I +
      ((-((n - j : ℕ) : ℝ) * θ : ℝ) : ℂ) * I =
      (((2 * (j : ℝ) - n) * θ : ℝ) : ℂ) * I := by
    rw [Nat.cast_sub hjn]
    push_cast
    ring
  rw [hexp, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one,
    add_zero, Real.exp_zero, one_mul]

theorem geometricDiagonalCumulative_cos_nonneg (θ : ℝ) (n : ℕ) :
    0 ≤ ∑ k ∈ range (n + 1), ∑ j ∈ range (k + 1),
      ∑ i ∈ range (j + 1), Real.cos ((2 * (i : ℝ) - j) * θ) := by
  have hz : ‖Complex.exp ((θ : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Real.exp_zero]
  simpa only [geometricDiagonalCumulative, geometricDiagonalPrefix,
    geometricDiagonal_exp_re] using geometricDiagonalCumulative_nonneg hz n

end HTGeometry
