/-
The partial-summation bridge used in Bourgain's critical-line zeta estimate.

Section 4 of Bourgain's proof first bounds unweighted logarithmic exponential
sums and then inserts the critical weight `n⁻¹ᐟ²` by partial summation.  This
module closes that step without an analytic integral: finite Abel summation and
monotonicity show that a uniform bound `B` for every partial phase sum on
`(a,b]` gives

  ‖∑_{a<n≤b} n⁻¹ᐟ² F(n)‖ ≤ B (a+1)⁻¹ᐟ².

The final theorem specializes `F(n)` to `n⁻ⁱᵗ` and rewrites the weighted term
as the exact Dirichlet monomial `n⁻¹ᐟ²⁻ⁱᵗ`.
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Complex

namespace RHTower

/-- Finite Abel summation on `(a,b]`, with the endpoint weight placed at
`b+1`. This form makes the monotone-weight estimate telescope exactly. -/
theorem sum_Ioc_weight_mul_eq
    (F w : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, w n * F n =
      w (b + 1) * (∑ n ∈ Finset.Ioc a b, F n)
        + ∑ n ∈ Finset.Ioc a b,
            (w n - w (n + 1)) * (∑ k ∈ Finset.Ioc a n, F k) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | @succ b hab ih =>
      rw [Finset.sum_Ioc_succ_top hab (fun n => w n * F n)]
      rw [Finset.sum_Ioc_succ_top hab F]
      rw [Finset.sum_Ioc_succ_top hab
        (fun n => (w n - w (n + 1)) * (∑ k ∈ Finset.Ioc a n, F k))]
      rw [Finset.sum_Ioc_succ_top hab F]
      rw [ih]
      ring

/-- Forward differences telescope on `(a,b]`. -/
theorem sum_Ioc_sub_succ (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, (w n - w (n + 1)) = w (a + 1) - w (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp
  | @succ b hab ih =>
      rw [Finset.sum_Ioc_succ_top hab, ih]
      ring

/-- Abel's inequality for a nonnegative weight decreasing at each index in
`(a,b]`. A uniform bound for the unweighted partial sums loses exactly the
left endpoint weight. -/
theorem norm_sum_Ioc_weight_mul_le
    (F : ℕ → ℂ) (w : ℕ → ℝ) {a b : ℕ} (hab : a < b)
    (hw_nonneg : ∀ n, 0 ≤ w n)
    (hw_step : ∀ n ∈ Finset.Ioc a b, w (n + 1) ≤ w n)
    {B : ℝ}
    (hpartial : ∀ n ∈ Finset.Ioc a b, ‖∑ k ∈ Finset.Ioc a n, F k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc a b, (w n : ℂ) * F n‖ ≤ B * w (a + 1) := by
  rw [sum_Ioc_weight_mul_eq F (fun n => (w n : ℂ)) hab.le]
  calc
    ‖(w (b + 1) : ℂ) * (∑ n ∈ Finset.Ioc a b, F n)
          + ∑ n ∈ Finset.Ioc a b,
              ((w n : ℂ) - (w (n + 1) : ℂ)) * (∑ k ∈ Finset.Ioc a n, F k)‖
        ≤ ‖(w (b + 1) : ℂ) * (∑ n ∈ Finset.Ioc a b, F n)‖
          + ∑ n ∈ Finset.Ioc a b,
              ‖((w n : ℂ) - (w (n + 1) : ℂ)) * (∑ k ∈ Finset.Ioc a n, F k)‖ := by
            exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w (b + 1) * B
          + ∑ n ∈ Finset.Ioc a b, (w n - w (n + 1)) * B := by
      gcongr with n hn
      · simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw_nonneg (b + 1))]
          using mul_le_mul_of_nonneg_left
            (hpartial b (Finset.mem_Ioc.mpr ⟨hab, le_rfl⟩)) (hw_nonneg (b + 1))
      · have hdiff : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw_step n hn)
        simpa [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hdiff]
          using mul_le_mul_of_nonneg_left (hpartial n hn) hdiff
    _ = B * w (a + 1) := by
      rw [← Finset.sum_mul, sum_Ioc_sub_succ w hab.le]
      ring

/-- Critical square-root specialization of finite Abel summation. -/
theorem norm_sum_Ioc_invSqrt_mul_le
    (F : ℕ → ℂ) {a b : ℕ} (hab : a < b) {B : ℝ}
    (hpartial : ∀ n ∈ Finset.Ioc a b, ‖∑ k ∈ Finset.Ioc a n, F k‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc a b, (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * F n‖
      ≤ B * ((a + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  apply norm_sum_Ioc_weight_mul_le F
    (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) hab
  · exact fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  · intro n hn
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    · exact_mod_cast Nat.le_succ n
    · norm_num
  · exact hpartial

/-- Exact factorization of the critical-line Dirichlet monomial into its
square-root weight and unitary logarithmic phase. -/
theorem natCast_cpow_neg_half_sub_I_mul
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ)) =
      (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        * (n : ℂ) ^ (-Complex.I * (t : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show -(1 / 2 : ℂ) - Complex.I * (t : ℂ) =
      (-(1 / 2 : ℝ) : ℂ) + (-Complex.I * (t : ℂ)) by push_cast; ring]
  rw [Complex.cpow_add _ _ hn0]
  congr 1
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  norm_num

/-- **Bourgain partial-summation bridge.** Uniform control of every
unweighted logarithmic phase sum on `(a,b]` gives the corresponding bound for
the exact critical-line Dirichlet block. No analytic or number-theoretic
hypothesis is hidden in the proof. -/
theorem norm_sum_Ioc_critical_cpow_le
    {a b : ℕ} (hab : a < b) (t : ℝ) {B : ℝ}
    (hpartial : ∀ n ∈ Finset.Ioc a b,
      ‖∑ k ∈ Finset.Ioc a n, (k : ℂ) ^ (-Complex.I * (t : ℂ))‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc a b, (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * (t : ℂ))‖
      ≤ B * ((a + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [Finset.sum_congr rfl fun n hn => natCast_cpow_neg_half_sub_I_mul n
    (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1) t]
  exact norm_sum_Ioc_invSqrt_mul_le
    (fun n => (n : ℂ) ^ (-Complex.I * (t : ℂ))) hab hpartial

end RHTower
