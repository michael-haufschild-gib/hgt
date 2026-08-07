import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The generalised von Mangoldt function of an arithmetic function

Halász's theorem is proved by iterating the identity `f·log = f * Λ_f`, where `Λ_f` is the unique
arithmetic function satisfying it.  When `f 1` is invertible the Dirichlet inverse exists, so `Λ_f` is
simply `f⁻¹ * (f·log)`, and the identity is associativity.

For the classical `f = 1` this is `Λ` itself, since `log = ζ * Λ`.  The point of the general version is
that the recursion it supports never forms a Dirichlet polynomial and never uses a mean-value theorem, so
it avoids the regime obstruction of the contour route.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction

/-- The generalised von Mangoldt function of `f`: the unique solution of `f·log = f * Λ_f`. -/
noncomputable def vonMangoldtOf (f : ArithmeticFunction ℝ) (hf : Invertible (f 1)) :
    ArithmeticFunction ℝ :=
  dirichletInverse f hf * pmul f ArithmeticFunction.log

/-- **The defining identity.**  `f·log = f * Λ_f`. -/
theorem pmul_log_eq_mul_vonMangoldtOf (f : ArithmeticFunction ℝ) (hf : Invertible (f 1)) :
    pmul f ArithmeticFunction.log = f * vonMangoldtOf f hf := by
  rw [vonMangoldtOf, ← mul_assoc, self_mul_dirichletInverse, one_mul]

/-- **Uniqueness.**  Any solution of the defining identity is the generalised von Mangoldt
function. -/
theorem eq_vonMangoldtOf_of_mul_eq (f g : ArithmeticFunction ℝ) (hf : Invertible (f 1))
    (hg : f * g = pmul f ArithmeticFunction.log) :
    g = vonMangoldtOf f hf := by
  have h := congrArg (fun h : ArithmeticFunction ℝ => dirichletInverse f hf * h) hg
  rw [← mul_assoc, dirichletInverse_mul_self, one_mul] at h
  rw [h, vonMangoldtOf]

/-- The classical case: for the zeta function the generalised von Mangoldt function is `Λ`. -/
theorem vonMangoldtOf_zeta
    (hf : Invertible (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) 1)) :
    vonMangoldtOf ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ) hf = Λ := by
  refine (eq_vonMangoldtOf_of_mul_eq _ Λ hf ?_).symm
  rw [zeta_mul_vonMangoldt]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simp [pmul, ArithmeticFunction.zeta_apply, hn.ne']

/-- **For a completely multiplicative `f` the generalised von Mangoldt function is `f·Λ`.**  Every
antidiagonal term collapses, `f a · (f b Λ b) = f (ab) Λ b = f n Λ b`, and `∑_{b ∣ n} Λ b = log n`. -/
theorem pmul_log_eq_mul_pmul_vonMangoldt (f : ArithmeticFunction ℝ)
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) :
    pmul f ArithmeticFunction.log = f * pmul f Λ := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, pmul_apply, ArithmeticFunction.log_apply]
  have hterm : ∀ x ∈ n.divisorsAntidiagonal, f x.1 * (pmul f Λ) x.2 = f n * Λ x.2 := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    rw [pmul_apply, ← mul_assoc, ← hf, hx.1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hdiv : (∑ x ∈ n.divisorsAntidiagonal, Λ x.2) = ∑ i ∈ n.divisors, Λ i :=
    Nat.sum_divisorsAntidiagonal' (fun _ b => Λ b)
  rw [hdiv, vonMangoldt_sum]

/-- The generalised von Mangoldt function of a completely multiplicative `f`. -/
theorem vonMangoldtOf_eq_pmul_vonMangoldt (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) :
    vonMangoldtOf f hf1 = pmul f Λ :=
  (eq_vonMangoldtOf_of_mul_eq f (pmul f Λ) hf1 (pmul_log_eq_mul_pmul_vonMangoldt f hf).symm).symm

/-- **The weight of the recursion is dominated by `Λ`.**  For a bounded completely multiplicative `f`
the generalised von Mangoldt function is supported on prime powers with mass at most `log p`. -/
theorem abs_vonMangoldtOf_le_vonMangoldt (f : ArithmeticFunction ℝ) (hf1 : Invertible (f 1))
    (hf : ∀ m n : ℕ, f (m * n) = f m * f n) (hbdd : ∀ n : ℕ, |f n| ≤ 1) (n : ℕ) :
    |vonMangoldtOf f hf1 n| ≤ Λ n := by
  have h0 : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
  rw [vonMangoldtOf_eq_pmul_vonMangoldt f hf1 hf, pmul_apply, abs_mul, abs_of_nonneg h0]
  calc |f n| * Λ n ≤ 1 * Λ n := mul_le_mul_of_nonneg_right (hbdd n) h0
    _ = Λ n := one_mul _

end GaloisForLFunctions.HTGeometry
