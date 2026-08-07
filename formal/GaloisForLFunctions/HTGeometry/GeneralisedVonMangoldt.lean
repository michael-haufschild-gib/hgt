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
open scoped zeta Moebius

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

/-- **The Leibniz rule of the Dirichlet ring.**  Pointwise multiplication by `log` is a derivation:
`L(f * g) = L(f) * g + f * L(g)` for `L f = f·log`.  It holds because `log` is additive on the
antidiagonal, `log n = log a + log b` whenever `a b = n ≠ 0`. -/
theorem pmul_log_mul (f g : ArithmeticFunction ℝ) :
    pmul (f * g) ArithmeticFunction.log
      = pmul f ArithmeticFunction.log * g + f * pmul g ArithmeticFunction.log := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [pmul_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hprod, hn0⟩ := hx
  have ha : (x.1 : ℝ) ≠ 0 := by
    have h : x.1 ≠ 0 := left_ne_zero_of_mul (by rw [hprod]; exact hn0)
    exact_mod_cast h
  have hb : (x.2 : ℝ) ≠ 0 := by
    have h : x.2 ≠ 0 := right_ne_zero_of_mul (by rw [hprod]; exact hn0)
    exact_mod_cast h
  rw [pmul_apply, pmul_apply, ArithmeticFunction.log_apply, ArithmeticFunction.log_apply,
    ← hprod, Nat.cast_mul, Real.log_mul ha hb]
  ring

/-- The generalised von Mangoldt function of the Dirichlet identity vanishes. -/
theorem vonMangoldtOf_one (hf : Invertible ((1 : ArithmeticFunction ℝ) 1)) :
    vonMangoldtOf (1 : ArithmeticFunction ℝ) hf = 0 := by
  refine (eq_vonMangoldtOf_of_mul_eq (1 : ArithmeticFunction ℝ) 0 hf ?_).symm
  rw [mul_zero]
  ext n
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [pmul_apply, hn]

/-- **Additivity of the generalised von Mangoldt weight.**  `Λ_{f*g} = Λ_f + Λ_g`: the weight is the
logarithmic derivative of the Dirichlet ring, so it turns convolution into addition.  With
`vonMangoldtOf_one` this says that `f ↦ Λ_f` is a homomorphism from the units of the Dirichlet ring to
the additive group of arithmetic functions. -/
theorem vonMangoldtOf_mul (f g : ArithmeticFunction ℝ) (hf : Invertible (f 1))
    (hg : Invertible (g 1)) (hfg : Invertible ((f * g) 1)) :
    vonMangoldtOf (f * g) hfg = vonMangoldtOf f hf + vonMangoldtOf g hg := by
  have hL := pmul_log_mul f g
  rw [pmul_log_eq_mul_vonMangoldtOf f hf, pmul_log_eq_mul_vonMangoldtOf g hg] at hL
  refine (eq_vonMangoldtOf_of_mul_eq (f * g) _ hfg ?_).symm
  rw [hL]
  ring

/-- **The Möbius instance.**  `μ·log = μ * (−Λ)`: the generalised von Mangoldt function of the Möbius
function is `−Λ`.  Equivalently `∑_{d ∣ n} μ(d) log d = −Λ(n)`, transported across `μ * ζ = 1`. -/
theorem pmul_moebius_log :
    pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log = μ * (-Λ) := by
  have hzeta : (ζ : ArithmeticFunction ℝ) * pmul (μ : ArithmeticFunction ℝ)
      ArithmeticFunction.log = -Λ := by
    ext n
    rw [coe_zeta_mul_apply, ArithmeticFunction.neg_apply]
    have hterm : ∀ i ∈ n.divisors,
        (pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log) i
          = ((μ i : ℤ) : ℝ) * ArithmeticFunction.log i := by
      intro i _
      rw [pmul_apply, intCoe_apply]
    rw [Finset.sum_congr rfl hterm]
    exact sum_moebius_mul_log_eq
  have hmul := congrArg (fun h : ArithmeticFunction ℝ => (μ : ArithmeticFunction ℝ) * h) hzeta
  rw [← mul_assoc, coe_moebius_mul_coe_zeta, one_mul] at hmul
  exact hmul

/-- The generalised von Mangoldt function of the Möbius function. -/
theorem vonMangoldtOf_moebius (hf : Invertible ((μ : ArithmeticFunction ℝ) 1)) :
    vonMangoldtOf (μ : ArithmeticFunction ℝ) hf = -Λ :=
  (eq_vonMangoldtOf_of_mul_eq (μ : ArithmeticFunction ℝ) (-Λ) hf pmul_moebius_log.symm).symm

end GaloisForLFunctions.HTGeometry
