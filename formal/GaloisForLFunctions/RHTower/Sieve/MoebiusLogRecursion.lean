import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.DirichletLogDerivation

/-!
# The Möbius log recursion

The Möbius function is multiplicative but not completely multiplicative, so the recursion for a
completely multiplicative `f` does not apply to it.  What replaces it is the identity

`μ·log = -(Λ * μ)`,

obtained by applying the logarithmic derivation to `μ * ζ = 1`: the derivation kills the identity
element, `ζ·log = log`, and `μ * log = Λ`, so `(μ·log) * ζ = -Λ` and multiplying by `μ` finishes.

Summed against the divisor swap this gives

`∑_{m ≤ N} μ(m) log m = -∑_{d ≤ N} Λ(d) ∑_{k ≤ N/d} μ(k)`,

expressing the log-weighted Möbius sum through the Mertens function on the shorter ranges `N/d`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- The logarithmic derivation kills the convolution identity. -/
theorem one_pmul_log : (1 : ArithmeticFunction ℝ).pmul ArithmeticFunction.log = 0 := by
  ext n
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · simp [hn]

/-- **The Möbius log identity**: `μ·log = -(Λ * μ)`. -/
theorem moebius_pmul_log :
    (((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log
      = -(vonMangoldt * ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) := by
  set μR := ((moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) with hμR
  set ζR := ((zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) with hζR
  have hζμ : ζR * μR = 1 := coe_zeta_mul_coe_moebius
  have hμζ : μR * ζR = 1 := by rw [mul_comm]; exact hζμ
  have h1 : (μR * ζR).pmul ArithmeticFunction.log
      = (μR.pmul ArithmeticFunction.log) * ζR + μR * (ζR.pmul ArithmeticFunction.log) :=
    RHTower.pmul_log_mul μR ζR
  rw [hμζ, one_pmul_log, RHTower.zeta_pmul_log] at h1
  have h2 : μR * ArithmeticFunction.log = vonMangoldt := by
    calc μR * ArithmeticFunction.log = μR * (vonMangoldt * ζR) := by rw [vonMangoldt_mul_zeta]
      _ = vonMangoldt * (μR * ζR) := by ring
      _ = vonMangoldt := by rw [hμζ, mul_one]
  rw [h2] at h1
  have h3 : (μR.pmul ArithmeticFunction.log) * ζR = -vonMangoldt := by linear_combination -h1
  calc μR.pmul ArithmeticFunction.log
      = (μR.pmul ArithmeticFunction.log) * (ζR * μR) := by rw [hζμ, mul_one]
    _ = ((μR.pmul ArithmeticFunction.log) * ζR) * μR := by ring
    _ = -vonMangoldt * μR := by rw [h3]
    _ = -(vonMangoldt * μR) := by ring

/-- **The Möbius log identity, pointwise.** -/
theorem moebius_mul_log_apply (n : ℕ) :
    ((moebius n : ℤ) : ℝ) * Real.log n
      = -∑ d ∈ n.divisors, vonMangoldt d * ((moebius (n / d) : ℤ) : ℝ) := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) moebius_pmul_log
  simp only [pmul_apply, intCoe_apply, log_apply, ArithmeticFunction.neg_apply, mul_apply] at h
  rw [h, Nat.sum_divisorsAntidiagonal
    (f := fun a b => vonMangoldt a * ((moebius b : ℤ) : ℝ))]

/-- **The Möbius log recursion.** -/
theorem sum_moebius_mul_log_eq (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ) * Real.log m
      = -∑ d ∈ Finset.Icc 1 N,
          vonMangoldt d * ∑ k ∈ Finset.Icc 1 (N / d), ((moebius k : ℤ) : ℝ) := by
  calc ∑ m ∈ Finset.Icc 1 N, ((moebius m : ℤ) : ℝ) * Real.log m
      = ∑ m ∈ Finset.Icc 1 N,
          -∑ d ∈ m.divisors, vonMangoldt d * ((moebius (m / d) : ℤ) : ℝ) :=
        Finset.sum_congr rfl fun m _ => moebius_mul_log_apply m
    _ = -∑ m ∈ Finset.Icc 1 N,
          ∑ d ∈ m.divisors, vonMangoldt d * ((moebius (m / d) : ℤ) : ℝ) := by
        rw [Finset.sum_neg_distrib]
    _ = -∑ d ∈ Finset.Icc 1 N,
          ∑ k ∈ Finset.Icc 1 (N / d), vonMangoldt d * ((moebius k : ℤ) : ℝ) := by
        rw [sum_divisors_swap N fun d k => vonMangoldt d * ((moebius k : ℤ) : ℝ)]
    _ = -∑ d ∈ Finset.Icc 1 N,
          vonMangoldt d * ∑ k ∈ Finset.Icc 1 (N / d), ((moebius k : ℤ) : ℝ) := by
        refine congrArg Neg.neg (Finset.sum_congr rfl fun d _ => ?_)
        rw [Finset.mul_sum]

end RHTower.Sieve
