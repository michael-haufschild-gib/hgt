import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Exact convolution class of the Route E empty Walsh grade

The primewise totient weight left by the hard-core Radon amplifier is not an
independent arithmetic source. Its literal Möbius coefficient is the Dirichlet
convolution of Möbius with the reciprocal radical function. This is a finite,
unconditional identity; no RH-scale summatory estimate follows here.
-/

open ArithmeticFunction

namespace RHTower

noncomputable section

/-- The local totient ratio as a multiplicative arithmetic function. -/
def routeEHardCoreTotientRatioArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => 1 - (p : ℝ)⁻¹)

/-- The tame local convolution factor: value `1/p` at every positive prime power. -/
def routeEHardCoreRadicalReciprocalArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => (p : ℝ)⁻¹)

/-- Möbius times the primewise totient ratio, including zero at index zero. -/
def routeEHardCoreTotientMobiusArithmetic : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    routeEHardCoreTotientRatioArithmetic

private theorem ratio_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    routeEHardCoreTotientRatioArithmetic (p ^ k) = 1 - (p : ℝ)⁻¹ := by
  simp [routeEHardCoreTotientRatioArithmetic,
    ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk hp]

/-- The reciprocal-radical factor has constant value along each prime ray. -/
theorem routeEHardCoreRadicalReciprocalArithmetic_prime_pow
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    routeEHardCoreRadicalReciprocalArithmetic (p ^ k) = (p : ℝ)⁻¹ := by
  simp [routeEHardCoreRadicalReciprocalArithmetic,
    ArithmeticFunction.prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero),
    Nat.primeFactors_prime_pow hk hp]

private theorem weighted_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    routeEHardCoreTotientMobiusArithmetic (p ^ k) =
      if k = 1 then -(1 - (p : ℝ)⁻¹) else 0 := by
  rw [routeEHardCoreTotientMobiusArithmetic, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime_pow hp hk, ratio_prime_pow hp hk]
  split_ifs <;> simp

private theorem weighted_one : routeEHardCoreTotientMobiusArithmetic 1 = 1 := by
  simp [routeEHardCoreTotientMobiusArithmetic,
    routeEHardCoreTotientRatioArithmetic,
    ArithmeticFunction.pmul_apply,
    ArithmeticFunction.prodPrimeFactors_apply]

private theorem sum_weighted_prime_pow (p i : ℕ) (hp : p.Prime) :
    (∑ j ∈ Finset.range (i + 1),
      routeEHardCoreTotientMobiusArithmetic (p ^ j)) =
        if i = 0 then 1 else (p : ℝ)⁻¹ := by
  induction i with
  | zero => simp [weighted_one]
  | succ i ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hi : i = 0
    · subst i
      rw [weighted_prime_pow hp (by omega)]
      simp
    · have hik : i + 1 ≠ 0 := by omega
      have hik1 : i + 1 ≠ 1 := by omega
      rw [weighted_prime_pow hp hik, if_neg hik1]
      simp [hi]

private theorem weighted_mul_zeta_eq_radicalReciprocal :
    (routeEHardCoreTotientMobiusArithmetic *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
      routeEHardCoreRadicalReciprocalArithmetic := by
  have hmultb : routeEHardCoreTotientMobiusArithmetic.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors _)
  have hmultg : routeEHardCoreRadicalReciprocalArithmetic.IsMultiplicative :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hmultz : (ArithmeticFunction.zeta : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    _ (hmultb.mul hmultz) _ hmultg).2
  intro p i hp
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    sum_weighted_prime_pow p i hp]
  by_cases hi : i = 0
  · subst i
    simp [routeEHardCoreRadicalReciprocalArithmetic]
  · rw [if_neg hi, routeEHardCoreRadicalReciprocalArithmetic_prime_pow hp hi]

/-- Closed Dirichlet convolution identity for the literal totient-weighted
Möbius source selected by the empty Walsh grade. -/
theorem routeEHardCoreTotientMobiusArithmetic_eq_moebius_mul_radicalReciprocal :
    routeEHardCoreTotientMobiusArithmetic =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        routeEHardCoreRadicalReciprocalArithmetic := by
  have h := congrArg
    (fun f : ArithmeticFunction ℝ =>
      f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ))
    weighted_mul_zeta_eq_radicalReciprocal
  rw [mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius,
    mul_one, mul_comm] at h
  exact h

/-- Euler's totient formula identifies the local ratio exactly. -/
theorem routeEHardCoreTotientRatioArithmetic_eq_div
    (n : ℕ) (hn : n ≠ 0) :
    routeEHardCoreTotientRatioArithmetic n =
      (n.totient : ℝ) / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have ht : (n.totient : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (fun q : ℚ => (q : ℝ))
      (Nat.totient_eq_mul_prod_factors n)
  rw [routeEHardCoreTotientRatioArithmetic,
    ArithmeticFunction.prodPrimeFactors_apply hn, ht]
  field_simp

/-- The arithmetic function is the claimed integer-indexed source. -/
theorem routeEHardCoreTotientMobiusArithmetic_apply
    (n : ℕ) (hn : n ≠ 0) :
    routeEHardCoreTotientMobiusArithmetic n =
      ((ArithmeticFunction.moebius n : ℤ) : ℝ) *
        (n.totient : ℝ) / (n : ℝ) := by
  rw [routeEHardCoreTotientMobiusArithmetic,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply,
    routeEHardCoreTotientRatioArithmetic_eq_div n hn]
  ring

end
end RHTower
