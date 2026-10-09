import GaloisForLFunctions.HTGeometry.PaperPrimeFlowCoefficients

/-!
# Exact support classification of native prime termination

An arithmetic function is killed by the mth prime derivative exactly when
it vanishes on multiples of the mth prime power. Equivalently every nonzero
coefficient has prime valuation below m. This classifies the entire maximal
terminating core, allowing infinitely many other active primes.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The rising-factorial multiplier never hides a coefficient on a prime-multiple ray. -/
theorem paperPrimeArithmetic_iterate_eq_zero_iff_multiples (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    (primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f = 0 ↔
      ∀ n : ℕ, f (n * (p : ℕ) ^ m) = 0 := by
  constructor
  · intro h n
    have he := congrArg (fun g : ArithmeticFunction ℂ => g n) h
    rw [paperPrimeArithmetic_iterate_apply, ArithmeticFunction.zero_apply] at he
    have hw : (((n.factorization (p : ℕ) + 1).ascFactorial m : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.ascFactorial_pos _ _))
    exact (mul_eq_zero.mp he).resolve_left hw
  · intro h
    ext n
    rw [paperPrimeArithmetic_iterate_apply, h n, mul_zero, ArithmeticFunction.zero_apply]

/-- Exact annihilation order is equivalent to vanishing on a principal divisibility set. -/
theorem paperPrimeArithmetic_iterate_eq_zero_iff_dvd (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    (primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f = 0 ↔
      ∀ n : ℕ, (p : ℕ) ^ m ∣ n → f n = 0 := by
  rw [paperPrimeArithmetic_iterate_eq_zero_iff_multiples]
  constructor
  · intro h n hn
    obtain ⟨a, rfl⟩ := hn
    simpa only [mul_comm] using h a
  · intro h n
    exact h (n * (p : ℕ) ^ m) ⟨n, mul_comm _ _⟩

/-- The complete support boundary, including the zero function and order zero. -/
theorem paperPrimeArithmetic_iterate_eq_zero_iff_support (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    (primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f = 0 ↔
      ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [paperPrimeArithmetic_iterate_eq_zero_iff_dvd]
  constructor
  · intro h n hf
    have hn : n ≠ 0 := by
      rintro rfl
      exact hf (by simp)
    by_contra hm
    apply hf
    exact h n ((p.property.pow_dvd_iff_le_factorization hn).mpr (by omega))
  · intro h n hdiv
    by_contra hf
    have hn : n ≠ 0 := by
      rintro rfl
      exact hf (by simp)
    have hle := (p.property.pow_dvd_iff_le_factorization hn).mp hdiv
    have hlt := h n hf
    omega

/-- The native prime constants are precisely functions vanishing on multiples of that prime. -/
theorem paperPrimeArithmetic_kernel_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    primeArithmeticDerivation (p : ℕ) p.property f = 0 ↔
      ∀ n : ℕ, (p : ℕ) ∣ n → f n = 0 := by
  simpa using paperPrimeArithmetic_iterate_eq_zero_iff_dvd p f 1

/-- The maximal terminating core is exactly bounded prime exponent in the nonzero support. -/
theorem paperPrimeTerminatingCore_support_iff (p : Nat.Primes) (f : ArithmeticFunction ℂ) :
    f ∈ paperTerminatingCore (primeArithmeticDerivation (p : ℕ) p.property) ↔
      ∃ m : ℕ, ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [paperTerminatingCore_mem_iff]
  simp only [paperPrimeArithmetic_iterate_eq_zero_iff_support]

/-- The same support bound determines exactly whether a global formal orbit is polynomial. -/
theorem paperArithmeticPrimeFormalFlow_polynomial_support_iff (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) :
    (∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticPrimeFormalFlow p f = (P : PowerSeries (ArithmeticFunction ℂ))) ↔
      ∃ m : ℕ, ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [paperArithmeticPrimeFormalFlow, paperFormalExponential_polynomial_iff]
  simp only [paperPrimeArithmetic_iterate_eq_zero_iff_support]

/-- At each prescribed truncation order, the support test is necessary and sufficient. -/
theorem paperArithmeticPrimeFormalFlow_trunc_support_iff (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    paperArithmeticPrimeFormalFlow p f =
        (PowerSeries.trunc m (paperArithmeticPrimeFormalFlow p f) :
          PowerSeries (ArithmeticFunction ℂ)) ↔
      ∀ n : ℕ, f n ≠ 0 → n.factorization (p : ℕ) < m := by
  rw [paperArithmeticPrimeFormalFlow, paperFormalExponential_trunc_iff,
    paperPrimeArithmetic_iterate_eq_zero_iff_support]

end

end GaloisForLFunctions.HTGeometry
