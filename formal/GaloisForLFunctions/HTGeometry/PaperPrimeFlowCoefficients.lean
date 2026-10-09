import GaloisForLFunctions.HTGeometry.PaperArithmeticFormalFlows
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The exact native prime-flow binomial transform

Repeated prime differentiation reads coefficients at successive prime
multiples with a rising-factorial weight. Dividing by the time factorial
gives the complete formal-flow coefficients, including the index-zero case.
The native zeta sequence supplies an explicit nonpolynomial formal orbit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every native prime-derivative iterate is an exact shifted coefficient readout. -/
theorem paperPrimeArithmetic_iterate_apply (p : Nat.Primes) (f : ArithmeticFunction ℂ)
    (n m : ℕ) :
    ((primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f) n =
      (((n.factorization (p : ℕ) + 1).ascFactorial m : ℕ) : ℂ) *
        f (n * (p : ℕ) ^ m) := by
  by_cases hn : n = 0
  · subst n
    simp
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, primeArithmeticDerivation_apply, primeDeriv_apply]
      have hindex : n * (p : ℕ) ^ m * (p : ℕ) = n * (p : ℕ) ^ (m + 1) := by
        rw [pow_succ, mul_assoc]
      rw [hindex]
      have hval : (n * (p : ℕ) ^ (m + 1)).factorization (p : ℕ) =
          n.factorization (p : ℕ) + (m + 1) := by
        rw [Nat.factorization_mul hn (pow_ne_zero _ p.property.ne_zero), Finsupp.add_apply,
          Nat.factorization_pow_self p.property]
      rw [hval, Nat.ascFactorial_succ]
      push_cast
      ring

/-- The full formal prime flow is the binomial transform along every prime-multiple ray. -/
theorem paperArithmeticPrimeFormalFlow_coeff (p : Nat.Primes) (f : ArithmeticFunction ℂ)
    (n m : ℕ) :
    PowerSeries.coeff m (paperArithmeticPrimeFormalFlow p f) n =
      (((n.factorization (p : ℕ) + m).choose m : ℕ) : ℂ) *
        f (n * (p : ℕ) ^ m) := by
  rw [paperArithmeticPrimeFormalFlow, paperFormalExponential_coeff,
    ArithmeticFunction.smul_map, paperPrimeArithmetic_iterate_apply,
    Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_eq_mul]
  have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  simp only [← mul_assoc, inv_mul_cancel₀ hm, one_mul]

/-- At the convolution identity, the formal orbit reads every pure prime-power coefficient. -/
theorem paperArithmeticPrimeFormalFlow_coeff_one (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (m : ℕ) :
    PowerSeries.coeff m (paperArithmeticPrimeFormalFlow p f) 1 = f ((p : ℕ) ^ m) := by
  simp [paperArithmeticPrimeFormalFlow_coeff]

/-- Zeta's derivative tower has the exact factorial witness at the convolution identity. -/
theorem paperPrimeArithmetic_iterate_zeta_one (p : Nat.Primes) (m : ℕ) :
    ((primeArithmeticDerivation (p : ℕ) p.property :
        ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m]
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) 1 = (m.factorial : ℂ) := by
  simp [paperPrimeArithmetic_iterate_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, p.property.ne_zero]

/-- The native zeta coefficient sequence has explicit binomial formal time coefficients. -/
theorem paperArithmeticPrimeFormalFlow_zeta_coeff (p : Nat.Primes) (n m : ℕ) :
    PowerSeries.coeff m
        (paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n =
      if n = 0 then 0 else (((n.factorization (p : ℕ) + m).choose m : ℕ) : ℂ) := by
  rw [paperArithmeticPrimeFormalFlow_coeff]
  by_cases hn : n = 0
  · simp [hn]
  · simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hn,
      mul_ne_zero hn (pow_ne_zero _ p.property.ne_zero)]

/-- Every formal time coefficient of zeta is nonzero already at the identity index. -/
theorem paperArithmeticPrimeFormalFlow_zeta_coeff_one (p : Nat.Primes) (m : ℕ) :
    PowerSeries.coeff m
        (paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) 1 =
      1 := by
  simp [paperArithmeticPrimeFormalFlow_zeta_coeff]

/-- Zeta is an explicit input whose global prime orbit cannot be polynomial. -/
theorem paperArithmeticPrimeFormalFlow_zeta_not_polynomial (p : Nat.Primes) :
    ¬ ∃ P : Polynomial (ArithmeticFunction ℂ),
      paperArithmeticPrimeFormalFlow p (ArithmeticFunction.zeta : ArithmeticFunction ℂ) =
        (P : PowerSeries (ArithmeticFunction ℂ)) := by
  rintro ⟨P, h⟩
  have hc := congrArg
    (fun F : PowerSeries (ArithmeticFunction ℂ) => PowerSeries.coeff (P.natDegree + 1) F 1) h
  have hz : P.coeff (P.natDegree + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  simp only [paperArithmeticPrimeFormalFlow_zeta_coeff_one, Polynomial.coeff_coe,
    hz, ArithmeticFunction.zero_apply] at hc
  exact one_ne_zero hc

end

end GaloisForLFunctions.HTGeometry
