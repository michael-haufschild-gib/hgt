import GaloisForLFunctions.RHTower.EulerGammaCoPoissonDividedLogJetWeld
import GaloisForLFunctions.RHTower.MobiusPrimeRenewalDefectBoundary

/-!
# Route E boundary as a primitive Gamma/co-Poisson prime-power current

The zero/one-large-prime boundary uses the prime tail

`sum_{p > z} A_z(px)`.

The Gamma/co-Poisson normal current instead naturally carries every prime
power with divided-log coefficient

`Λ(p^k) / log(p^k) = 1 / k`.

This file proves the exact finite bridge.  The primitive Gamma/co-Poisson
term is the confluence jet divided by one additional logarithmic action;
on a prime power it is exactly the negative divided-log Dirichlet monomial.
The corresponding physical renewal defect is the old prime defect minus
the higher-prime-power tail.  The same identity is retained before
scalarization by the finite small-prime parity partition.

No critical estimate or RH assumption occurs here.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Divided-log von Mangoldt coefficient.  It is `1 / k` at `p^k`. -/
def dividedVonMangoldtCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) /
    (Real.log (n : ℝ) : ℂ)

/-- Exact prime-power value of the divided-log current. -/
theorem dividedVonMangoldtCoefficient_prime_pow
    {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    dividedVonMangoldtCoefficient (p ^ k) = (k : ℂ)⁻¹ := by
  have hpLog : Real.log (p : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have hpLogC : (Real.log (p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpLog
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [dividedVonMangoldtCoefficient,
    ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [show Real.log ((p ^ k : ℕ) : ℝ) =
      (k : ℝ) * Real.log (p : ℝ) by
    simpa only [Nat.cast_pow] using Real.log_pow (p : ℝ) k]
  rw [Complex.ofReal_mul]
  change (Real.log (p : ℝ) : ℂ) /
      ((k : ℂ) * (Real.log (p : ℝ) : ℂ)) = (k : ℂ)⁻¹
  field_simp [hpLogC, hkC]

/-- Gamma/co-Poisson confluence current with one further logarithmic
primitive. -/
def eulerGammaCoPoissonPrimitiveTerm (n : ℕ) (s : ℂ) : ℂ :=
  eulerGammaCoPoissonJetTerm 0 n s /
    (Real.log (n : ℝ) : ℂ)

/-- The primitive confluence term is the divided-log von Mangoldt
Dirichlet monomial, with the sign fixed by the interval orientation. -/
theorem eulerGammaCoPoissonPrimitiveTerm_eq
    {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    eulerGammaCoPoissonPrimitiveTerm n s =
      -dividedVonMangoldtCoefficient n *
        LSeries.term (fun _ => (1 : ℂ)) s n := by
  rw [eulerGammaCoPoissonPrimitiveTerm,
    eulerGammaCoPoissonJetTerm_eq_LSeries_term]
  simp only [Nat.cast_zero, zero_add, pow_one, div_one,
    Function.iterate_zero_apply]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [dividedVonMangoldtCoefficient]
  ring

/-- At a prime power the primitive Gamma/co-Poisson term is exactly the
negative `1 / k` monomial. -/
theorem eulerGammaCoPoissonPrimitiveTerm_prime_pow
    {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) (s : ℂ) :
    eulerGammaCoPoissonPrimitiveTerm (p ^ k) s =
      -(k : ℂ)⁻¹ * LSeries.term (fun _ => (1 : ℂ)) s (p ^ k) := by
  rw [eulerGammaCoPoissonPrimitiveTerm_eq (pow_ne_zero k hp.ne_zero) s,
    dividedVonMangoldtCoefficient_prime_pow hp hk]

/-- Finite all-prime condensation of the primitive term, retaining every
prime-power and exponent label. -/
theorem finite_sum_neg_eulerGammaCoPoissonPrimitiveTerm_prime_pow
    (Q : Finset ℕ) (K : ℕ) (s : ℂ)
    (hQ : ∀ q ∈ Q, Nat.Prime q) :
    (∑ q ∈ Q, ∑ j ∈ Finset.range K,
        -eulerGammaCoPoissonPrimitiveTerm (q ^ (j + 1)) s) =
      ∑ q ∈ Q, ∑ j ∈ Finset.range K,
        ((j + 1 : ℕ) : ℂ)⁻¹ *
          LSeries.term (fun _ => (1 : ℂ)) s (q ^ (j + 1)) := by
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro j _hj
  rw [eulerGammaCoPoissonPrimitiveTerm_prime_pow
    (hQ q hq) (Nat.succ_ne_zero j) s]
  ring

/-- Higher-prime-power part of the finite divided-log physical current. -/
def finiteDividedLogHigherPrimePowerTail
    (Q : Finset ℕ) (K : ℕ) (t : ℂ) : ℂ :=
  ∑ q ∈ Q, ∑ j ∈ Finset.range K,
    ((j + 2 : ℕ) : ℂ)⁻¹ *
      Complex.exp (-((q ^ (j + 2) : ℕ) : ℂ) * t)

/-- Finite physical prime-power renewal: grade one plus all selected
higher grades. -/
def finiteDividedLogPrimePowerRenewal
    (Q : Finset ℕ) (K : ℕ) (t : ℂ) : ℂ :=
  ∑ q ∈ Q, (Complex.exp (-(q : ℂ) * t) +
    ∑ j ∈ Finset.range K,
      ((j + 2 : ℕ) : ℂ)⁻¹ *
        Complex.exp (-((q ^ (j + 2) : ℕ) : ℂ) * t))

/-- One base exponential minus the divided-log prime-power renewal. -/
def finiteDividedLogPrimePowerRenewalDefect
    (Q : Finset ℕ) (K : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (-t) - finiteDividedLogPrimePowerRenewal Q K t

/-- The completed current is the prime current plus its higher-power tail. -/
theorem finiteDividedLogPrimePowerRenewal_eq_prime_add_higher
    (Q : Finset ℕ) (K : ℕ) (t : ℂ) :
    finiteDividedLogPrimePowerRenewal Q K t =
      (∑ q ∈ Q, Complex.exp (-(q : ℂ) * t)) +
        finiteDividedLogHigherPrimePowerTail Q K t := by
  rw [finiteDividedLogPrimePowerRenewal,
    finiteDividedLogHigherPrimePowerTail]
  rw [← Finset.sum_add_distrib]

/-- Exact defect comparison: primitive Gamma/co-Poisson completion changes
the Route E renewal defect only by higher prime powers. -/
theorem finiteDividedLogPrimePowerRenewalDefect_eq_prime_sub_higher
    (Q : Finset ℕ) (K : ℕ) (t : ℂ) :
    finiteDividedLogPrimePowerRenewalDefect Q K t =
      finitePrimeRenewalDefect Q t -
        finiteDividedLogHigherPrimePowerTail Q K t := by
  rw [finiteDividedLogPrimePowerRenewalDefect,
    finiteDividedLogPrimePowerRenewal_eq_prime_add_higher,
    finitePrimeRenewalDefect]
  ring

/-- Small-prime parity source tested against the complete divided-log
prime-power current before scalarization. -/
def finitePrimePowerCompletedParityBoundary
    (P Q : Finset ℕ) (K : ℕ) (w : ℂ) : ℂ :=
  finitePrimeParityPartition P w -
    ∑ q ∈ Q, (finitePrimeParityPartition P ((q : ℂ) * w) +
      ∑ j ∈ Finset.range K,
        ((j + 2 : ℕ) : ℂ)⁻¹ *
          finitePrimeParityPartition P
            (((q ^ (j + 2) : ℕ) : ℂ) * w))

/-- Exact pre-scalar comparison with the original zero/one-prime
boundary.  Only the higher-prime-power tail is added. -/
theorem finitePrimePowerCompletedParityBoundary_eq_primeBoundary_sub_higher
    (P Q : Finset ℕ) (K : ℕ) (w : ℂ) :
    finitePrimePowerCompletedParityBoundary P Q K w =
      (finitePrimeParityPartition P w -
        ∑ q ∈ Q, finitePrimeParityPartition P ((q : ℂ) * w)) -
      ∑ q ∈ Q, ∑ j ∈ Finset.range K,
        ((j + 2 : ℕ) : ℂ)⁻¹ *
          finitePrimeParityPartition P
            (((q ^ (j + 2) : ℕ) : ℂ) * w) := by
  rw [finitePrimePowerCompletedParityBoundary]
  rw [Finset.sum_add_distrib]
  ring

end

end RHTower
