import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# Wold-sieve normal cone and the von Mangoldt current

The common normal deformation of a finite family of Wold off-multiple
factors has one scalar factor

`∏ p ∈ S, (1 - exp (-h * log p))`

on an incidence set `S`.  Its first derivative vanishes unless `S` is a
singleton.  Applied to the complete prime-factor set of `n`, this says
that the first normal stratum is exactly the prime-power stratum and its
coefficient is `ArithmeticFunction.vonMangoldt n`.

This is unconditional source algebra.  It does not assert any critical
Gamma/co-Poisson boundary estimate or RH.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Scalar common-normal factor attached to a finite prime-incidence set. -/
def woldSieveNormalFactor (S : Finset ℕ) (h : ℝ) : ℝ :=
  ∏ p ∈ S, (1 - Real.exp (-h * Real.log p))

/-- One Wold factor has outward normal derivative `log p`. -/
theorem hasDerivAt_woldSievePrimeFactor (p : ℕ) :
    HasDerivAt (fun h : ℝ => 1 - Real.exp (-h * Real.log p)) (Real.log p) 0 := by
  have hinner :
      HasDerivAt (fun h : ℝ => -h * Real.log p) (-Real.log p) 0 := by
    have hid : HasDerivAt (fun h : ℝ => h) 1 0 := hasDerivAt_id 0
    simpa using (hid.neg.mul_const (Real.log p))
  have he :
      HasDerivAt (fun h : ℝ => Real.exp (-h * Real.log p)) (-Real.log p) 0 := by
    simpa only [Function.comp_apply, neg_zero, zero_mul, Real.exp_zero, one_mul] using!
      (Real.hasDerivAt_exp (-0 * Real.log p)).comp 0 hinner
  simpa only [Pi.sub_apply, Function.comp_apply, neg_zero, zero_mul, Real.exp_zero,
    one_mul, zero_sub, neg_neg] using!
      he.const_sub 1

/-- Finite-product rule for the common-normal Wold factor. -/
theorem hasDerivAt_woldSieveNormalFactor (S : Finset ℕ) :
    HasDerivAt (woldSieveNormalFactor S)
      (∑ p ∈ S,
        (∏ q ∈ S.erase p, (1 - Real.exp (-(0 : ℝ) * Real.log q))) * Real.log p) 0 := by
  change HasDerivAt
    (fun h : ℝ => ∏ p ∈ S, (1 - Real.exp (-h * Real.log p))) _ 0
  simpa using
    (HasDerivAt.fun_finsetProd (u := S)
      (f := fun (p : ℕ) (h : ℝ) => 1 - Real.exp (-h * Real.log p))
      (f' := fun p => Real.log p)
      (x := 0) (fun p _ => hasDerivAt_woldSievePrimeFactor p))

/-- A singleton incidence set contributes its prime logarithm. -/
theorem hasDerivAt_woldSieveNormalFactor_singleton (p : ℕ) :
    HasDerivAt (woldSieveNormalFactor {p}) (Real.log p) 0 := by
  change HasDerivAt
    (fun h : ℝ => ∏ q ∈ ({p} : Finset ℕ), (1 - Real.exp (-h * Real.log q)))
    (Real.log p) 0
  simpa using
    hasDerivAt_woldSievePrimeFactor p

/-- Every incidence set containing at least two primes has zero first normal jet. -/
theorem hasDerivAt_woldSieveNormalFactor_of_nontrivial
    {S : Finset ℕ} (hS : S.Nontrivial) :
    HasDerivAt (woldSieveNormalFactor S) 0 0 := by
  have hzero :
      (∑ p ∈ S,
        (∏ q ∈ S.erase p, (1 - Real.exp (-(0 : ℝ) * Real.log q))) *
          Real.log p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hne : (S.erase p).Nonempty := hS.erase_nonempty
    have hcard : 0 < (S.erase p).card := Finset.card_pos.mpr hne
    simp only [neg_zero, zero_mul, Real.exp_zero, sub_self, Finset.prod_const]
    rw [zero_pow hcard.ne']
    simp
  convert hasDerivAt_woldSieveNormalFactor S using 1
  exact hzero.symm

/-- Complete all-prime incidence factor at one positive-integer coordinate. -/
def woldIncidenceNormalFactor (n : ℕ) (h : ℝ) : ℝ :=
  woldSieveNormalFactor n.primeFactors h

/-- On a prime power, the first Wold normal jet is the von Mangoldt weight. -/
theorem hasDerivAt_woldIncidenceNormalFactor_of_isPrimePow
    {n : ℕ} (hn : IsPrimePow n) :
    HasDerivAt (woldIncidenceNormalFactor n)
      (ArithmeticFunction.vonMangoldt n) 0 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  change HasDerivAt
    (woldSieveNormalFactor (p ^ k).primeFactors)
    (ArithmeticFunction.vonMangoldt (p ^ k)) 0
  rw [Nat.primeFactors_prime_pow hk.ne' hp]
  simpa [ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp] using
    hasDerivAt_woldSieveNormalFactor_singleton p

/-- Outside the prime-power stratum, the first Wold normal jet vanishes. -/
theorem hasDerivAt_woldIncidenceNormalFactor_of_not_isPrimePow
    {n : ℕ} (hn : ¬ IsPrimePow n) :
    HasDerivAt (woldIncidenceNormalFactor n) 0 0 := by
  change HasDerivAt (woldSieveNormalFactor n.primeFactors) 0 0
  by_cases hempty : n.primeFactors = ∅
  · rw [hempty]
    change HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0
    simpa using!
      (hasDerivAt_const (x := 0) (c := (1 : ℝ)))
  · have hcard0 : n.primeFactors.card ≠ 0 := by
      simpa using hempty
    have hcard1 : n.primeFactors.card ≠ 1 := by
      simpa [isPrimePow_iff_card_primeFactors_eq_one] using hn
    have hgt : 1 < n.primeFactors.card := by omega
    exact hasDerivAt_woldSieveNormalFactor_of_nontrivial
      (Finset.one_lt_card.mp hgt)

/-- **Wold normal-cone/von Mangoldt identity.**

For every positive-integer coordinate (and harmlessly also `0`), the
first normal derivative of the complete prime-incidence Wold factor is
exactly the von Mangoldt function.
-/
theorem hasDerivAt_woldIncidenceNormalFactor (n : ℕ) :
    HasDerivAt (woldIncidenceNormalFactor n)
      (ArithmeticFunction.vonMangoldt n) 0 := by
  by_cases hn : IsPrimePow n
  · exact hasDerivAt_woldIncidenceNormalFactor_of_isPrimePow hn
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
    exact hasDerivAt_woldIncidenceNormalFactor_of_not_isPrimePow hn

end

end RHTower
