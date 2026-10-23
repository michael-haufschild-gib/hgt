import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Linarith

/-!
# Proper-divisor marks on shifted primes

A sum over nontrivial proper divisors vanishes at every prime. Its squared
error in approximating one therefore contains the entire twin-prime mass.
The bound is attained by normalizing the number of proper divisors.
The signed Möbius residual identifies the separate composite contribution.
-/

open Finset
open scoped BigOperators NNReal

noncomputable section

namespace TwinPrime

/-- A mark supported on divisors strictly between one and the argument. -/
def divisorMark (c : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.properDivisors.erase 1, c n d

/-- Every proper-divisor mark vanishes at a prime. -/
theorem divisorMark_prime (c : ℕ → ℕ → ℝ) (p : Nat.Primes) :
    divisorMark c p = 0 := by
  simp only [divisorMark, p.property.properDivisors, erase_singleton, sum_empty]

/-- Weighted mass of the prime shifts in a finite set of primes. -/
def twinMass (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0) : ℝ :=
  ∑ p ∈ S, if Nat.Prime ((p : ℕ) + 2) then (w p : ℝ) else 0

/-- Squared error of the mark as an approximation to one. -/
def divisorMarkError (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0)
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, (w p : ℝ) * (1 - divisorMark c ((p : ℕ) + 2)) ^ 2

/-- The part of the squared error carried by composite shifts. -/
def compositeMarkError (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0)
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, if Nat.Prime ((p : ℕ) + 2) then 0
    else (w p : ℝ) * (1 - divisorMark c ((p : ℕ) + 2)) ^ 2

/-- The prime-valued part of the error is exactly the twin-prime mass. -/
theorem divisorMarkError_eq (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0)
    (c : ℕ → ℕ → ℝ) :
    divisorMarkError S w c = twinMass S w + compositeMarkError S w c := by
  unfold divisorMarkError twinMass compositeMarkError
  rw [← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  by_cases h : Nat.Prime ((p : ℕ) + 2)
  · have hz := divisorMark_prime c ⟨(p : ℕ) + 2, h⟩
    change divisorMark c ((p : ℕ) + 2) = 0 at hz
    simp only [if_pos h, hz, sub_zero, one_pow, mul_one, add_zero]
  · simp only [if_neg h, zero_add]

theorem compositeMarkError_nonneg (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) (c : ℕ → ℕ → ℝ) :
    0 ≤ compositeMarkError S w c := by
  apply sum_nonneg
  intro p _
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (w p).coe_nonneg (sq_nonneg _)

/-- Improving this approximation bounds twin mass from above. -/
theorem twinMass_le_divisorMarkError (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) (c : ℕ → ℕ → ℝ) :
    twinMass S w ≤ divisorMarkError S w c := by
  rw [divisorMarkError_eq]
  exact le_add_of_nonneg_right (compositeMarkError_nonneg S w c)

/-- Equality means that every positive-weight composite shift has mark one. -/
theorem divisorMarkError_eq_twinMass_iff (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) (c : ℕ → ℕ → ℝ) :
    divisorMarkError S w c = twinMass S w ↔
      ∀ p ∈ S, ¬ Nat.Prime ((p : ℕ) + 2) →
        w p = 0 ∨ divisorMark c ((p : ℕ) + 2) = 1 := by
  have hn (p : Nat.Primes) (_ : p ∈ S) :
      0 ≤ if Nat.Prime ((p : ℕ) + 2) then (0 : ℝ)
        else (w p : ℝ) * (1 - divisorMark c ((p : ℕ) + 2)) ^ 2 := by
    split_ifs
    · exact le_refl 0
    · exact mul_nonneg (w p).coe_nonneg (sq_nonneg _)
  constructor
  · intro he p hp hcomp
    have hzero : compositeMarkError S w c = 0 := by
      have := divisorMarkError_eq S w c
      linarith only [he, this]
    have ht := (sum_eq_zero_iff_of_nonneg hn).mp hzero p hp
    rw [if_neg hcomp] at ht
    rcases mul_eq_zero.mp ht with hw | hm
    · exact Or.inl (NNReal.coe_eq_zero.mp hw)
    · right
      rw [pow_two] at hm
      have hz := (mul_eq_zero.mp hm).elim id id
      exact (sub_eq_zero.mp hz).symm
  · intro he
    have hzero : compositeMarkError S w c = 0 := by
      apply sum_eq_zero
      intro p hp
      by_cases h : Nat.Prime ((p : ℕ) + 2)
      · exact if_pos h
      · rw [if_neg h]
        rcases he p hp h with hw | hm
        · simp only [hw, NNReal.coe_zero, zero_mul]
        · simp only [hm, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]
    rw [divisorMarkError_eq, hzero, add_zero]

/-- Equal coefficients make the mark one exactly when a proper divisor exists. -/
def uniformDivisorCoefficient (n _d : ℕ) : ℝ :=
  ((n.properDivisors.erase 1).card : ℝ)⁻¹

theorem uniformDivisorMark_add_two (n : ℕ) :
    divisorMark uniformDivisorCoefficient (n + 2) =
      if Nat.Prime (n + 2) then 0 else 1 := by
  by_cases h : Nat.Prime (n + 2)
  · rw [if_pos h]
    exact divisorMark_prime _ ⟨n + 2, h⟩
  · rw [if_neg h]
    have hone : 1 ∈ (n + 2).properDivisors :=
      Nat.one_mem_properDivisors_iff_one_lt.mpr (by omega)
    have hcard : ((n + 2).properDivisors.erase 1).card ≠ 0 := by
      intro hc
      have hempty := card_eq_zero.mp hc
      rcases (erase_eq_empty_iff _ _).mp hempty with he | he
      · rw [he] at hone
        exact notMem_empty 1 hone
      · exact h (Nat.properDivisors_eq_singleton_one_iff_prime.mp he)
    simp only [divisorMark, uniformDivisorCoefficient, sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hcard)

/-- The lower bound is attained, without any prime-distribution input. -/
theorem divisorMarkError_uniform (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) :
    divisorMarkError S w uniformDivisorCoefficient = twinMass S w := by
  unfold divisorMarkError twinMass
  refine sum_congr rfl fun p _ => ?_
  rw [uniformDivisorMark_add_two]
  by_cases h : Nat.Prime ((p : ℕ) + 2)
  · simp only [if_pos h, sub_zero, one_pow, mul_one]
  · simp only [if_neg h, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]

/-- Twin mass is the attainable minimum over all proper-divisor marks. -/
theorem exists_divisorMark_minimum (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) :
    ∃ c : ℕ → ℕ → ℝ, divisorMarkError S w c = twinMass S w ∧
      ∀ d : ℕ → ℕ → ℝ, divisorMarkError S w c ≤ divisorMarkError S w d := by
  refine ⟨uniformDivisorCoefficient, divisorMarkError_uniform S w, ?_⟩
  intro d
  rw [divisorMarkError_uniform]
  exact twinMass_le_divisorMarkError S w d

/-- Signed error left after applying a proper-divisor mark. -/
def moebiusMarkResidual (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0)
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, (w p : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) + 2) : ℝ) *
    (1 - divisorMark c ((p : ℕ) + 2))

/-- Composite contribution to the signed residual. -/
def compositeMoebiusResidual (S : Finset Nat.Primes) (w : Nat.Primes → ℝ≥0)
    (c : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, if Nat.Prime ((p : ℕ) + 2) then 0
    else (w p : ℝ) * (ArithmeticFunction.moebius ((p : ℕ) + 2) : ℝ) *
      (1 - divisorMark c ((p : ℕ) + 2))

/-- A twin lower bound requires a signed surplus over the total residual. -/
theorem twinMass_eq_signed_residual_difference (S : Finset Nat.Primes)
    (w : Nat.Primes → ℝ≥0) (c : ℕ → ℕ → ℝ) :
    twinMass S w = compositeMoebiusResidual S w c - moebiusMarkResidual S w c := by
  unfold twinMass compositeMoebiusResidual moebiusMarkResidual
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  by_cases h : Nat.Prime ((p : ℕ) + 2)
  · have hz := divisorMark_prime c ⟨(p : ℕ) + 2, h⟩
    change divisorMark c ((p : ℕ) + 2) = 0 at hz
    simp only [if_pos h, hz, ArithmeticFunction.moebius_apply_prime h,
      Int.cast_neg, Int.cast_one, sub_zero, mul_one, mul_neg, zero_sub, neg_neg]
  · simp only [if_neg h, sub_self]

end TwinPrime

#print axioms TwinPrime.divisorMarkError_eq_twinMass_iff
#print axioms TwinPrime.exists_divisorMark_minimum
#print axioms TwinPrime.twinMass_eq_signed_residual_difference
