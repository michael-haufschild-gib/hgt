import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree

/-!
# Multiplicative functions from local prime-power data

Construct the normalized multiplicative function of arbitrary local data,
reusing the product-form multiplicativity and prime-power lemmas already in
`DampedMobiusSumsZeroFree`. No complete-multiplicativity relation between
successive exponents is imposed. Exponent zero is normalized to one, and extra
finite prime sets can be inserted into the Euler product exactly.

This supplies the local-factor construction for the dilation expansion in
Lemma 18.2 of *Ordinary two-point correlations of multiplicative functions*.
-/


open Finset
namespace RHTower.Sieve
noncomputable section
variable {R : Type*} [CommMonoidWithZero R]

/-- The normalized multiplicative function specified by arbitrary positive prime-power values. -/
def localEuler (A : ℕ → ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else ∏ p ∈ n.primeFactors, A p (n.factorization p)
  map_zero' := if_pos rfl

@[simp] theorem localEuler_zero (A : ℕ → ℕ → R) : localEuler A 0 = 0 := rfl

@[simp] theorem localEuler_one (A : ℕ → ℕ → R) : localEuler A 1 = 1 := by
  simp [localEuler]

/-- No relations between different prime-power values are needed for multiplicativity. -/
theorem localEuler_isMultiplicative (A : ℕ → ℕ → R) :
    (localEuler A).IsMultiplicative := by
  exact RHTower.DampedMobius.isMultiplicative_of_prod A (localEuler A)
    (fun n hn => by simp [localEuler, hn])

/-- Prime-power values are recovered exactly; exponent zero is normalized to one. -/
theorem localEuler_prime_pow (A : ℕ → ℕ → R) (p : Nat.Primes) (k : ℕ) :
    localEuler A ((p : ℕ) ^ k) = if k = 0 then 1 else A p k := by
  by_cases hk : k = 0
  · subst k; simp
  · change (if (p : ℕ) ^ k = 0 then 0 else _) = _
    rw [if_neg (pow_ne_zero _ p.property.ne_zero), if_neg hk]
    exact RHTower.DampedMobius.prod_prime_pow A p.property hk

/-- In particular, the prime values are exactly the supplied degree-one data. -/
theorem localEuler_prime (A : ℕ → ℕ → R) (p : Nat.Primes) :
    localEuler A p = A p 1 := by
  simpa using localEuler_prime_pow A p 1

/-- Exponent zero is normalized to the multiplicative identity. -/
def normalizedPrimePowerValue (A : ℕ → ℕ → R) (p k : ℕ) : R :=
  if k = 0 then 1 else A p k

private theorem localEuler_eq_prod_of_subset (A : ℕ → ℕ → R)
    {n : ℕ} (hn : n ≠ 0) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    localEuler A n = ∏ p ∈ S, normalizedPrimePowerValue A p (n.factorization p) := by
  change (if n = 0 then 0 else _) = _
  rw [if_neg hn]
  apply prod_subset_one_on_sdiff hS
  · intro p hp
    have hz : n.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa using (mem_sdiff.mp hp).2)
    simp [normalizedPrimePowerValue, hz]
  · intro p hp
    have hz : n.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp (by simpa using hp)
    simp [normalizedPrimePowerValue, hz]

/-- Any additional finite set of primes can be inserted without changing the Euler value. -/
theorem localEuler_eq_prod_on_union (A : ℕ → ℕ → R) (n : ℕ) (S : Finset ℕ) :
    localEuler A n = if n = 0 then 0 else
      ∏ p ∈ S ∪ n.primeFactors, normalizedPrimePowerValue A p (n.factorization p) := by
  by_cases hn : n = 0
  · subst n; simp
  · rw [if_neg hn]
    exact localEuler_eq_prod_of_subset A hn _ subset_union_right

end
end RHTower.Sieve
