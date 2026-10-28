import GaloisForLFunctions.HTGeometry.SmoothNumbers
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFiniteSieveHasTheTowerFinitePart

/-!
# Finite sieve classes are complete valuation coordinates

Unique factorization identifies the supported positive integers with all
nonnegative exponent vectors on the finite prime set, with no exponent cutoff.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.HTGeometry

/-- Extend a finite sieve exponent vector by zero on the other primes. -/
def sieveExponentVector (Q : Finset Nat.Primes) (e : Q → ℕ) : Nat.Primes →₀ ℕ := by
  classical
  exact Finsupp.onFinset Q (fun p => if hp : p ∈ Q then e ⟨p, hp⟩ else 0)
    (fun p hp => by
      by_contra h
      exact hp (dif_neg h))

theorem sieveExponentVector_apply (Q : Finset Nat.Primes) (e : Q → ℕ) (p : Nat.Primes) :
    sieveExponentVector Q e p = if hp : p ∈ Q then e ⟨p, hp⟩ else 0 := rfl

theorem sieveExponentVector_apply_mem (Q : Finset Nat.Primes) (e : Q → ℕ) (p : Q) :
    sieveExponentVector Q e p = e p := by
  rw [sieveExponentVector_apply, dif_pos p.property]

theorem sieveExponentVector_support_subset (Q : Finset Nat.Primes) (e : Q → ℕ) :
    (sieveExponentVector Q e).support ⊆ Q := by
  intro p hp
  by_contra h
  have hn := Finsupp.mem_support_iff.mp hp
  rw [sieveExponentVector_apply, dif_neg h] at hn
  exact hn rfl

/-- A finite product of supported factors is supported. -/
theorem SieveSupported.prod {Q : Finset Nat.Primes} {I : Type*}
    (s : Finset I) (f : I → ℕ) (h : ∀ i ∈ s, SieveSupported Q (f i)) :
    SieveSupported Q (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- Every exponent vector on the sieve gives a supported positive integer. -/
theorem sieveSupported_primeProduct (Q : Finset Nat.Primes) (e : Q → ℕ) :
    SieveSupported Q (primeProduct (sieveExponentVector Q e)) := by
  classical
  rw [primeProduct, Finsupp.prod]
  apply SieveSupported.prod
  intro p hp
  have hpQ := sieveExponentVector_support_subset Q e hp
  refine ⟨sieveExponentVector Q e p, pow_dvd_pow_of_dvd ?_ _⟩
  exact Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hpQ

theorem factorization_eq_zero_of_notMem_sieve {Q : Finset Nat.Primes} {n : ℕ}
    (hn : SieveSupported Q n) {p : Nat.Primes} (hp : p ∉ Q) :
    n.factorization (p : ℕ) = 0 := by
  by_contra hne
  have hmem : (p : ℕ) ∈ n.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]
    exact hne
  exact hp (hn.prime_dvd_mem (Nat.dvd_of_mem_primeFactors hmem))

theorem sieveExponentVector_factorization {Q : Finset Nat.Primes} {n : ℕ}
    (hn : SieveSupported Q n) :
    sieveExponentVector Q (fun p => n.factorization (p : Nat.Primes)) =
      primeExponentVector n := by
  classical
  ext p
  rw [sieveExponentVector_apply, primeExponentVector_apply]
  by_cases hp : p ∈ Q
  · rw [dif_pos hp]
  · rw [dif_neg hp, factorization_eq_zero_of_notMem_sieve hn hp]

/-- All supported positive integers, with their actual numerical labels. -/
abbrev SieveClass (Q : Finset Nat.Primes) := {n : ℕ // SieveSupported Q n}

/-- Prime valuations give a bijection with the entire finite exponent lattice. -/
def sieveValuationEquiv (Q : Finset Nat.Primes) : SieveClass Q ≃ (Q → ℕ) where
  toFun n p := (n : ℕ).factorization (p : Nat.Primes)
  invFun e := ⟨primeProduct (sieveExponentVector Q e), sieveSupported_primeProduct Q e⟩
  left_inv n := by
    apply Subtype.ext
    exact (congrArg primeProduct (sieveExponentVector_factorization n.property)).trans
      (primeProduct_primeExponentVector n.property.pos.ne')
  right_inv e := by
    funext p
    exact (primeProduct_factorization (sieveExponentVector Q e) (p : Nat.Primes)).trans
      (sieveExponentVector_apply_mem Q e p)

theorem sieveValuationEquiv_apply (Q : Finset Nat.Primes) (n : SieveClass Q) (p : Q) :
    sieveValuationEquiv Q n p = (n : ℕ).factorization (p : Nat.Primes) := rfl

theorem sieveValuationEquiv_symm_apply (Q : Finset Nat.Primes) (e : Q → ℕ) :
    ((sieveValuationEquiv Q).symm e : ℕ) = primeProduct (sieveExponentVector Q e) := rfl

/-- Logarithmic degree is exactly the finite valuation-weighted prime logarithm. -/
theorem log_sieveValuationEquiv_symm (Q : Finset Nat.Primes) (e : Q → ℕ) :
    Real.log (((sieveValuationEquiv Q).symm e : ℕ) : ℝ) =
      ∑ p : Q, (e p : ℝ) * Real.log ((p : Nat.Primes) : ℕ) := by
  classical
  rw [sieveValuationEquiv_symm_apply, log_primeProduct,
    Finsupp.sum_of_support_subset _ (sieveExponentVector_support_subset Q e) _
      (fun _ _ => by simp)]
  rw [← Finset.sum_coe_sort Q]
  apply Finset.sum_congr rfl
  intro p _
  rw [sieveExponentVector_apply_mem]

/-- Agreement away from one sieve prime is exactly agreement of the complementary
valuation coordinates, including all primes outside the sieve. -/
theorem sieveValuations_agree_off_prime_iff (Q : Finset Nat.Primes)
    (m n : SieveClass Q) (p : Q) :
    (∀ l : ℕ, l ≠ ((p : Nat.Primes) : ℕ) →
      (m : ℕ).factorization l = (n : ℕ).factorization l) ↔
    (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q m j) =
      (fun j : {j : Q // j ≠ p} => sieveValuationEquiv Q n j) := by
  constructor
  · intro h
    funext j
    apply h
    intro hj
    exact j.property (Subtype.ext (Subtype.ext hj))
  · intro h l hl
    by_cases hprime : l.Prime
    · let lp : Nat.Primes := ⟨l, hprime⟩
      by_cases hQ : lp ∈ Q
      · let j : Q := ⟨lp, hQ⟩
        have hj : j ≠ p := fun hjp => hl (congrArg (fun r : Q => ((r : Nat.Primes) : ℕ)) hjp)
        exact congrFun h ⟨j, hj⟩
      · exact (factorization_eq_zero_of_notMem_sieve m.property hQ).trans
          (factorization_eq_zero_of_notMem_sieve n.property hQ).symm
    · rw [Nat.factorization_eq_zero_of_not_prime _ hprime,
        Nat.factorization_eq_zero_of_not_prime _ hprime]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
