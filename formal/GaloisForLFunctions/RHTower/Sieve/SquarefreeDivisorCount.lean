import GaloisForLFunctions.RHTower.Sieve.EulerExpansion

/-!
# A squarefree integer has `2^ω` divisors

For squarefree `m` the divisors are exactly the products of subsets of `m.primeFactors`, so

`#m.divisors = 2^{ω(m)}`.

This quantifies the multiplicity obstruction the coprime card records: a balanced factorization count
overcounts each physical product by its number of coprime factorizations, and that number is
`2^{ω(m)}` — **unbounded**.  Dividing a representation count by the multiplicity therefore loses an
unbounded factor, which is why a representation density does not by itself give a distinct-target
bound.
-/

namespace RHTower.Sieve

open Finset

/-- The divisors of a squarefree integer are the subset products of its prime factors. -/
theorem divisors_eq_image_powerset {m : ℕ} (hm : Squarefree m) (hm0 : m ≠ 0) :
    m.divisors = m.primeFactors.powerset.image (fun T => ∏ p ∈ T, p) := by
  classical
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hdvd, -⟩
    refine ⟨d.primeFactors, Nat.primeFactors_mono hdvd hm0, ?_⟩
    exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hdvd)
  · rintro ⟨T, hT, rfl⟩
    refine ⟨?_, hm0⟩
    calc ∏ p ∈ T, p ∣ ∏ p ∈ m.primeFactors, p := Finset.prod_dvd_prod_of_subset _ _ _ hT
      _ = m := Nat.prod_primeFactors_of_squarefree hm

/-- **A squarefree integer has `2^ω` divisors.** -/
theorem card_divisors_of_squarefree_squarefreeDivisorCount {m : ℕ} (hm : Squarefree m) (hm0 : m ≠ 0) :
    m.divisors.card = 2 ^ m.primeFactors.card := by
  classical
  rw [divisors_eq_image_powerset hm hm0]
  rw [Finset.card_image_of_injOn (prod_injOn_powerset (fun p hp => Nat.prime_of_mem_primeFactors hp))]
  exact Finset.card_powerset _

end RHTower.Sieve
