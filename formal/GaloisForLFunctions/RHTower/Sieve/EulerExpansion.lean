import GaloisForLFunctions.RHTower.Sieve.EulerDamping

/-!
# The damped product as a Dirichlet sum

Expanding the finite Euler product turns it into a sum over subsets:

`∏_{p ∈ P} (1 + z_p) = ∑_{T ⊆ P} ∏_{p ∈ T} z_p`,

and when `P` consists of primes the map `T ↦ ∏_{p ∈ T} p` is injective, its image being exactly the
squarefree `P`-smooth integers.  So the subset sum *is* a Dirichlet sum over those integers.

Combining with the damping bound, the Dirichlet sum obeys

`‖∑_{T ⊆ P} ∏_{p ∈ T} f(p) p^{-it}/p‖ ≤ exp(∑_{p ∈ P} 1/p + ∑_{p ∈ P} 1/p² - D(f,t;P)²)`.

The bound is an equality-through-the-product, not a triangle inequality: the sum is rewritten as the
product and only then estimated, so no cancellation is thrown away in the passage.
-/

namespace RHTower.Sieve

open Finset

/-- **Expansion of a finite Euler product over subsets.** -/
theorem prod_one_add_eq_sum_powerset {ι : Type*} [DecidableEq ι] (P : Finset ι) (z : ι → ℂ) :
    ∏ p ∈ P, (1 + z p) = ∑ T ∈ P.powerset, ∏ p ∈ T, z p := by
  have h := Finset.prod_add z (fun _ => (1 : ℂ)) P
  simpa [add_comm] using h

/-- On a set of primes, a subset is recovered from its product. -/
theorem primeFactors_prod_of_subset {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {T : Finset ℕ}
    (hT : T ⊆ P) : (∏ p ∈ T, p).primeFactors = T :=
  Nat.primeFactors_prod fun p hp => hP p (hT hp)

/-- **The subset-to-integer map is injective on a set of primes.** -/
theorem prod_injOn_powerset {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) ↑P.powerset := by
  intro S hS T hT hST
  have hS' : S ⊆ P := Finset.mem_powerset.mp (by simpa using hS)
  have hT' : T ⊆ P := Finset.mem_powerset.mp (by simpa using hT)
  calc S = (∏ p ∈ S, p).primeFactors := (primeFactors_prod_of_subset hP hS').symm
    _ = (∏ p ∈ T, p).primeFactors := by
          simp only at hST
          rw [hST]
    _ = T := primeFactors_prod_of_subset hP hT'

/-- **The Dirichlet sum over squarefree `P`-smooth integers is damped by the distance.** -/
theorem norm_sum_powerset_le_exp {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (t : ℝ) {P : Finset ℕ}
    (hP : ∀ p ∈ P, 0 < p) :
    ‖∑ T ∈ P.powerset, ∏ p ∈ T, ((1 / (p : ℝ) : ℝ) : ℂ)
        * (f p * Complex.exp (((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I))‖
      ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) + (∑ p ∈ P, 1 / (p : ℝ) ^ 2) - mulDistSq f t P) := by
  classical
  rw [← prod_one_add_eq_sum_powerset, norm_prod]
  exact prod_euler_factor_le hf t hP

end RHTower.Sieve
