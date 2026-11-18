import Mathlib.Algebra.BigOperators.Associated

/-!
# Injective marks

Distinct primes `p_i` of a cancellative monoid with trivial units (for example nonzero integral
ideals of a Dedekind domain) give an injective map `U ↦ ∏_{i ∈ U} p_i` on finite sets of positions
(Lemma 8.2): a prime `p_i` divides the product exactly when `i ∈ U`. Hence an injective mark
`M_I(n) = Σ_{distinct (p_i)} Π b_i(p_i)` reads each selected tuple once.
-/

namespace GaloisForLFunctions.JointMarkedMoments

variable {α ι : Type*} [CancelCommMonoidWithZero α] [Unique αˣ]

/-- A prime divides a product of distinct primes exactly at its own position. -/
theorem prime_dvd_prod_iff {p : ι → α} (hp : ∀ i, Prime (p i)) (hinj : Function.Injective p)
    (U : Finset ι) (i : ι) : p i ∣ ∏ j ∈ U, p j ↔ i ∈ U := by
  constructor
  · intro h
    obtain ⟨j, hj, hdvd⟩ := ((hp i).dvd_finsetProd_iff p).1 h
    have : p i = p j := associated_iff_eq.1 ((hp i).associated_of_dvd (hp j) hdvd)
    rwa [hinj this]
  · intro hi
    exact Finset.dvd_prod_of_mem p hi

/-- Lemma 8.2: `U ↦ ∏_{i ∈ U} p_i` is injective. -/
theorem prod_primes_injective {p : ι → α} (hp : ∀ i, Prime (p i)) (hinj : Function.Injective p) :
    Function.Injective (fun U : Finset ι => ∏ i ∈ U, p i) := by
  intro U V h
  ext i
  rw [← prime_dvd_prod_iff hp hinj U i, ← prime_dvd_prod_iff hp hinj V i]
  simp only at h
  rw [h]

end GaloisForLFunctions.JointMarkedMoments
