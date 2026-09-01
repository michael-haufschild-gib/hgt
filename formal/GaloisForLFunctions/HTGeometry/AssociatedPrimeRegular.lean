import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regularity of a scalar is avoidance of the associated primes

Over a Noetherian ring the zero divisors on a module are the union of its associated primes
(`biUnion_associatedPrimes_eq_zero_divisors`), so a scalar acts regularly exactly when it lies
outside every associated prime.

This is the entry point of the Cohen–Macaulay argument the critical horizon needs: to know that a
system of parameters is a regular sequence one has to know, at each stage, that the next parameter
misses every associated prime of the current quotient.
-/

namespace GaloisForLFunctions.HTGeometry

variable (R : Type*) [CommRing R] [IsNoetherianRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- **A scalar outside every associated prime is regular**, and conversely.  Over a Noetherian
ring the zero divisors on a module are exactly the union of its associated primes. -/
theorem isSMulRegular_iff_forall_notMem_associatedPrimes {y : R} :
    IsSMulRegular M y ↔ ∀ p ∈ associatedPrimes R M, y ∉ p := by
  constructor
  · intro hy p hp hmem
    have : y ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
      Set.mem_iUnion₂_of_mem hp hmem
    rw [biUnion_associatedPrimes_eq_zero_divisors R M] at this
    obtain ⟨x, hx, hyx⟩ := this
    exact hx (hy (by simpa using hyx))
  · intro h a b hab
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.2 hne
    have hzero : y • (a - b) = 0 := by
      have : y • a = y • b := hab
      rw [smul_sub, this, sub_self]
    have hmem : y ∈ { r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0 } := ⟨a - b, hne', hzero⟩
    rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hmem
    simp only [Set.mem_iUnion₂] at hmem
    obtain ⟨p, hp, hy⟩ := hmem
    exact h p hp hy

end GaloisForLFunctions.HTGeometry
