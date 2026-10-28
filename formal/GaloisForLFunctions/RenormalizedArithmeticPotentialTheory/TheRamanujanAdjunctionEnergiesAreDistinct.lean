import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSieveExcitationsHaveAdjunctionEnergy

/-!
# Distinct positive conductors have distinct adjunction energies

Any two conductors lie in one finite prime sieve. The proved separation of
finite-sieve energies therefore separates all positive integer labels.
-/

noncomputable section

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticIntersectionTheory

/-- A positive integer belongs to any sieve containing its prime-exponent support. -/
theorem sieveSupported_of_primeExponentVector_support_subset
    {Q : Finset Nat.Primes} {m : ℕ} (hm : 0 < m)
    (hQ : (primeExponentVector m).support ⊆ Q) : SieveSupported Q m := by
  classical
  let e : Q → ℕ := fun p => primeExponentVector m p
  have he : sieveExponentVector Q e = primeExponentVector m := by
    ext p
    rw [sieveExponentVector_apply]
    by_cases hp : p ∈ Q
    · rw [dif_pos hp]
    · rw [dif_neg hp]
      symm
      by_contra hne
      exact hp (hQ (Finsupp.mem_support_iff.mpr hne))
  have h := sieveSupported_primeProduct Q e
  rw [he, primeProduct_primeExponentVector hm.ne'] at h
  exact h

/-- No two positive arithmetic conductors have the same full-prime trial energy. -/
theorem ramanujanAdjunctionEnergy_injectiveOn :
    Set.InjOn ramanujanAdjunctionEnergy {m : ℕ | 0 < m} := by
  classical
  intro m hm n hn h
  let Q := (primeExponentVector m).support ∪ (primeExponentVector n).support
  have hmQ : SieveSupported Q m := sieveSupported_of_primeExponentVector_support_subset hm
    (Finset.subset_union_left)
  have hnQ : SieveSupported Q n := sieveSupported_of_primeExponentVector_support_subset hn
    (Finset.subset_union_right)
  have he : Real.log m + tameDifferent m = Real.log n + tameDifferent n :=
    add_left_cancel h
  have hlabel : (⟨m, hmQ⟩ : SieveClass Q) = ⟨n, hnQ⟩ :=
    sieveAdjunctionEnergy_injective Q he
  exact congrArg Subtype.val hlabel

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

