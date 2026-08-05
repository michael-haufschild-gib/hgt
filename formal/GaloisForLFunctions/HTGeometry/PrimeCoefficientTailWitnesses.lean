import GaloisForLFunctions.HTGeometry.FiniteRangePrimeDirichletModuli

/-!
# Prime coefficient families with vanishing tail exist

A prime coefficient family has vanishing tail when only finitely many primes carry a nonzero
coefficient.  The zero family and every family supported on a finite set of primes have it, the
condition is stable under the linear operations, and it fails for a family that is nowhere zero —
so the tail dichotomy of the finite-range laws separates a genuinely nonempty class from a
genuinely nonempty complement.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Classical

/-- The zero coefficient family has vanishing tail. -/
theorem primeCoefficientTailZero_zero :
    PrimeCoefficientTailZero (fun _ : Nat.Primes => (0 : ℂ)) := by
  rw [PrimeCoefficientTailZero]
  simp

/-- A coefficient family supported on a finite set of primes has vanishing tail. -/
theorem primeCoefficientTailZero_of_support_subset {c : Nat.Primes → ℂ} {s : Finset Nat.Primes}
    (hs : ∀ p, c p ≠ 0 → p ∈ s) : PrimeCoefficientTailZero c :=
  Set.Finite.subset s.finite_toSet fun p hp => hs p hp

/-- A coefficient family concentrated at one prime has vanishing tail. -/
theorem primeCoefficientTailZero_single (p₀ : Nat.Primes) (z : ℂ) :
    PrimeCoefficientTailZero (fun p => if p = p₀ then z else 0) := by
  refine primeCoefficientTailZero_of_support_subset (s := {p₀}) fun p hp => ?_
  by_cases h : p = p₀
  · simp [h]
  · exact absurd (by simp [h]) hp

/-- Vanishing tails are closed under addition. -/
theorem PrimeCoefficientTailZero.add {c d : Nat.Primes → ℂ}
    (hc : PrimeCoefficientTailZero c) (hd : PrimeCoefficientTailZero d) :
    PrimeCoefficientTailZero (fun p => c p + d p) := by
  refine Set.Finite.subset (hc.union hd) fun p hp => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  exact hp (by simp [hcon.1, hcon.2])

/-- Vanishing tails are closed under scalar multiples. -/
theorem PrimeCoefficientTailZero.const_mul {c : Nat.Primes → ℂ}
    (hc : PrimeCoefficientTailZero c) (z : ℂ) :
    PrimeCoefficientTailZero (fun p => z * c p) := by
  refine Set.Finite.subset hc fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro hzero
  exact hp (by simp [hzero])

/-- The constant family with nonzero value has a nonvanishing tail: there are infinitely many
primes. -/
theorem not_primeCoefficientTailZero_const {z : ℂ} (hz : z ≠ 0) :
    ¬ PrimeCoefficientTailZero (fun _ : Nat.Primes => z) := by
  rw [PrimeCoefficientTailZero]
  have huniv : {p : Nat.Primes | z ≠ 0} = (Set.univ : Set Nat.Primes) := by
    ext p
    simp [hz]
  rw [huniv]
  exact Set.infinite_univ

end GaloisForLFunctions.HTGeometry
