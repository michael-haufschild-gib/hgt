import GaloisForLFunctions.RHTower.ActionStableWitnesses

/-!
# Realizations of the prime-log expansion interfaces

A finite integer expansion in prime logarithms exists for `0`, for each prime logarithm, and for
sums, in both the natural-number-indexed and the prime-indexed form.  Combining the prime-indexed
form with the lattice membership already available reduces stability of the prime-log lattice to the
checkable statement that the action sends each prime logarithm to a finite prime-indexed expansion.
-/

namespace GaloisForLFunctions

namespace RHTower

/-! ## Natural-number-indexed expansions -/

theorem primeLogExpansion_zero : PrimeLogExpansion 0 := by
  refine ⟨0, ?_, ?_⟩
  · intro p hp
    simp at hp
  · simp

theorem primeLogExpansion_log_prime {p : ℕ} (hp : p.Prime) :
    PrimeLogExpansion (Real.log p) := by
  classical
  refine ⟨Finsupp.single p 1, ?_, ?_⟩
  · intro q hq
    rw [Finsupp.single_apply_ne_zero] at hq
    rcases hq with ⟨rfl, _⟩
    exact hp
  · rw [Finsupp.sum_single_index (by simp)]
    simp

theorem PrimeLogExpansion.add {x y : ℝ}
    (hx : PrimeLogExpansion x) (hy : PrimeLogExpansion y) :
    PrimeLogExpansion (x + y) := by
  classical
  obtain ⟨cx, hcx, rfl⟩ := hx
  obtain ⟨cy, hcy, rfl⟩ := hy
  refine ⟨cx + cy, ?_, ?_⟩
  · intro p hp
    by_cases hxp : cx p = 0
    · have hyp : cy p ≠ 0 := by
        intro h
        exact hp (by simp [hxp, h])
      exact hcy p hyp
    · exact hcx p hxp
  · rw [Finsupp.sum_add_index' (by intro p; simp) (by intro p b₁ b₂; exact add_smul b₁ b₂ _)]

/-! ## Prime-indexed expansions -/

theorem primeIndexedLogExpansion_zero : PrimeIndexedLogExpansion 0 := by
  refine ⟨0, ?_⟩
  simp

theorem primeIndexedLogExpansion_log_prime (p : Nat.Primes) :
    PrimeIndexedLogExpansion (Real.log (p : ℕ)) := by
  classical
  refine ⟨Finsupp.single p 1, ?_⟩
  rw [Finsupp.sum_single_index (by simp)]
  simp

theorem PrimeIndexedLogExpansion.add {x y : ℝ}
    (hx : PrimeIndexedLogExpansion x) (hy : PrimeIndexedLogExpansion y) :
    PrimeIndexedLogExpansion (x + y) := by
  classical
  obtain ⟨cx, rfl⟩ := hx
  obtain ⟨cy, rfl⟩ := hy
  refine ⟨cx + cy, ?_⟩
  rw [Finsupp.sum_add_index' (by intro p; simp) (by intro p b₁ b₂; exact add_smul b₁ b₂ _)]

/-! ## Lattice stability from prime-indexed expansions -/

variable {Greal : Type*} [Group Greal] [DistribMulAction Greal ℝ]

/-- Stability of the prime-log lattice follows from a finite prime-indexed expansion of every moved
prime logarithm. -/
theorem isActionStable_primeLogLattice_of_primeIndexedExpansion
    (h : ∀ (g : Greal) (p : ℕ), p.Prime →
      PrimeIndexedLogExpansion (g • Real.log p)) :
    IsActionStable Greal primeLogLattice :=
  isActionStable_primeLogLattice_of_smul_primeLog fun g p hp =>
    (h g p hp).mem_primeLogLattice

/-- The first two prime logarithms have an explicit finite prime-log expansion. -/
theorem primeLogExpansion_log_two_add_log_three :
    PrimeLogExpansion (Real.log (2 : ℕ) + Real.log (3 : ℕ)) :=
  PrimeLogExpansion.add
    (primeLogExpansion_log_prime Nat.prime_two)
    (primeLogExpansion_log_prime Nat.prime_three)

/-- The fifth prime logarithm has its explicit one-support expansion. -/
theorem primeLogExpansion_log_five : PrimeLogExpansion (Real.log (5 : ℕ)) :=
  primeLogExpansion_log_prime Nat.prime_five

end RHTower

end GaloisForLFunctions
