import GaloisForLFunctions.HTGeometry.CoordinateCorankDirectedSup
import GaloisForLFunctions.HTGeometry.Resonance

/-!
# The relation lattice of the arithmetic frequencies and its coordinate coranks

The relation lattice of a family of frequencies is the set of finitely supported integer vectors
annihilating it.  Its rational span is a subspace of `P →₀ ℚ`, so the coordinate coranks of the
previous file apply.  For the prime logarithms the relation lattice is trivial, so every finite
prime slice has corank equal to its size and the coranks are unbounded: the limit corank is
infinite while every slice is finite.

* `relationSpan` — the rational span of a set of integer relation vectors.
* `relationSpan_primeLog_eq_bot` — the arithmetic relation lattice spans nothing.
* `coordCorank_primeLog` — every finite prime slice has corank equal to the number of primes in it.
* `not_bddAbove_coordCorank_primeLog`, `not_finiteDimensional_quotient_primeLog` — the coranks are
  unbounded and the limit is infinite dimensional.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {P : Type*}

/-- The rational span of a set of integer relation vectors. -/
noncomputable def relationSpan (S : Set (P →₀ ℤ)) : Submodule ℚ (P →₀ ℚ) :=
  Submodule.span ℚ ((fun m : P →₀ ℤ => Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero m) '' S)

theorem relationSpan_singleton_zero : relationSpan ({0} : Set (P →₀ ℤ)) = ⊥ := by
  rw [relationSpan]
  simp

/-- The frequency relation lattice of a family, as a set of integer vectors. -/
abbrev frequencyRelationLattice {A : Type*} [AddCommGroup A] (ω : P → A) : Set (P →₀ ℤ) :=
  diagonalRelationLattice ω

/-- **The arithmetic prime-frequency relation lattice spans the zero subspace.**  Its triviality is
unique factorization, in the form of rational independence of the prime logarithms. -/
theorem relationSpan_primeLog_eq_bot :
    relationSpan (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ))) = ⊥ := by
  rw [frequencyRelationLattice, primeLog_diagonalRelationLattice_eq_singleton,
    relationSpan_singleton_zero]

/-- **Every finite prime slice has corank equal to its size.** -/
theorem coordCorank_primeLog (T : Finset Nat.Primes) :
    coordCorank
      (relationSpan (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)))) T
      = T.card := by
  rw [relationSpan_primeLog_eq_bot, coordCorank_bot]

/-- **The prime coranks are unbounded.** -/
theorem not_bddAbove_coordCorank_primeLog :
    ¬ BddAbove (Set.range (coordCorank
      (relationSpan (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)))))) := by
  rw [relationSpan_primeLog_eq_bot]
  exact not_bddAbove_coordCorank_bot

/-- **The arithmetic limit has infinite corank while every finite prime slice has finite corank.**
This is the non-reconstruction witness: the finite-base slices are all trivially finite, and the
infinitude lives only in the limit. -/
theorem not_finiteDimensional_quotient_primeLog :
    ¬ FiniteDimensional ℚ ((Nat.Primes →₀ ℚ) ⧸
      relationSpan (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)))) := by
  rw [relationSpan_primeLog_eq_bot]
  exact not_finiteDimensional_quotient_bot

end GaloisForLFunctions.HTGeometry
