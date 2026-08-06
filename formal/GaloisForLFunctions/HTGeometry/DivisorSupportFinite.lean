import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# The divisor of a rational function has finite support

A height-one prime containing a nonzero element of a domain is minimal over the principal ideal
that element generates, by Krull's height theorem: the principal ideal already has height at
least one, so no prime strictly between it and a height-one prime can exist.  In a Noetherian
ring there are only finitely many minimal primes over a fixed ideal, so a nonzero element vanishes
along only finitely many prime divisors, and so does a quotient of two of them.

This is the finiteness hypothesis of the eigenvolume ramification system, discharged: the
divisorial support of a rational form is finite.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A height-one prime containing a nonzero element is minimal over the ideal it generates. -/
theorem mem_minimalPrimes_span_of_height_eq_one
    {a : R} (ha : a ≠ 0) {p : Ideal R} [p.IsPrime] (hp : p.height = 1) (hap : a ∈ p) :
    p ∈ (Ideal.span {a}).minimalPrimes := by
  haveI : p.FiniteHeight := ⟨Or.inr (by rw [hp]; exact ENat.one_ne_top)⟩
  refine Ideal.mem_minimalPrimes_of_height_eq (Ideal.span_le.mpr ?_) ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hap
  · rw [hp]
    exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha)

variable [IsNoetherianRing R]

/-- **The zero locus of a nonzero element meets only finitely many prime divisors.** -/
theorem finite_heightOneSupport {a : R} (ha : a ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ a ∈ p}.Finite := by
  refine Set.Finite.subset (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a}))
    ?_
  rintro p ⟨hprime, hheight, hmem⟩
  exact mem_minimalPrimes_span_of_height_eq_one ha hheight hmem

/-- **The divisorial support of a rational form is finite.**  Writing the form as a quotient
`a / b`, its order can be nonzero only at prime divisors containing `a` or `b`. -/
theorem finite_heightOneSupport_frac {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) :
    {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ (a ∈ p ∨ b ∈ p)}.Finite := by
  refine Set.Finite.subset ((finite_heightOneSupport ha).union (finite_heightOneSupport hb)) ?_
  rintro p ⟨hprime, hheight, hmem | hmem⟩
  · exact Or.inl ⟨hprime, hheight, hmem⟩
  · exact Or.inr ⟨hprime, hheight, hmem⟩

omit [IsDomain R] [IsNoetherianRing R] in
/-- Away from the divisorial support of `a`, that element lies in no prime divisor of the
complement. -/
theorem notMem_of_notMem_heightOneSupport {a : R} {p : Ideal R} [p.IsPrime]
    (hp : p.height = 1) (h : p ∉ {q : Ideal R | q.IsPrime ∧ q.height = 1 ∧ a ∈ q}) :
    a ∉ p := by
  intro hmem
  exact h ⟨‹_›, hp, hmem⟩

end GaloisForLFunctions.HTGeometry
