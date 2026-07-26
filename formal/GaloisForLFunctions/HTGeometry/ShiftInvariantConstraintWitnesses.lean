import GaloisForLFunctions.HTGeometry.IsodivisorialPrimeWalshStoneSaturation

/-!
# Realizations of the shift-invariant Boolean constraint interface

Shift invariance holds for the empty and full constraint sets and for the singleton carrying a
constant orientation pattern, since every tail of a constant sequence is that sequence.  The
singleton is closed and contains the all-positive pattern, so the sparse-constraint prime-tail
theorem applies to it with no interface premise.
-/

namespace GaloisForLFunctions.HTGeometry

theorem closedBooleanConstraintShiftInvariant_univ :
    ClosedBooleanConstraintShiftInvariant (Set.univ : Set (ℕ → Bool)) :=
  fun _ _ _ => Set.mem_univ _

theorem closedBooleanConstraintShiftInvariant_empty :
    ClosedBooleanConstraintShiftInvariant (∅ : Set (ℕ → Bool)) := by
  intro x hx
  exact absurd hx (Set.notMem_empty x)

/-- Every tail of a constant orientation pattern is that pattern. -/
theorem closedBooleanConstraintShiftInvariant_singleton_const (b : Bool) :
    ClosedBooleanConstraintShiftInvariant ({fun _ => b} : Set (ℕ → Bool)) := by
  intro x hx m
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rfl

/-- **Sparse constraint prime-tail invariance for the all-positive singleton.**  The interface
premises of the sparse-constraint theorem are all met by the singleton constraint carrying the
all-positive orientation pattern. -/
theorem sparseClosedConstraint_primeTailShiftInvariant_singleton (pi : ℕ ≃ Nat.Primes) :
    PrimeTailShiftInvariant pi
      (sparseClosedConstraintPrimeOrientation
        ({allPositiveOrientationPattern} : Set (ℕ → Bool))) := by
  haveI : Nonempty ({allPositiveOrientationPattern} : Set (ℕ → Bool)) :=
    ⟨⟨allPositiveOrientationPattern, rfl⟩⟩
  exact sparseClosedConstraint_primeTailShiftInvariant pi _ isClosed_singleton rfl
    (closedBooleanConstraintShiftInvariant_singleton_const false)

end GaloisForLFunctions.HTGeometry
