import GaloisForLFunctions.HTGeometry.CofinalRecurrentPrimeValuationMaster

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A fixed enumeration of the prime subtype. Existence follows from countability and infinitude;
no mathematical statement below depends on which enumeration is selected. -/
noncomputable def chosenPrimeEnumerationEquiv : ℕ ≃ Nat.Primes :=
  Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))

/-- Repeat every term of a countable profile on an infinite prime fibre. -/
def infinitelyRepeatedPrimeProfile {V : Type*}
    (e : ℕ ≃ Nat.Primes) (y : ℕ → V) (p : Nat.Primes) : V :=
  y (Nat.unpair (e.symm p)).1

/-- Every prescribed profile value has an infinite prime fibre in the repeated construction. -/
theorem infinitelyRepeatedPrimeProfile_fiber_infinite {V : Type*}
    (e : ℕ ≃ Nat.Primes) (y : ℕ → V) (n : ℕ) :
    {p | infinitelyRepeatedPrimeProfile e y p = y n}.Infinite := by
  let f : ℕ → Nat.Primes := fun m => e (Nat.pair n m)
  have hf : Function.Injective f := by
    intro a b hab
    have hright := congrArg (fun p => (Nat.unpair (e.symm p)).2) hab
    simpa [f, Nat.unpair_pair] using hright
  apply (Set.infinite_range_of_injective hf).mono
  intro p hp
  obtain ⟨m, rfl⟩ := hp
  simp [f, infinitelyRepeatedPrimeProfile, Nat.unpair_pair]

/-- The recurrent locus of the repeated prime profile is exactly the range of the prescribed
countable geometry. -/
theorem recurringValueSet_infinitelyRepeatedPrimeProfile {V : Type*}
    (e : ℕ ≃ Nat.Primes) (y : ℕ → V) :
    recurringValueSet (infinitelyRepeatedPrimeProfile e y) = Set.range y := by
  apply Set.Subset.antisymm
  · intro v hv
    obtain ⟨p, rfl⟩ := recurringValueSet_subset_range
      (infinitelyRepeatedPrimeProfile e y) hv
    exact ⟨(Nat.unpair (e.symm p)).1, rfl⟩
  · intro v hv
    obtain ⟨n, rfl⟩ := hv
    exact infinitelyRepeatedPrimeProfile_fiber_infinite e y n

/-- Every countable profile geometry has a prime realization with no nonrecurrent primes. -/
theorem infinitelyRepeatedPrimeProfile_cofinitelyRecurring {V : Type*}
    (e : ℕ ≃ Nat.Primes) (y : ℕ → V) :
    CofinitelyRecurring (infinitelyRepeatedPrimeProfile e y) := by
  rw [CofinitelyRecurring]
  have hempty :
      {p | infinitelyRepeatedPrimeProfile e y p ∉
        recurringValueSet (infinitelyRepeatedPrimeProfile e y)} = ∅ := by
    ext p
    rw [recurringValueSet_infinitelyRepeatedPrimeProfile e y]
    simp [infinitelyRepeatedPrimeProfile]
  rw [hempty]
  exact Set.finite_empty

end

end GaloisForLFunctions.HTGeometry
