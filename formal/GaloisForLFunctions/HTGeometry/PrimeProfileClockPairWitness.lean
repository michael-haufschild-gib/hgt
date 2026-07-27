import GaloisForLFunctions.HTGeometry.PrimeClockUniformAnnihilatorInverseLimit

/-!
# Clock independence and prime-power support, together

The prime-profile layer consumes `PrimeProfileClockIndependent g` — linear independence of the whole
clock jet family — together with `PrimeProfileSupportedOnPositivePrimePowers` on the sources.  Both
hold for the explicit unit source, but the independence half exists only inside the proof of the
Kolchin fracture, as an anonymous `show`, so nothing in the corpus states it and nothing else can use
it.

Naming it makes the pair jointly realized on record.

* **`primeClockUnitSource_clockIndependent`**;
* **`exists_clockIndependent_supportedOnPositivePrimePowers`**.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The unit source has an independent clock orbit.**  Its polynomial clock orbit is linearly
independent, and over a one-element index the jet family is that orbit reindexed. -/
theorem primeClockUnitSource_clockIndependent :
    PrimeProfileClockIndependent (fun _ : Unit => primeClockUnitSource) := by
  simpa [PrimeProfileClockIndependent, primeProfileClockJetFamily] using
    primeClockUnitSource_clockOrbit_linearIndependent.comp
      (fun ik : Unit × Nat => ik.2)
      (by
        rintro ⟨u, m⟩ ⟨v, n⟩ h
        exact Prod.ext (Subsingleton.elim _ _) h)

/-- **Joint realization.**  A clock-independent source family all of whose members are supported on
positive prime powers exists. -/
theorem exists_clockIndependent_supportedOnPositivePrimePowers :
    ∃ (I : Type) (g : I → ArithmeticFunction ℂ),
      PrimeProfileClockIndependent g ∧
        ∀ i, PrimeProfileSupportedOnPositivePrimePowers (g i) :=
  ⟨Unit, fun _ => primeClockUnitSource, primeClockUnitSource_clockIndependent,
    fun _ => primeClockUnitSource_supportedOnPositivePrimePowers⟩

end GaloisForLFunctions.HTGeometry
