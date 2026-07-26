import GaloisForLFunctions.HTGeometry.ExponentZeroEulerGaugeReflectionTransversal

/-!
# Realizations of the gauge-separated reflection-class interface

Gauge separation is a subsingleton condition on gauge fibres, so it holds for the empty class and for
every singleton class.  These are the extreme transversals of the exponent-zero gauge action.
-/

namespace GaloisForLFunctions.HTGeometry

theorem exponentZeroGaugeSeparatedReflectionClass_empty :
    ExponentZeroGaugeSeparatedReflectionClass (∅ : Set (PrimePhase Nat.Primes)) := by
  intro eta heta
  exact absurd heta (Set.notMem_empty eta)

theorem exponentZeroGaugeSeparatedReflectionClass_singleton
    (eta : PrimePhase Nat.Primes) :
    ExponentZeroGaugeSeparatedReflectionClass ({eta} : Set (PrimePhase Nat.Primes)) := by
  intro a ha b hb _
  rw [Set.mem_singleton_iff] at ha hb
  rw [ha, hb]

end GaloisForLFunctions.HTGeometry
