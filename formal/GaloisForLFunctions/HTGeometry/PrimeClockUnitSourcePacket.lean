import GaloisForLFunctions.HTGeometry.CofinitePacketCriterion
import GaloisForLFunctions.HTGeometry.PrimeProfileClockPairWitness

/-!
# The corpus's own source satisfies every prime-profile interface

The explicit unit source replicates the constant valuation profile `1` across all prime powers, so it
is nonzero at every prime.  The support criterion then hands it a cofinite jet packet, and with the
two properties already on record — clock independence and prime-power support — the source satisfies
all three interfaces of the prime-profile layer at once.

* `primeClockUnitSource_apply_of_isPrimePow`;
* **`cofinitePrimeProfileJetPacket_primeClockUnitSource`**;
* **`primeClockUnitSource_packet_clock_support`** — the three interfaces together.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The unit source is `1` at every prime power: its valuation profile is constantly `1`, so the
prime-power index is irrelevant. -/
theorem primeClockUnitSource_apply_of_isPrimePow {n : ℕ} (hn : IsPrimePow n) :
    primeClockUnitSource n = 1 := by
  show (if h : IsPrimePow n then
      primeClockUnitValuationProfile (Nat.Primes.prodNatEquiv.symm ⟨n, h⟩).2 else 0) = 1
  rw [dif_pos hn]
  rfl

/-- **The unit source has a cofinite jet packet.**  It is nonzero at every prime, so the support
criterion applies. -/
theorem cofinitePrimeProfileJetPacket_primeClockUnitSource :
    CofinitePrimeProfileJetPacket (fun _ : Unit => primeClockUnitSource) := by
  refine cofinitePrimeProfileJetPacket_of_infinite_prime_support ?_
  have huniv : {p : Nat.Primes | primeClockUnitSource (p : ℕ) ≠ 0} = Set.univ := by
    ext p
    simp [primeClockUnitSource_apply_of_isPrimePow p.2.isPrimePow]
  rw [huniv]
  exact Set.infinite_univ

/-- **All three prime-profile interfaces on one source.** -/
theorem primeClockUnitSource_packet_clock_support :
    CofinitePrimeProfileJetPacket (fun _ : Unit => primeClockUnitSource) ∧
      PrimeProfileClockIndependent (fun _ : Unit => primeClockUnitSource) ∧
      PrimeProfileSupportedOnPositivePrimePowers primeClockUnitSource :=
  ⟨cofinitePrimeProfileJetPacket_primeClockUnitSource, primeClockUnitSource_clockIndependent,
    primeClockUnitSource_supportedOnPositivePrimePowers⟩

end GaloisForLFunctions.HTGeometry
