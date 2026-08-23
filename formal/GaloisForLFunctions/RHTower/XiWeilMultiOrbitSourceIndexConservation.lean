import GaloisForLFunctions.RHTower.XiWeilMultiOrbitSourceInertia
import GaloisForLFunctions.RHTower.XiWeilNegativeIndexConservation

/-!
# Free-orbit charge of explicit Xi source packets

The reflected Gram of separated continued-Cauchy prime--Gamma packets is the multiplicity-exact
Xi Hilbert Gram.  Therefore a strictly negative `k`-packet source block cannot be an approximation
artifact: it forces `k` pairwise disjoint free critical-line-reflection orbits on Xi divisor copies.
-/

namespace RHTower

open scoped BigOperators ComplexConjugate
open Complex Matrix

noncomputable section

/-- Source-packet Gram is literally the reflected Xi Hilbert Gram of packet evaluations. -/
theorem xiSeparatedPacketWeilGram_eq_xiWeilHilbertGram
    {k : ℕ} (P : Fin k → XiSeparatedContinuedCauchyPacket) :
    xiSeparatedPacketWeilGram P =
      xiWeilHilbertGram (fun j => (P j).evaluation) := by
  rfl

/-- Every strictly negative explicit separated-source block exposes the same number of disjoint
free multiplicity-copy Xi reflection orbits. -/
theorem exists_xiZeroCopy_freeOrbitPacket_of_xiSeparatedPacketWeilGram_negDef
    {k : ℕ} (P : Fin k → XiSeparatedContinuedCauchyPacket)
    (hneg : ∀ x : Fin k → ℂ, x ≠ 0 →
      (star x ⬝ᵥ (xiSeparatedPacketWeilGram P).mulVec x).re < 0) :
    ∃ (e : Fin k → XiZeroCopy) (Q : Matrix (Fin k) (Fin k) ℂ),
      Function.Injective e ∧
      (∀ r s, xiZeroCopyLineConjEquiv (e r) ≠ e s) ∧
      IsUnit Q.det ∧
      ∀ r s, Q r s = xiWeilAntiPart ((P s).evaluation) (e r) := by
  apply exists_xiZeroCopy_freeOrbitPacket_of_hilbertGram_negDef
    (fun j => (P j).evaluation)
  simpa [xiSeparatedPacketWeilGram_eq_xiWeilHilbertGram] using hneg

end

end RHTower
