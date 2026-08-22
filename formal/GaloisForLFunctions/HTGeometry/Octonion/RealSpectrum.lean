import GaloisForLFunctions.HTGeometry.Octonion.ComplexSlice
import GaloisForLFunctions.HTGeometry.Octonion.Sylvester

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The real-linear resolvent set of left multiplication by `q`. -/
def leftMultiplicationRealResolventSet (q : RealOctonion) : Set RealOctonion :=
  {s | Function.Bijective (sylvesterDifferenceLinear s q)}

/-- The real-linear spectrum of left multiplication by `q`. -/
def leftMultiplicationRealSpectrum (q : RealOctonion) : Set RealOctonion :=
  (leftMultiplicationRealResolventSet q)ᶜ

/-- The real-linear resolvent set of left multiplication is the complement of the
conjugacy sphere.  This is the algebraic core of Theorem 8.7. -/
theorem mem_leftMultiplicationRealResolventSet_iff
    (s q : RealOctonion) :
    s ∈ leftMultiplicationRealResolventSet q ↔ s ∉ conjugacySphere q := by
  exact sylvesterDifferenceLinear_bijective_iff_not_mem_conjugacySphere s q

/-- The real-linear spectrum of left multiplication is exactly its conjugacy sphere. -/
theorem leftMultiplicationRealSpectrum_eq_conjugacySphere
    (q : RealOctonion) :
    leftMultiplicationRealSpectrum q = conjugacySphere q := by
  ext s
  change s ∉ leftMultiplicationRealResolventSet q ↔ s ∈ conjugacySphere q
  rw [mem_leftMultiplicationRealResolventSet_iff]
  simp

/-- The fixed-slice form of the real resolvent set used in the proof of Theorem 8.7. -/
def leftMultiplicationRealSliceResolventSet
    (q : RealOctonion) (J : ImaginaryUnit) : Set RealOctonion :=
  complexSliceSubmodule J ∩ leftMultiplicationRealResolventSet q

/-- On every complex slice, the real resolvent set is precisely the complement of
the conjugacy sphere within that slice. -/
theorem leftMultiplicationRealSliceResolventSet_eq
    (q : RealOctonion) (J : ImaginaryUnit) :
    leftMultiplicationRealSliceResolventSet q J =
      (complexSliceSubmodule J : Set RealOctonion) \ conjugacySphere q := by
  ext s
  change (s ∈ complexSliceSubmodule J ∧ s ∈ leftMultiplicationRealResolventSet q) ↔
    (s ∈ complexSliceSubmodule J ∧ s ∉ conjugacySphere q)
  exact and_congr Iff.rfl (mem_leftMultiplicationRealResolventSet_iff s q)

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
