import GaloisForLFunctions.HTGeometry.Octonion.ComplexSliceCover

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- The global pull-back resolvent set in the one-dimensional octonion example. -/
def leftMultiplicationPullbackResolventSet (q : RealOctonion) : Set RealOctonion :=
  ⋃ J : ImaginaryUnit, leftMultiplicationPullbackSliceResolventSet q J

/-- The global pull-back spectrum in the one-dimensional octonion example. -/
def leftMultiplicationPullbackSpectrum (q : RealOctonion) : Set RealOctonion :=
  (leftMultiplicationPullbackResolventSet q)ᶜ

/-- The pull-back resolvent set of left multiplication is the complement of the
conjugacy sphere. -/
theorem mem_leftMultiplicationPullbackResolventSet_iff
    (s q : RealOctonion) :
    s ∈ leftMultiplicationPullbackResolventSet q ↔ s ∉ conjugacySphere q := by
  change (s ∈ ⋃ J : ImaginaryUnit, leftMultiplicationPullbackSliceResolventSet q J) ↔
    s ∉ conjugacySphere q
  constructor
  · intro hmem
    obtain ⟨J, hs⟩ := Set.mem_iUnion.mp hmem
    rw [leftMultiplicationPullbackSliceResolventSet_eq] at hs
    exact hs.2
  · intro hnot
    obtain ⟨J, hs⟩ := exists_complexSliceSubmodule_mem s
    refine Set.mem_iUnion.mpr ⟨J, ?_⟩
    rw [leftMultiplicationPullbackSliceResolventSet_eq]
    exact ⟨hs, hnot⟩

/-- Theorem 8.7: the global pull-back spectrum of left multiplication by `q` is
exactly the octonionic conjugacy sphere `[q]`. -/
theorem leftMultiplicationPullbackSpectrum_eq_conjugacySphere
    (q : RealOctonion) :
    leftMultiplicationPullbackSpectrum q = conjugacySphere q := by
  ext s
  change s ∉ leftMultiplicationPullbackResolventSet q ↔ s ∈ conjugacySphere q
  rw [mem_leftMultiplicationPullbackResolventSet_iff]
  simp

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
