import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.BinaryArtinSchreier
import GaloisForLFunctions.HTGeometry.Topology.ClopenComponentSubsets
import GaloisForLFunctions.HTGeometry.Topology.NoetherianComponents
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Artin–Schreier fibres counted by connected components

For every Noetherian binary algebra, Artin–Schreier kernel elements correspond
to subsets of the connected-component space of its spectrum. The kernel has
`2^c` elements, where `c` is the number of connected components. Translation
identifies every nonempty fibre with the kernel, giving the exact solution
count `0` or `2^c`, including nonreduced and zero algebras.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open Classical
open TopologicalSpace
open GaloisForLFunctions.HTGeometry
attribute [local instance] NoetherianComponents.connectedComponents_discrete
attribute [local instance] NoetherianComponents.connectedComponents_finite
variable (A : Type*) [CommRing A] [Algebra (ZMod 2) A] [IsNoetherianRing A]

/-- Kernel elements of binary Artin–Schreier are exactly choices of connected
components of the spectrum. This also includes nonreduced and zero algebras. -/
def binaryArtinSchreierKernelComponentSubsetEquiv :
    (binaryArtinSchreier A).ker ≃ Set (ConnectedComponents (PrimeSpectrum A)) :=
  (binaryArtinSchreierKernelEquivIdempotents A).trans
    (PrimeSpectrum.isIdempotentElemEquivClopens.toEquiv.trans
      (ClopenComponents.clopenComponentSubsetEquiv (PrimeSpectrum A)))

/-- Each connected component contributes one independent binary kernel choice. -/
theorem card_binaryArtinSchreier_kernel :
    Nat.card (binaryArtinSchreier A).ker =
      2 ^ Nat.card (ConnectedComponents (PrimeSpectrum A)) := by
  letI := Fintype.ofFinite (ConnectedComponents (PrimeSpectrum A))
  rw [Nat.card_congr (binaryArtinSchreierKernelComponentSubsetEquiv A),
    Nat.card_eq_fintype_card, Fintype.card_set, Nat.card_eq_fintype_card]

/-- Every nonempty Artin–Schreier fibre has one binary choice per connected component. -/
theorem card_binaryArtinSchreier_fibre (x : A) :
    Nat.card {y : A // binaryArtinSchreier A y = binaryArtinSchreier A x} =
      2 ^ Nat.card (ConnectedComponents (PrimeSpectrum A)) :=
  (Nat.card_congr (binaryArtinSchreierFibreEquivKernel A x)).trans
    (card_binaryArtinSchreier_kernel A)

/-- The exact solution count is zero for an insoluble equation and a power of two
controlled by the spectrum otherwise. -/
theorem card_binaryArtinSchreier_solutions (a : A) :
    Nat.card {x : A // binaryArtinSchreier A x = a} =
      if ∃ x : A, binaryArtinSchreier A x = a then
        2 ^ Nat.card (ConnectedComponents (PrimeSpectrum A)) else 0 := by
  classical
  split_ifs with h
  · obtain ⟨x, rfl⟩ := h
    exact card_binaryArtinSchreier_fibre A x
  · haveI : IsEmpty {x : A // binaryArtinSchreier A x = a} :=
      ⟨fun x => h ⟨x.1, x.2⟩⟩
    exact Nat.card_of_isEmpty

#print axioms binaryArtinSchreierKernelComponentSubsetEquiv
#print axioms card_binaryArtinSchreier_kernel
#print axioms card_binaryArtinSchreier_fibre
#print axioms card_binaryArtinSchreier_solutions
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
