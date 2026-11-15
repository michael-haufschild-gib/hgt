import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.AffineMomentConnected
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Exact connected-component counts of affine moment loci

An affine paired moment locus has one connected component when its equations
are compatible and zero otherwise. This holds for arbitrary equation families
in finitely many paired coordinates. The native `ConnectedComponents` quotient
is used, and compatibility is decided by the established linear relations.

At a specified linear relation space and affine level, compatibility is
automatic, so the connected-component count is always one, even when the
locus has many irreducible components.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical

/-- A nonempty connected subset has exactly one native connected component. -/
private theorem card_components_of_isConnected {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsConnected s) : Nat.card (ConnectedComponents s) = 1 := by
  letI : ConnectedSpace s := isConnected_iff_connectedSpace.mp hs
  exact Nat.card_unique

/-- The empty subspace has no native connected components. -/
private theorem card_components_empty (X : Type*) [TopologicalSpace X] :
    Nat.card (ConnectedComponents (∅ : Set X)) = 0 := by
  letI : IsEmpty (ConnectedComponents (∅ : Set X)) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  exact Nat.card_of_isEmpty

variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- Every affine moment level has exactly one native connected component. -/
theorem card_affinePaired_connectedComponents (L : Submodule K (ι → K)) (ℓ : L →ₗ[K] K) :
    Nat.card (ConnectedComponents (PrimeSpectrum.zeroLocus
      (((affineMomentIdeal K L ℓ).map (invariantSubstitution K)) :
        Set (MvPolynomial (ι ⊕ ι) K)))) = 1 :=
  card_components_of_isConnected (affinePairedZeroLocus_isConnected K L ℓ)

namespace AffineMomentSystem
variable {α : Type*}

/-- Arbitrary affine paired equation families have one component exactly when compatible. -/
theorem card_pairedConnectedComponents (a : α → ι → K) (b : α → K) :
    Nat.card (ConnectedComponents (PrimeSpectrum.zeroLocus
      (((ideal K a b).map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K)))) =
      if Compatible K a b then 1 else 0 := by
  by_cases hc : Compatible K a b
  · rw [if_pos hc]
    exact card_components_of_isConnected ((pairedZeroLocus_isConnected_iff K a b).mpr hc)
  · rw [if_neg hc, (pairedZeroLocus_eq_empty_iff K a b).mpr hc]
    exact card_components_empty _

end AffineMomentSystem
end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.card_affinePaired_connectedComponents
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.AffineMomentSystem.card_pairedConnectedComponents
