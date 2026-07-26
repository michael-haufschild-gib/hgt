import GaloisForLFunctions.HTGeometry.GammaPhaseCompletion
import GaloisForLFunctions.HTGeometry.GammaOrientedAlienCharge

/-!
# Degenerate realizations of the projective-boundary and alien-charge interfaces

The empty coefficient class has no nonzero family, so it satisfies the projective-boundary interface;
and an empty family of gamma factors carries no alien charge.  Both interfaces are therefore
consistent, their substantive content being the nondegenerate Montel-type statement and the exact
charge cancellation respectively.
-/

namespace GaloisForLFunctions.HTGeometry

theorem hasPolynomialFunctionalProjectiveBoundary_empty :
    HasPolynomialFunctionalProjectiveBoundary (∅ : Set (ℂ → ℂ)) := by
  intro r a haK ha S hS
  obtain ⟨j, _⟩ := ha
  exact absurd (haK j) (Set.notMem_empty _)

theorem orientedGammaAlienChargeZero_empty (a : Fin 0 → OrientedAffineGammaFactor) :
    OrientedGammaAlienChargeZero a := by
  intro t _
  simp [scaledGammaAlienChargeAt]

end GaloisForLFunctions.HTGeometry
