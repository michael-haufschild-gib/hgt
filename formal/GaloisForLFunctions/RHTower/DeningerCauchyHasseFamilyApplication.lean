import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.DeningerCauchyHasse

/-!
# Cauchy descent Hasse family

Descended local boundary quotients give a common place-indexed interface for Cauchy cohomology.
When simultaneous local boundary membership classifies the global boundary, the complete local
profile separates global cohomology classes.
-/

namespace RHTower

noncomputable section

variable {R V W iota : Type*}
variable [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- Descended local boundary quotients form a Hasse family whenever simultaneous local boundary
membership classifies the global boundary. -/
def deningerCauchyQuotientHasseFamily
    (globalBoundaries : Submodule R V)
    (localBoundaries : Submodule R W)
    (restriction : iota → V →ₗ[R] W)
    (hboundary : ∀ (i : iota) (x : V), x ∈ globalBoundaries →
      restriction i x ∈ localBoundaries)
    (hclass : ∀ x : V, (∀ i : iota, restriction i x ∈ localBoundaries) →
      x ∈ globalBoundaries) :
    GaloisForLFunctions.HTGeometry.HasseFamily (V ⧸ globalBoundaries) iota where
  Local := fun _ => W ⧸ localBoundaries
  profile := deningerCauchySimultaneousRestriction
    globalBoundaries localBoundaries restriction hboundary
  profile_injective := deningerCauchySimultaneousRestriction_injective
    globalBoundaries localBoundaries restriction hboundary hclass

end
end RHTower
