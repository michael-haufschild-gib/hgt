import GaloisForLFunctions.HTGeometry.NonautonomousFirstOrderTailSymbol

/-!
# The universal twelve-charge of scalar parabolic orbifold tails

The complete finite-order tail classification leaves exactly the six parabolic orbifold
signatures on the sphere.  Their finite cone holonomy orders divide `12`.  Consequently the
translation-invariant current on the affine universal cover always has a rational twelfth tensor
power downstairs, independently of which parabolic signature occurs at a phase.

This file records the classification surface and its universal charge without introducing a flow
or a numerical experiment.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every finite rotational order occurring in a parabolic orbifold divides the universal tensor
charge `12`.  Explicit witnesses are used rather than a numerical search. -/
theorem parabolicHolonomyOrder_dvd_twelve (order : ℕ)
    (horder : order = 1 ∨ order = 2 ∨ order = 3 ∨ order = 4 ∨ order = 6) :
    order ∣ 12 := by
  rcases horder with h | h | h | h | h
  · subst order
    exact ⟨12, rfl⟩
  · subst order
    exact ⟨6, rfl⟩
  · subst order
    exact ⟨4, rfl⟩
  · subst order
    exact ⟨3, rfl⟩
  · subst order
    exact ⟨2, rfl⟩

/-- The six zero-Euler orbifold signatures with underlying Riemann sphere. -/
inductive ParabolicSphereSignature where
  | twoCusps
  | twoTwosCusp
  | fourTwos
  | twoThreeSix
  | twoFourFour
  | threeThrees
  deriving DecidableEq

/-- Finite cone orders of a parabolic sphere signature; cusps are recorded separately. -/
def ParabolicSphereSignature.finiteConeOrders : ParabolicSphereSignature → List ℕ
  | .twoCusps => []
  | .twoTwosCusp => [2, 2]
  | .fourTwos => [2, 2, 2, 2]
  | .twoThreeSix => [2, 3, 6]
  | .twoFourFour => [2, 4, 4]
  | .threeThrees => [3, 3, 3]

/-- Number of punctures of a parabolic sphere signature. -/
def ParabolicSphereSignature.cuspCount : ParabolicSphereSignature → ℕ
  | .twoCusps => 2
  | .twoTwosCusp => 1
  | .fourTwos | .twoThreeSix | .twoFourFour | .threeThrees => 0

/-- Every finite local holonomy order on a parabolic sphere divides the universal charge `12`. -/
theorem ParabolicSphereSignature.coneOrder_dvd_twelve
    (signature : ParabolicSphereSignature) (order : ℕ)
    (horder : order ∈ signature.finiteConeOrders) :
    order ∣ 12 := by
  apply parabolicHolonomyOrder_dvd_twelve
  cases signature <;> simp [ParabolicSphereSignature.finiteConeOrders] at horder ⊢
  all_goals omega

/-- A single tensor charge works simultaneously for any phasewise choice of parabolic signature. -/
theorem parabolicSphereTower_has_universal_twelve_charge
    (signature : ℕ → ParabolicSphereSignature) :
    ∀ i order, order ∈ (signature i).finiteConeOrders → order ∣ 12 := by
  intro i order horder
  exact (signature i).coneOrder_dvd_twelve order horder

end GaloisForLFunctions.HTGeometry
