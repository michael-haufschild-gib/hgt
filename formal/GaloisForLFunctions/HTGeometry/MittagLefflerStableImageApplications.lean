import GaloisForLFunctions.HTGeometry.ShilovStableImage

/-!
# A concrete algebraic Mittag-Leffler tower

The constant tower of complex vector spaces with zero bonds is a closed
instance of the stable-image form of the Mittag-Leffler theorem.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Constant complex vector-space tower used for the zero-bond example. -/
abbrev complexZeroTower : ℕ → Type := fun _ => ℂ

/-- Every transition in the concrete tower is zero. -/
def complexZeroBond : ∀ n, complexZeroTower (n + 1) →ₗ[ℂ] complexZeroTower n := fun _ => 0

/-- The concrete zero-bond tower satisfies the algebraic Mittag-Leffler condition. -/
theorem complexZeroBond_hasStableImages :
    BoundaryMigration.HasStableImages complexZeroBond :=
  BoundaryMigration.hasStableImages_of_zero_bond complexZeroBond (fun _ => rfl)

/-- The Roos difference is onto for the concrete Mittag-Leffler tower. -/
theorem complexZeroBond_inverseDifference_surjective :
    Function.Surjective (BoundaryMigration.inverseDifference complexZeroTower complexZeroBond) :=
  BoundaryMigration.inverseDifference_surjective_of_hasStableImages complexZeroBond
    complexZeroBond_hasStableImages

/-- The derived inverse-limit obstruction vanishes for the concrete zero-bond tower. -/
theorem complexZeroBond_derivedLimitOne_subsingleton :
    Subsingleton (BoundaryMigration.DerivedLimitOne complexZeroTower complexZeroBond) :=
  BoundaryMigration.derivedLimitOne_subsingleton_of_hasStableImages complexZeroBond
    complexZeroBond_hasStableImages

end GaloisForLFunctions.HTGeometry
