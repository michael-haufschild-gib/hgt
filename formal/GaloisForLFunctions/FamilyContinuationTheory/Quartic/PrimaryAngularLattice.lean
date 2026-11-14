import GaloisForLFunctions.FamilyContinuationTheory.Quartic.GaussianPrimary
import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.GaussianAffineAngularBound

/-!
# Primary Gaussian angular lattice sums

The primary condition parametrizes exactly the affine lattice
`1 + (1+i)^3 ℤ[i]`. Its covolume is eight. Affine Poisson summation therefore
separates the exact density-one-eighth mean from a uniformly bounded remainder.
For nontrivial angular sectors the mean vanishes, leaving a bound independent
of the complex sampling scale.
-/

noncomputable section
open Complex RHTower.GaussianTwoSquares
open scoped Classical SchwartzMap FourierTransform

namespace GaloisForLFunctions.FamilyContinuationTheory.Quartic
open MetaplecticMobiusDescent.QuarticPoisson

/-- Gaussian integers congruent to one modulo the ramified cube. -/
abbrev PrimaryGaussian := {z : GaussianInt // IsPrimary z}

/-- Multiplication by the ramified cube, followed by translation by one. -/
def primaryLatticeParam (w : GaussianInt) : PrimaryGaussian :=
  ⟨onePlusI ^ 3 * w + 1, by
    change onePlusI ^ 3 ∣ (onePlusI ^ 3 * w + 1) - 1
    rw [add_sub_cancel_right]
    exact ⟨w, rfl⟩⟩

end GaloisForLFunctions.FamilyContinuationTheory.Quartic
