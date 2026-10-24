import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HeatConeEvolution
import GaloisForLFunctions.HTGeometry.HermitePerturbationRealRoots

/-!
# Unit Gaussian normalization of polynomial heat

Backward heat at time one half sends a monomial to the probabilists' Hermite polynomial.
The finite heat semigroup gives the inverse identity. These normalizations allow root
obstructions to be expressed in the same units as the coefficient cone.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The Gaussian inverse heat of a monomial is its probabilists' Hermite polynomial. -/
theorem forwardPolyHeat_neg_half_X_pow (n : ℕ) :
    forwardPolyHeat (-1 / 2) (X ^ n) = hermiteReal n := by
  induction n with
  | zero => norm_num [hermiteReal, forwardPolyHeat_one]
  | succ n ih =>
    rw [pow_succ', forwardPolyHeat_X_mul, ih, hermiteReal_succ]
    norm_num [gaussShift]

/-- Forward Gaussian heat removes the Hermite correction exactly. -/
theorem forwardPolyHeat_half_hermite (n : ℕ) :
    forwardPolyHeat (1 / 2) (hermiteReal n) = X ^ n := by
  rw [← forwardPolyHeat_neg_half_X_pow, forwardPolyHeat_comp,
    show (1 / 2 : ℝ) + (-1 / 2) = 0 by ring, forwardPolyHeat_zero]

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
