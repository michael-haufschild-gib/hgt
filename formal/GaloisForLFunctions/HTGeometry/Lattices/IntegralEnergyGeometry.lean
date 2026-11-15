import GaloisForLFunctions.HTGeometry.Lattices.IntegralZeroSumEnergy
import GaloisForLFunctions.HTGeometry.SchwartzPoissonSummation

/-!
# Integral energy in Euclidean coordinates

The existing Euclidean integer embedding converts integral coordinate energy
into squared Euclidean distance. This identifies algebraic minimum-norm bounds
with geometric separation bounds.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
variable {ι : Type*} [Fintype ι]

/-- Squared distance between integral points is the integer energy of their difference. -/
theorem euclideanIntegerPoint_dist_sq (x y : ι → ℤ) :
    dist (euclideanIntegerPoint x) (euclideanIntegerPoint y)^2 =
      (IntegralZeroSum.energy (x - y) : ℝ) := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [euclideanIntegerPoint, integerPoint, IntegralZeroSum.energy]

#print axioms euclideanIntegerPoint_dist_sq
end GaloisForLFunctions.HTGeometry.IntegerLatticePoisson
