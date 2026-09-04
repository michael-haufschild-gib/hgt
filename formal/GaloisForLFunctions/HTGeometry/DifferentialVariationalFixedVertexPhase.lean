import GaloisForLFunctions.HTGeometry.DifferentialVariationalBoundedOrbitFixedVertex
import GaloisForLFunctions.HTGeometry.DifferentialVariationalPhaseNecessary
import GaloisForLFunctions.HTGeometry.FreeDifferentialBoundedOrbit

/-!
# Exact bounded-orbit/fixed-vertex phase

The canonical variational action has a bounded Euclidean vertex orbit exactly when it fixes a
projective completed-lattice vertex.  On a free finite-rank differential field this is also exactly
boundedness of all iterate reconstruction orders.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Bounded orbit and existence of a fixed projective lattice vertex are equivalent. -/
theorem differentialVariationalEuclideanOrbitBounded_iff_hasFixedVertex
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (sigma : DifferentialFieldAut C K) :
    DifferentialVariationalEuclideanOrbitBounded b x sigma ↔
      DifferentialVariationalHasFixedVertex b sigma :=
  ⟨differentialVariationalEuclideanOrbitBounded_implies_hasFixedVertex b x sigma,
    differentialVariationalHasFixedVertex_implies_orbitBounded b x sigma⟩

namespace DifferentialFieldAut

variable {C : Type*} [Field C] [CharZero C] {r : ℕ}

/-- On a free finite-rank differential field, bounded reconstruction order is exactly the
fixed-projective-lattice phase. -/
theorem freeDifferentialOrderPowersBounded_iff_hasFixedVertex
    (sigma : FreeAut (C := C) (ι := Fin (r + 1))) :
    FreeDifferentialOrderPowersBounded sigma ↔
      DifferentialVariationalHasFixedVertex
        (freeVariationalOreBasis (C := C) (r := r + 1)) sigma := by
  rw [← freeDifferentialEuclideanOrbitBounded_iff_orderPowersBounded]
  exact differentialVariationalEuclideanOrbitBounded_iff_hasFixedVertex
    (freeVariationalOreBasis (C := C) (r := r + 1))
    (freeDifferentialProjectiveBasePoint (C := C) (r + 1)) sigma

end DifferentialFieldAut

end

end GaloisForLFunctions.HTGeometry
