/- Adapted from OpenAI/math (MIT license), commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Source: lean/OAI/AlgebraicGeometry/StableCoordinate/NonCoordinate.lean -/

import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoordinateToQuadric
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LiftObstruction
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.Rigidity

namespace GaloisForLFunctions.HTGeometry

/-!
# The exact polynomial is not a coordinate in four variables

The sole temporary hypothesis is that the literal polynomial `f` is sent to
the first variable by a complex algebra automorphism.  The proved separated
filtration and associated-graded construction then produce a nonzero locally
nilpotent derivation on the actual quadric with a nonzero invariant in its
center ideal.  The proved normalized determinant lift carries this to a
nonzero weight-preserving locally nilpotent derivation annihilating `v`, in
contradiction with the proved rigidity theorem.  No auxiliary construction
or existence hypothesis remains in this statement.
-/

namespace StableCoordinate

/-- No complex algebra automorphism of the four-variable polynomial ring
sends the specified degree-five polynomial to the first variable. -/
theorem f_not_coordinate : ¬ IsCoordinate (by decide : 0 < 4) f := by
  intro hf
  obtain ⟨E, hE, hE0, hInv⟩ := CoordinateToQuadric.f_coordinate_produces_quadric_lnd hf
  exact Obstruction.no_nonzero_lnd_preserving_fiber_weights_killing_v ℂ
    (Obstruction.exists_nonzero_weight_preserving_lnd_killing_v E hE hE0 hInv)

end StableCoordinate

end GaloisForLFunctions.HTGeometry
