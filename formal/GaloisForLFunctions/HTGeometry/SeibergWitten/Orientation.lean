import GaloisForLFunctions.HTGeometry.SeibergWitten.Geometry
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Globally oriented smooth four-manifolds

This module upgrades the prior choice of an orientation on the local model to an actual
atlas-compatible orientation datum.  For overlapping preferred charts, mathlib's
`tangentCoordChange` gives the derivative of their transition map.  The cocycle and identity laws
make this derivative a linear equivalence on the overlap.  An `OrientedSmoothFourAtlas` assigns an
orientation to every preferred coordinate frame and requires transport by that equivalence to
preserve it.

The closed flat model proves the interface is inhabited.  This is oriented-atlas infrastructure;
it does not construct a principal `Spinᶜ(4)` lift.
-/

noncomputable section

open scoped Manifold

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- The actual tangent-coordinate transition map is a linear equivalence on a chart overlap. -/
def fourTangentCoordChangeEquiv
    {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold fourModel 1 M]
    (x y z : M)
    (hxy : z ∈ (extChartAt fourModel x).source ∩ (extChartAt fourModel y).source) :
    FourSpace ≃ₗ[ℝ] FourSpace :=
  LinearEquiv.ofLinear (tangentCoordChange fourModel x y z).toLinearMap
    (tangentCoordChange fourModel y x z).toLinearMap
    (by
      apply LinearMap.ext
      intro v
      change tangentCoordChange fourModel x y z (tangentCoordChange fourModel y x z v) = v
      rw [tangentCoordChange_comp (I := fourModel)
        (w := y) (x := x) (y := y) (z := z)
        ⟨⟨hxy.2, hxy.1⟩, hxy.2⟩,
        tangentCoordChange_self (I := fourModel) hxy.2])
    (by
      apply LinearMap.ext
      intro v
      change tangentCoordChange fourModel y x z (tangentCoordChange fourModel x y z v) = v
      rw [tangentCoordChange_comp (I := fourModel)
        (w := x) (x := y) (y := x) (z := z)
        ⟨⟨hxy.1, hxy.2⟩, hxy.1⟩,
        tangentCoordChange_self (I := fourModel) hxy.1])

/-- A smooth four-manifold with orientations on preferred coordinate frames compatible on every
chart overlap. -/
structure OrientedSmoothFourAtlas
    (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] [SmoothFourManifold M] where
  coordinateOrientation : M → Orientation ℝ FourSpace (Fin 4)
  transition_preserves : ∀ x y z
    (hxy : z ∈ (extChartAt fourModel x).source ∩ (extChartAt fourModel y).source),
    Orientation.map (Fin 4) (fourTangentCoordChangeEquiv x y z hxy)
      (coordinateOrientation x) = coordinateOrientation y

/-- On the flat model, every actual tangent-coordinate transition is the identity. -/
theorem fourTangentCoordChangeEquiv_flat_eq_refl
    (x y z : FourSpace)
    (hxy : z ∈ (extChartAt fourModel x).source ∩ (extChartAt fourModel y).source) :
    fourTangentCoordChangeEquiv x y z hxy = LinearEquiv.refl ℝ FourSpace := by
  apply LinearEquiv.ext
  intro v
  change (tangentBundleCore fourModel FourSpace).coordChange
    (achart FourSpace x) (achart FourSpace y) z v = v
  rw [tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_apply]

local instance flatFourSpace_smooth : SmoothFourManifold FourSpace :=
  ⟨flatFourSpace_isSmooth⟩

/-- Closed globally orientation-compatible atlas on real Euclidean four-space. -/
noncomputable def flatOrientedSmoothFourAtlas : OrientedSmoothFourAtlas FourSpace where
  coordinateOrientation := fun _ => flatFourSpaceOrientation
  transition_preserves := by
    intro x y z hxy
    rw [fourTangentCoordChangeEquiv_flat_eq_refl x y z hxy]
    simp

end GaloisForLFunctions.HTGeometry.SeibergWitten
