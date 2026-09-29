import GaloisForLFunctions.HTGeometry.CompactPoissonGreen
import GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration

/-!
# Endpoint dressing of the compact geometric Green inverse

The smooth compact mean-zero Poisson solver supplies both operator inverse
identities. Receiver and source linear equivalences supply the gain inverses.
Keeping this consumer adapter separate preserves the geometry-only dependency
chain of `CompactPoissonGreen`.
-/

noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
namespace HTGeometry.CompactPoissonGreen
open DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [CompactSpace M]
  [NeZero (Module.finrank ℝ E)] [ConnectedSpace M]

open GaloisForLFunctions.HTGeometry in
/-- Geometric Poisson solvability discharges both inverse premises for endpoint dressing. -/
theorem endpointDressedGreen_isTwoSided (g : SmoothRiemannianMetric I M)
    (receiver source : meanZero g ≃ₗ[ℝ] meanZero g) :
    endpointDressedInverse source.symm.toLinearMap (laplacian g) receiver.symm.toLinearMap *
        endpointDressedGreen receiver.toLinearMap (green g) source.toLinearMap = 1 ∧
      endpointDressedGreen receiver.toLinearMap (green g) source.toLinearMap *
        endpointDressedInverse source.symm.toLinearMap (laplacian g) receiver.symm.toLinearMap = 1 := by
  apply endpointDressedInverse_isTwoSided _ _ _ _ _ _ (laplacian_green g) (green_laplacian g)
  · apply LinearMap.ext
    intro f
    exact receiver.symm_apply_apply f
  · apply LinearMap.ext
    intro f
    exact receiver.apply_symm_apply f
  · apply LinearMap.ext
    intro f
    exact source.symm_apply_apply f
  · apply LinearMap.ext
    intro f
    exact source.apply_symm_apply f

end HTGeometry.CompactPoissonGreen
