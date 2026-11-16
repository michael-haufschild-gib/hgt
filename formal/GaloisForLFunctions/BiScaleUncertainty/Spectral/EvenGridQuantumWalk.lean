import GaloisForLFunctions.HilbertMetric.QuantumWalk.IdempotentCalculus
import GaloisForLFunctions.BiScaleUncertainty.Spectral.EvenGridCompression

/-!
# Exact quantum returns on arithmetic tent grids

The even-grid compression has eigenvalues one and one half. The associated
reflection walk therefore has compressed signal equal to the common-grid
projection. Common modes remain fixed; the complementary return amplitude
is `T_k(0)`, giving a four-step cycle.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
open Polynomial
open GaloisForLFunctions.HilbertMetric.QuantumWalk

/-- Reflection walk between the even grid and the grid of spacing `n+3`. -/
def evenGridWalk (n : ℕ) : Velocity →L[ℝ] Velocity :=
  HTGeometry.twoProjectionQuantumWalk (coprimeProjector 0) (coprimeProjector (n+1))

private theorem grid_idem (d : ℕ) : coprimeProjector d * coprimeProjector d =
    coprimeProjector d := by
  ext v
  exact coprimeProjection_idempotent d v

private theorem common_idem (n : ℕ) : evenGridCommonPart n * evenGridCommonPart n =
    evenGridCommonPart n := by
  ext v
  exact (evenGrid_parts_projections n v).1

private theorem common_mul_grid (n : ℕ) : evenGridCommonPart n * coprimeProjector (n+1) =
    evenGridCommonPart n := by
  ext v
  simp only [ContinuousLinearMap.mul_apply, evenGridCommonPart,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    evenGridCompression_project]
  rw [show coprimeProjector (n+1) (coprimeProjector (n+1) v) =
    coprimeProjector (n+1) v from coprimeProjection_idempotent (n+1) v]

private theorem grid_signal (n : ℕ) :
    coprimeProjector (n+1) * HTGeometry.projectionReflection (coprimeProjector 0) *
      coprimeProjector (n+1) = evenGridCommonPart n := by
  ext v
  simp only [HTGeometry.projectionReflection, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply, map_sub, map_add, evenGridCommonPart,
    ContinuousLinearMap.smul_apply, evenGridCompression, ContinuousLinearMap.comp_apply]
  rw [show coprimeProjector (n+1) (coprimeProjector (n+1) v) =
    coprimeProjector (n+1) v from coprimeProjection_idempotent (n+1) v]
  module

private theorem grid_sub_common (n : ℕ) :
    coprimeProjector (n+1) - evenGridCommonPart n = evenGridHalfPart n := by
  unfold evenGridCommonPart evenGridHalfPart
  module

/-- All return operators split into common modes and the scalar Chebyshev-zero mode. -/
theorem evenGridWalk_compression (n k : ℕ) :
    coprimeProjector (n+1) * evenGridWalk n ^ k * coprimeProjector (n+1) =
      evenGridCommonPart n + (Chebyshev.T ℝ (k : ℤ)).eval 0 • evenGridHalfPart n := by
  have h := compressed_reflection_pow (𝕜 := ℝ)
    (coprimeProjector 0) (coprimeProjector (n+1)) (grid_idem 0) (grid_idem (n+1)) k
  change coprimeProjector (n+1) * evenGridWalk n ^ k * coprimeProjector (n+1) =
    aeval (coprimeProjector (n+1) * HTGeometry.projectionReflection (coprimeProjector 0) *
      coprimeProjector (n+1)) (Chebyshev.T ℝ (k : ℤ)) * coprimeProjector (n+1) at h
  rw [h, grid_signal, chebyshev_idempotent_mul _ _ (common_idem n) (common_mul_grid n),
    grid_sub_common]

/-- At every odd time the return operator removes exactly the half-overlap modes. -/
theorem evenGridWalk_odd_compression (n k : ℕ) :
    coprimeProjector (n+1) * evenGridWalk n ^ (2*k+1) * coprimeProjector (n+1) =
      evenGridCommonPart n := by
  rw [evenGridWalk_compression, Chebyshev.T_eval_zero_of_odd]
  · simp only [zero_smul, add_zero]
  · exact ⟨(k : ℤ), by push_cast; ring⟩

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_compression
#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_odd_compression
