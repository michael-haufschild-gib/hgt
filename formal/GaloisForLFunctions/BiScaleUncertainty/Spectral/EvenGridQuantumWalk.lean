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
  apply ContinuousLinearMap.ext
  intro v
  simpa only [mul_apply_eq_comp, coprimeProjector_apply] using coprimeProjection_idempotent d v

private theorem common_idem (n : ℕ) : evenGridCommonPart n * evenGridCommonPart n =
    evenGridCommonPart n := by
  apply ContinuousLinearMap.ext
  intro v
  exact (evenGrid_parts_projections n v).1

private theorem common_mul_grid (n : ℕ) : evenGridCommonPart n * coprimeProjector (n+1) =
    evenGridCommonPart n := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [mul_apply_eq_comp, evenGridCommonPart,
    sub_apply, smul_apply,
    evenGridCompression_project]
  rw [show coprimeProjector (n+1) (coprimeProjector (n+1) v) =
    coprimeProjector (n+1) v from coprimeProjection_idempotent (n+1) v]

private theorem grid_signal (n : ℕ) :
    coprimeProjector (n+1) * HTGeometry.projectionReflection (coprimeProjector 0) *
      coprimeProjector (n+1) = evenGridCommonPart n := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [HTGeometry.projectionReflection, mul_apply_eq_comp,
    sub_apply, add_apply,
    one_apply_eq_self, map_sub, map_add, evenGridCommonPart,
    smul_apply, evenGridCompression, ContinuousLinearMap.comp_apply]
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

private theorem zero_signal_four_mul (k : ℕ) :
    (Chebyshev.T ℝ ((4*k : ℕ) : ℤ)).eval 0 = 1 := by
  have hindex : ((4*k : ℕ) : ℤ) = 2 * (2 * (k : ℤ)) := by push_cast; ring
  have heven : Even (2 * (k : ℤ)) := ⟨k, by ring⟩
  rw [hindex, Chebyshev.T_eval_two_mul_zero, Int.negOnePow_even _ heven]
  simp

/-- Every fourth step returns the entire original grid exactly. -/
theorem evenGridWalk_four_mul_compression (n k : ℕ) :
    coprimeProjector (n+1) * evenGridWalk n ^ (4*k) * coprimeProjector (n+1) =
      coprimeProjector (n+1) := by
  rw [evenGridWalk_compression, zero_signal_four_mul, one_smul]
  apply ContinuousLinearMap.ext
  intro v
  exact evenGrid_parts_sum n v

/-- Halfway through each return cycle, half-overlap modes change sign. -/
theorem evenGridWalk_four_mul_add_two_compression (n k : ℕ) :
    coprimeProjector (n+1) * evenGridWalk n ^ (4*k+2) * coprimeProjector (n+1) =
      evenGridCommonPart n - evenGridHalfPart n := by
  have hz : (Chebyshev.T ℝ ((4*k+2 : ℕ) : ℤ)).eval 0 = -1 := by
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval_sub, eval_mul, eval_X, mul_zero, zero_mul, zero_sub,
      zero_signal_four_mul]
  rw [evenGridWalk_compression, hz, neg_one_smul, sub_eq_add_neg]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear

#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_compression
#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_odd_compression

#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_four_mul_compression
#print axioms GaloisForLFunctions.BiScaleUncertainty.SobolevShear.evenGridWalk_four_mul_add_two_compression
