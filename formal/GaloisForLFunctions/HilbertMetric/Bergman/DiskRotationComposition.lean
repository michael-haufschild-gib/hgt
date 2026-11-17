import GaloisForLFunctions.HilbertMetric.Bergman.DiskAreaSurjectivity
import GaloisForLFunctions.HilbertMetric.Bergman.DiskReproducingKernel
import GaloisForLFunctions.HilbertMetric.Dynamics.RotationEssentialNorm

/-!
# Compact cancellation on the actual Bergman disk space

Rotations act diagonally in the normalized Bergman monomial basis and
preserve the literal disk-area norm. Finite linear combinations are
compact exactly when coefficients cancel at each repeated rotation.
Their essential norm is their full norm for arbitrary rotation angles.
-/

open Filter Topology MeasureTheory Metric
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry
noncomputable section

/-- Composition by a unit disk rotation in Bergman coordinates. -/
def rotation (z : Circle) : Disk →L[ℂ] Disk := Dynamics.phaseRotation z

/-- The diagonal action is literal composition of holomorphic functions. -/
theorem diskFun_rotation (z : Circle) (a : Disk) (w : ℂ) :
    diskFun (rotation z a) w = diskFun a ((z : ℂ) * w) := by
  unfold diskFun
  apply tsum_congr
  intro k
  change (Real.sqrt ((k : ℝ) + 1) : ℂ) * ((z : ℂ) ^ k * a k) * w ^ k =
    (Real.sqrt ((k : ℝ) + 1) : ℂ) * a k * ((z : ℂ) * w) ^ k
  rw [mul_pow]
  ring

/-- Every geometric disk rotation is unitary in the complete Bergman coefficient space. -/
theorem rotation_unitary (z : Circle) : rotation z ∈ unitary (Disk →L[ℂ] Disk) :=
  Dynamics.phaseRotation_unitary z

private theorem rotation_norm_sq (z : Circle) (a : Disk) : ‖rotation z a‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [hardyDisk_norm_sq, hardyDisk_norm_sq]
  apply tsum_congr
  intro k
  change ‖(z : ℂ) ^ k * a k‖ ^ 2 = ‖a k‖ ^ 2
  rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul]

/-- Unitarity preserves the actual area integral, with its precise normalization. -/
theorem rotation_preserves_area (z : Circle) (a : Disk) :
    (∫ w in ball (0 : ℂ) 1, ‖diskFun (rotation z a) w‖ ^ 2) =
      ∫ w in ball (0 : ℂ) 1, ‖diskFun a w‖ ^ 2 := by
  rw [integral_diskFun_norm_sq, integral_diskFun_norm_sq, rotation_norm_sq]

/-- A finite sum of genuine Bergman composition operators, allowing repeated rotations. -/
def rotationCombination {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) : Disk →L[ℂ] Disk :=
  Dynamics.phaseRotationSum z c

/-- The operator sum acts by the corresponding finite sum of holomorphic compositions. -/
theorem diskFun_rotationCombination {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ)
    (a : Disk) (w : Point) :
    diskFun (rotationCombination z c a) w = ∑ i, c i * diskFun a ((z i : ℂ) * (w : ℂ)) := by
  rw [← evaluation_apply]
  unfold rotationCombination
  rw [Dynamics.phaseRotationSum_eq_sum, ContinuousLinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.smul_apply, map_smul, evaluation_apply]
  change c i * diskFun (rotation (z i) a) w = _
  rw [diskFun_rotation]

/-- Compactness on the full Bergman disk model is exactly cancellation at each rotation. -/
theorem rotationCombination_compact_iff {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    IsCompactOperator (rotationCombination z c) ↔
      ∀ u ∈ Finset.univ.image (fun i => (z i : ℂ)), Dynamics.rotationFiber z c u = 0 :=
  Dynamics.phaseRotationSum_compact_iff z c

/-- Every nonzero finite rotation combination survives in the compact quotient. -/
theorem rotationCombination_compact_iff_zero {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    IsCompactOperator (rotationCombination z c) ↔ rotationCombination z c = 0 :=
  Dynamics.phaseRotationSum_compact_iff_zero z c

/-- Arbitrary finite Bergman rotation sums have essential norm equal to their full norm. -/
theorem rotationCombination_essential_norm {n : ℕ} (z : Fin n → Circle) (c : Fin n → ℂ) :
    compactIdealDistance (rotationCombination z c) = ‖rotationCombination z c‖ :=
  Dynamics.phaseRotationSum_compactIdealDistance z c

#print axioms diskFun_rotation
#print axioms rotation_preserves_area
#print axioms diskFun_rotationCombination
#print axioms rotationCombination_compact_iff
#print axioms rotationCombination_essential_norm
end
end GaloisForLFunctions.HilbertMetric.Bergman
