import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicGradedRecovery
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The sharp physical cost of a missing homogeneous coefficient

The missing coefficient is a surjective linear map. Its kernel consists exactly
of homogeneous observations available in the cusp algebra. The attained
positive recovery gap gives a sharp lower bound for the physical capacity,
and every prescribed real coefficient has a representative attaining it.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial



theorem cubicHomogeneousCapacity_smul (k : ℕ) (r : ℝ) (P : cubicHomogeneousSpace k) :
    cubicHomogeneousCapacity k (r • P)=|r| *cubicHomogeneousCapacity k P := by
  letI := cubicHomogeneousNormedGroup k
  letI := cubicHomogeneousNormedSpace k
  change ‖r • P‖=|r| *‖P‖
  rw [norm_smul,Real.norm_eq_abs]

def cubicGradedCoefficient (k : ℕ) : cubicHomogeneousSpace (k+1) →ₗ[ℝ] ℝ :=
  (LinearMap.proj (cubicMissingIndex k)).comp (cubicHomogeneousCoordinatesEquiv (k+1)).toLinearMap

theorem cubicGradedCoefficient_apply (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    cubicGradedCoefficient k P=cubicHomogeneousCoordinates (k+1) P (cubicMissingIndex k) := rfl

theorem cubicGradedCoefficient_missing (k : ℕ) :
    cubicGradedCoefficient k (cubicHomogeneousMissing k)=1 := by
  rw [cubicGradedCoefficient_apply,cubicHomogeneousMissing_coordinates]
  simp only [cubicMissingCoefficients,ite_true]

theorem cubicGradedCoefficient_surjective (k : ℕ) : Function.Surjective (cubicGradedCoefficient k) := by
  intro r
  refine ⟨r • cubicHomogeneousMissing k,?_⟩
  rw [map_smul,cubicGradedCoefficient_missing,smul_eq_mul,mul_one]

@[reducible]
def cubicGradedAvailable (k : ℕ) : Submodule ℝ (cubicHomogeneousSpace (k+1)) :=
  LinearMap.ker (cubicGradedCoefficient k)

theorem cubicGradedAvailable_mem (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    P ∈ cubicGradedAvailable k ↔ P.val ∈ cubicCuspAlgebra := by
  rw [cubicGradedAvailable,LinearMap.mem_ker,cubicGradedCoefficient_apply]
  exact (cubicHomogeneousCoordinates_cusp k P).symm


theorem cubicGradedCoefficient_sharpBound (k : ℕ) (P : cubicHomogeneousSpace (k+1)) :
    |cubicGradedCoefficient k P| *cubicGradedRecoveryGap k ≤ cubicHomogeneousCapacity (k+1) P := by
  by_cases hz : cubicGradedCoefficient k P=0
  · simpa only [hz,abs_zero,zero_mul] using cubicHomogeneousCapacity_nonneg (k+1) P
  · let R := (cubicGradedCoefficient k P)⁻¹ • P
    have hR : R ∈ cubicNormalizedResiduals k := by
      change cubicGradedCoefficient k ((cubicGradedCoefficient k P)⁻¹ • P)=1
      rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hz]
    have hb := (cubicGradedRecoveryGap_isLeast k).2
      (show cubicHomogeneousCapacity (k+1) R ∈ cubicHomogeneousRecoveryErrors k from
        ⟨R,(cubicNormalizedResiduals_mem k R).mp hR,rfl⟩)
    change cubicGradedRecoveryGap k ≤ cubicHomogeneousCapacity (k+1) ((cubicGradedCoefficient k P)⁻¹ • P) at hb
    rw [cubicHomogeneousCapacity_smul,abs_inv] at hb
    have h := mul_le_mul_of_nonneg_left hb (abs_nonneg (cubicGradedCoefficient k P))
    rw [← mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hz),one_mul] at h
    exact h

theorem cubicGradedCoefficient_sharpAttainment (k : ℕ) (r : ℝ) :
    ∃ P : cubicHomogeneousSpace (k+1), cubicGradedCoefficient k P=r ∧
      cubicHomogeneousCapacity (k+1) P=|r| *cubicGradedRecoveryGap k := by
  obtain ⟨R,hR,hcap⟩ := cubicGradedRecoveryGap_attained k
  have hr : cubicGradedCoefficient k R=1 := hR
  refine ⟨r • R,?_,?_⟩
  · rw [map_smul,hr,smul_eq_mul,mul_one]
  · rw [cubicHomogeneousCapacity_smul,hcap]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
