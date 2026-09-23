import GaloisForLFunctions.RHTower.FokasLenellsCausalComplexShift
import GaloisForLFunctions.RHTower.FokasLenellsCausalNeumannCenter
import GaloisForLFunctions.HTGeometry.ExteriorFeshbachPruning

/-! The existing Feshbach Neumann inverse applied to the actual causal generator's resolvent.
The explicit disk construction discharges every perturbation assumption on the right half-plane. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance fokasLenellsCausalComplexResolventInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The actual bounded inverse of the explicit perturbation of the identity. -/
def causalNeumannInverse (z : {z : ℂ // 0 < z.re}) : hardyL2ᗮ →L[ℂ] hardyL2ᗮ :=
  shiftInverse (norm_causalNeumannPerturbation_lt_one z)

/-- The existing corpus Neumann construction cancels the actual perturbation from the right. -/
theorem causalNeumannInverse_right (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    causalNeumannInverse z u + causalNeumannPerturbation z (causalNeumannInverse z u) = u := by
  have h := congrArg (fun f : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => f u)
    (shiftInverse_mul_right (norm_causalNeumannPerturbation_lt_one z))
  change (1 : ℝ) • causalNeumannInverse z u +
    causalNeumannPerturbation z (causalNeumannInverse z u) = u at h
  simpa only [one_smul] using h

/-- The actual complex shift factors through the constructed positive real resolvent. -/
theorem causalComplexGeneratorShift_realResolvent (z : {z : ℂ // 0 < z.re})
    (u : hardyL2ᗮ) :
    causalComplexGeneratorShift z.val (causalResolvent (causalNeumannParameter z) u) =
      u + causalNeumannPerturbation z u := by
  change z.val • (causalResolvent (causalNeumannParameter z) u).val -
    causalGenerator (causalResolvent (causalNeumannParameter z) u) = _
  rw [causalGenerator_resolvent, causalResolvent_eq_laplace, exp_causalNeumannParameter]
  change z.val • causalLaplaceIntegral (causalNeumannParameter z) u -
    ((causalNeumannCenter z : ℂ) • causalLaplaceIntegral (causalNeumannParameter z) u - u) =
    u + (z.val-(causalNeumannCenter z : ℂ)) • causalLaplaceIntegral (causalNeumannParameter z) u
  module

/-- The actual bounded resolvent into the maximal generator domain at every right-half-plane point. -/
def causalComplexResolvent (z : {z : ℂ // 0 < z.re}) :
    hardyL2ᗮ →L[ℂ] causalGeneratorDomain :=
  (causalResolvent (causalNeumannParameter z)).comp (causalNeumannInverse z)

/-- Every right-half-plane shift has the constructed resolvent as a right inverse. -/
theorem causalComplexGeneratorShift_resolvent (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    causalComplexGeneratorShift z.val (causalComplexResolvent z u) = u := by
  change causalComplexGeneratorShift z.val
    (causalResolvent (causalNeumannParameter z) (causalNeumannInverse z u)) = u
  rw [causalComplexGeneratorShift_realResolvent, causalNeumannInverse_right]

/-- Every right-half-plane shift has the same resolvent as a left inverse on the actual domain. -/
theorem causalComplexResolvent_generatorShift (z : {z : ℂ // 0 < z.re})
    (u : causalGeneratorDomain) :
    causalComplexResolvent z (causalComplexGeneratorShift z.val u) = u := by
  apply causalComplexGeneratorShift_injective z
  exact causalComplexGeneratorShift_resolvent z _

/-- The actual generator of the complex resolvent is the required affine expression. -/
theorem causalGenerator_complexResolvent (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    causalGenerator (causalComplexResolvent z u) = z.val • (causalComplexResolvent z u).val - u := by
  have h := causalComplexGeneratorShift_resolvent z u
  change z.val • (causalComplexResolvent z u).val -
    causalGenerator (causalComplexResolvent z u) = u at h
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  exact (sub_eq_iff_eq_add.mp h).symm

/-- The full right half-plane shift is bijective on the actual maximal domain. -/
theorem causalComplexGeneratorShift_bijective (z : {z : ℂ // 0 < z.re}) :
    Function.Bijective (causalComplexGeneratorShift z.val) :=
  ⟨causalComplexGeneratorShift_injective z,
    fun u => ⟨causalComplexResolvent z u, causalComplexGeneratorShift_resolvent z u⟩⟩

/-- The inverse bound depends only on the actual spectral parameter's real part. -/
theorem causalComplexResolvent_norm_le (z : {z : ℂ // 0 < z.re}) (u : hardyL2ᗮ) :
    ‖causalComplexResolvent z u‖ ≤ z.val.re⁻¹ * ‖u‖ := by
  have h := causalComplexGeneratorShift_norm_lowerBound z (causalComplexResolvent z u)
  rw [causalComplexGeneratorShift_resolvent] at h
  change z.val.re * ‖causalComplexResolvent z u‖ ≤ ‖u‖ at h
  calc
    ‖causalComplexResolvent z u‖ = z.val.re⁻¹ * (z.val.re * ‖causalComplexResolvent z u‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ z.property.ne', one_mul]
    _ ≤ z.val.re⁻¹ * ‖u‖ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr z.property.le)

/-- The complex resolvent is bounded by reciprocal real damping in operator norm. -/
theorem norm_causalComplexResolvent_le (z : {z : ℂ // 0 < z.re}) :
    ‖causalComplexResolvent z‖ ≤ z.val.re⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr z.property.le)
    (causalComplexResolvent_norm_le z)

end
end RHTower.FokasLenells
