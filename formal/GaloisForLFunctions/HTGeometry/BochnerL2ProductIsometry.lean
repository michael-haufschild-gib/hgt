import GaloisForLFunctions.HTGeometry.BochnerL2HilbertTensor
import GaloisForLFunctions.RHTower.L2HilbertTensorProduct

/-! The original product-measure L² space is isometric to angular-L²-valued radial L². -/
open MeasureTheory
open scoped TensorProduct
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]

def bochnerL2ProductEquiv : Lp (Lp ℂ 2 ν) 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  bochnerL2TensorEquiv.symm.trans l2HilbertTensorProductEquiv

/-- The isometry agrees with the actual pointwise separated product on every pure tensor. -/
theorem bochnerL2ProductEquiv_pure (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    bochnerL2ProductEquiv (bochnerL2Product f g) = l2SeparatedProduct f g := by
  change l2HilbertTensorProductEquiv (bochnerL2TensorEquiv.symm (bochnerL2Product f g)) = _
  rw [← bochnerL2Tensor_tmul,← bochnerL2TensorEquiv_coe,
    LinearIsometryEquiv.symm_apply_apply,l2HilbertTensorProductEquiv_coe,l2TensorToProduct_tmul]

end
end GaloisForLFunctions.HTGeometry
