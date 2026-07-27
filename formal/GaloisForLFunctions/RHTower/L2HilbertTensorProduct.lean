import GaloisForLFunctions.RHTower.L2SeparatedProductDensity
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Hilbert tensor product of two `L²` spaces

For sigma-finite measures, the pointwise separated-product map preserves the canonical inner
product on the algebraic tensor product.  Its extension identifies the Hilbert completion of
`L²(μ) ⊗ L²(ν)` linearly and isometrically with `L²(μ.prod ν)`.  This supplies the completed
Hilbert tensor product construction left open by the algebraic tensor-product API.
-/

namespace MeasureTheory

noncomputable section

open scoped TensorProduct

variable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SigmaFinite μ] [SigmaFinite ν]


theorem l2SeparatedProduct_inner
    (f f' : Lp ℂ 2 μ) (g g' : Lp ℂ 2 ν) :
    inner ℂ (l2SeparatedProduct f g)
        (l2SeparatedProduct f' g') =
      inner ℂ f f' * inner ℂ g g' := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  have hae :
      (fun z =>
        inner ℂ
          (l2SeparatedProduct f g z)
          (l2SeparatedProduct f' g' z))
        =ᵐ[μ.prod ν]
      fun z =>
        inner ℂ
          (l2SeparatedFun f g z)
          (l2SeparatedFun f' g' z) :=
    by
      filter_upwards [
        l2SeparatedProduct_ae f g,
        l2SeparatedProduct_ae f' g']
        with z hf hg
      rw [hf, hg]
  rw [integral_congr_ae hae]
  simpa [l2SeparatedFun, mul_assoc, mul_left_comm, mul_comm] using
    (integral_prod_mul
      (μ := μ) (ν := ν)
      (fun x => inner ℂ (f x) (f' x))
      (fun y => inner ℂ (g y) (g' y)))

theorem l2TensorToProduct_inner
    (x y : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    inner ℂ (l2TensorToProduct x)
        (l2TensorToProduct y) =
      inner ℂ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul f' g' =>
          simpa only [l2TensorToProduct_tmul,
            TensorProduct.inner_tmul] using
            l2SeparatedProduct_inner f f' g g'
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [map_add, inner_add_right, hy₁, hy₂]
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [map_add, inner_add_left, hx₁, hx₂]

def l2TensorToProductLinearIsometry :
    (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) →ₗᵢ[ℂ]
      Lp ℂ 2 (μ.prod ν) :=
  l2TensorToProduct.isometryOfInner l2TensorToProduct_inner

abbrev L2HilbertTensorProduct :=
  UniformSpace.Completion
    (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)

theorem l2TensorCompletionDenseNorm
    (x : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    ‖l2TensorToProductLinearIsometry x‖ =
      ‖(UniformSpace.Completion.toComplₗᵢ
          (𝕜 := ℂ)
          (E := Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)).toLinearMap x‖ := by
  rw [l2TensorToProductLinearIsometry.norm_map]
  exact
    ((UniformSpace.Completion.toComplₗᵢ
      (𝕜 := ℂ)
      (E := Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)).norm_map x).symm

def l2HilbertTensorProductEquiv :
    L2HilbertTensorProduct
        (α := α) (β := β) (μ := μ) (ν := ν) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (μ.prod ν) :=
  LinearEquiv.extendOfIsometry
    (LinearEquiv.refl ℂ
      (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := ℂ)
      (E := Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)).toLinearMap
    l2TensorToProductLinearIsometry.toLinearMap
    UniformSpace.Completion.denseRange_coe
    l2TensorToProduct_denseRange
    l2TensorCompletionDenseNorm

@[simp]
theorem l2HilbertTensorProductEquiv_coe
    (x : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
    l2HilbertTensorProductEquiv
        (x : L2HilbertTensorProduct
          (α := α) (β := β) (μ := μ) (ν := ν)) =
      l2TensorToProduct x := by
  exact LinearEquiv.extendOfIsometry_eq
    (LinearEquiv.refl ℂ
      (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν))
    (UniformSpace.Completion.toComplₗᵢ
      (𝕜 := ℂ)
      (E := Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)).toLinearMap
    l2TensorToProductLinearIsometry.toLinearMap
    UniformSpace.Completion.denseRange_coe
    l2TensorToProduct_denseRange
    l2TensorCompletionDenseNorm
    x

end

end MeasureTheory
