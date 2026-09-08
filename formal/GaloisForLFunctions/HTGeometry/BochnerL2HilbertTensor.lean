import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Module.Completion

/-! The completed Hilbert tensor product of scalar L² and a Hilbert space is its Bochner L² space. -/
open MeasureTheory Set Filter Topology
open scoped TensorProduct ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def bochnerL2Product (f : Lp ℂ 2 μ) (g : E) : Lp E 2 μ :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight g).compLp f

theorem bochnerL2Product_ae (f : Lp ℂ 2 μ) (g : E) :
    (bochnerL2Product f g : α → E) =ᵐ[μ] fun t => f t • g :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight g).coeFn_compLp f

def bochnerL2ProductBilinear : Lp ℂ 2 μ →ₗ[ℂ] E →ₗ[ℂ] Lp E 2 μ where
  toFun f := {
    toFun := bochnerL2Product f
    map_add' g h := by
      apply Lp.ext
      filter_upwards [bochnerL2Product_ae f (g+h),bochnerL2Product_ae f g,
        bochnerL2Product_ae f h,Lp.coeFn_add (bochnerL2Product f g) (bochnerL2Product f h)]
        with t h0 h1 h2 h3
      simp only [h0,h3,Pi.add_apply,h1,h2,smul_add]
    map_smul' c g := by
      apply Lp.ext
      filter_upwards [bochnerL2Product_ae f (c • g),bochnerL2Product_ae f g,
        Lp.coeFn_smul c (bochnerL2Product f g)] with t h0 h1 h2
      simp only [RingHom.id_apply]
      rw [h0,h2]
      simp only [Pi.smul_apply]
      rw [h1]
      exact smul_comm _ _ _ }
  map_add' f h := by
    apply LinearMap.ext
    intro g
    change bochnerL2Product (f+h) g = bochnerL2Product f g+bochnerL2Product h g
    apply Lp.ext
    filter_upwards [bochnerL2Product_ae (f+h) g,bochnerL2Product_ae f g,
      bochnerL2Product_ae h g,Lp.coeFn_add (bochnerL2Product f g) (bochnerL2Product h g),
      Lp.coeFn_add f h] with t h0 h1 h2 h3 h4
    rw [h0,h3,h4]
    simp only [Pi.add_apply]
    rw [h1,h2,add_smul]
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    change bochnerL2Product (c • f) g = c • bochnerL2Product f g
    apply Lp.ext
    filter_upwards [bochnerL2Product_ae (c • f) g,bochnerL2Product_ae f g,
      Lp.coeFn_smul c (bochnerL2Product f g),Lp.coeFn_smul c f] with t h0 h1 h2 h3
    rw [h0,h2,h3]
    simp only [Pi.smul_apply]
    rw [h1,smul_smul]
    simp only [smul_eq_mul]

theorem bochnerL2Product_inner (f h : Lp ℂ 2 μ) (g k : E) :
    inner ℂ (bochnerL2Product f g) (bochnerL2Product h k) = inner ℂ f h * inner ℂ g k := by
  rw [L2.inner_def,L2.inner_def]
  have he : (fun t => inner ℂ (bochnerL2Product f g t) (bochnerL2Product h k t)) =ᵐ[μ]
      fun t => inner ℂ (f t) (h t) * inner ℂ g k := by
    filter_upwards [bochnerL2Product_ae f g,bochnerL2Product_ae h k] with t hf hh
    rw [hf,hh,inner_smul_left,inner_smul_right]
    simp [mul_assoc,mul_comm]
  rw [integral_congr_ae he,integral_mul_const]

def bochnerL2Tensor : Lp ℂ 2 μ ⊗[ℂ] E →ₗ[ℂ] Lp E 2 μ :=
  TensorProduct.lift bochnerL2ProductBilinear

theorem bochnerL2Tensor_tmul (f : Lp ℂ 2 μ) (g : E) :
    bochnerL2Tensor (f ⊗ₜ[ℂ] g) = bochnerL2Product f g := rfl

theorem bochnerL2Tensor_inner (x y : Lp ℂ 2 μ ⊗[ℂ] E) :
    inner ℂ (bochnerL2Tensor x) (bochnerL2Tensor y) = inner ℂ x y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul h k => simpa only [bochnerL2Tensor_tmul,TensorProduct.inner_tmul] using
          bochnerL2Product_inner f h g k
      | add y z hy hz => simp only [map_add,inner_add_right,hy,hz]
  | add x z hx hz => simp only [map_add,inner_add_left,hx,hz]

def bochnerL2TensorIsometry : Lp ℂ 2 μ ⊗[ℂ] E →ₗᵢ[ℂ] Lp E 2 μ :=
  bochnerL2Tensor.isometryOfInner bochnerL2Tensor_inner

theorem bochnerL2Product_indicator {s : Set α} (hs : MeasurableSet s) (hμ : μ s ≠ ∞) (g : E) :
    bochnerL2Product (indicatorConstLp 2 hs hμ (1:ℂ)) g = indicatorConstLp 2 hs hμ g := by
  apply Lp.ext
  filter_upwards [bochnerL2Product_ae (indicatorConstLp 2 hs hμ (1:ℂ)) g,
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1:ℂ))),
    (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := g))] with t h0 h1 h2
  rw [h0,h1,h2]
  by_cases ht : t ∈ s <;> simp [ht]

/-- Scalar indicator tensors generate a dense subspace of the actual Bochner L² space. -/
theorem bochnerL2Tensor_dense : DenseRange (bochnerL2Tensor (μ := μ) (E := E)) := by
  have hm : ∀ v : Lp E 2 μ, v ∈ bochnerL2Tensor.range.topologicalClosure := by
    refine Lp.induction (by norm_num)
      (fun v : Lp E 2 μ => v ∈ bochnerL2Tensor.range.topologicalClosure) ?_ ?_ ?_
    · intro g s hs hμs
      apply Submodule.le_topologicalClosure
      refine ⟨indicatorConstLp 2 hs hμs.ne (1:ℂ) ⊗ₜ[ℂ] g,?_⟩
      rw [bochnerL2Tensor_tmul,bochnerL2Product_indicator,Lp.simpleFunc.coe_indicatorConst]
    · intro f g hf hg _ hfmem hgmem
      exact Submodule.add_mem _ hfmem hgmem
    · exact Submodule.isClosed_topologicalClosure _
  intro v
  exact hm v

variable [CompleteSpace E]

/-- Canonical Bochner L² realization of the completed scalar-Hilbert tensor product. -/
def bochnerL2TensorEquiv : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] E) ≃ₗᵢ[ℂ] Lp E 2 μ :=
  LinearEquiv.extendOfIsometry (LinearEquiv.refl ℂ (Lp ℂ 2 μ ⊗[ℂ] E))
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := Lp ℂ 2 μ ⊗[ℂ] E)).toLinearMap
    bochnerL2TensorIsometry.toLinearMap UniformSpace.Completion.denseRange_coe
    bochnerL2Tensor_dense (fun x => by
      change ‖bochnerL2TensorIsometry x‖ =
        ‖(UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := Lp ℂ 2 μ ⊗[ℂ] E)) x‖
      rw [bochnerL2TensorIsometry.norm_map]
      exact ((UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ)
        (E := Lp ℂ 2 μ ⊗[ℂ] E)).norm_map x).symm)

theorem bochnerL2TensorEquiv_coe (x : Lp ℂ 2 μ ⊗[ℂ] E) :
    bochnerL2TensorEquiv (x : UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] E)) = bochnerL2Tensor x := by
  exact LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (Lp ℂ 2 μ ⊗[ℂ] E))
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := Lp ℂ 2 μ ⊗[ℂ] E)).toLinearMap
    bochnerL2TensorIsometry.toLinearMap UniformSpace.Completion.denseRange_coe
    bochnerL2Tensor_dense _ x

end
end GaloisForLFunctions.HTGeometry
