import GaloisForLFunctions.HTGeometry.BochnerL2HilbertTensor

/-! Scalar Hilbert probes detect both Bochner L² vectors and their measurable support. -/
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Filter Topology
open scoped TensorProduct
noncomputable section
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem bochnerL2Product_inner_probe (f : Lp ℂ 2 μ) (v : H) (g : Lp H 2 μ) :
    inner ℂ (bochnerL2Product f v) g = inner ℂ f ((innerSL ℂ v).compLp g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [bochnerL2Product_ae f v,(innerSL ℂ v).coeFn_compLp g] with x hx hy
  rw [hx,hy]
  simp only [inner_smul_left,RCLike.inner_apply,innerSL_apply_apply]
  ring

/-- No separability assumption or common pointwise representative is needed to separate L² vectors. -/
theorem bochnerL2_eq_zero_of_inner_probes (g : Lp H 2 μ)
    (hg : ∀ v : H, (innerSL ℂ v).compLp g = 0) : g = 0 := by
  have hall : ∀ x : Lp ℂ 2 μ ⊗[ℂ] H, inner ℂ (bochnerL2Tensor x) g = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f v => rw [bochnerL2Tensor_tmul,bochnerL2Product_inner_probe,hg,inner_zero_right]
    | add x y hx hy => rw [map_add,inner_add_left,hx,hy,add_zero]
  have hself : inner ℂ g g = 0 :=
    DenseRange.induction_on (p := fun f : Lp H 2 μ => inner ℂ f g = 0)
      bochnerL2Tensor_dense g
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hall
  exact inner_self_eq_zero.mp hself

/-- Weak scalar support of a Bochner L² function is its actual almost-everywhere support. -/
theorem bochnerL2_ae_zero_on_of_inner_probes (f : α → H) (hf : MemLp f 2 μ)
    (s : Set α) (hs : MeasurableSet s)
    (h : ∀ v : H, ∀ᵐ x ∂μ, x ∈ s → inner ℂ v (f x) = 0) :
    ∀ᵐ x ∂μ, x ∈ s → f x = 0 := by
  let g : Lp H 2 (μ.restrict s) := (hf.restrict s).toLp f
  have hg : g = 0 := by
    apply bochnerL2_eq_zero_of_inner_probes
    intro v
    apply Lp.ext
    filter_upwards [(innerSL ℂ v).coeFn_compLp g,(hf.restrict s).coeFn_toLp,
      ae_restrict_of_ae (h v),ae_restrict_mem hs,Lp.coeFn_zero ℂ 2 (μ.restrict s)]
      with x hx hy hv hsx h0
    rw [hx,hy,h0]
    exact hv hsx
  have hae : ∀ᵐ x ∂μ.restrict s, f x = 0 := by
    have he := (hf.restrict s).coeFn_toLp
    change g =ᵐ[μ.restrict s] f at he
    rw [hg] at he
    exact he.symm.trans (Lp.coeFn_zero H 2 (μ.restrict s))
  exact (ae_restrict_iff' hs).mp hae

end
end GaloisForLFunctions.HTGeometry
