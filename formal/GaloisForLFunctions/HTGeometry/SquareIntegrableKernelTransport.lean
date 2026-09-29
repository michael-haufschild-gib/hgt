import GaloisForLFunctions.HTGeometry.SquareIntegrableKernelOperator

/-!
# Transport of kernel operators along measure-preserving maps

For a measure-preserving `σ : (δ, m) → (α, μ)` the composition `U f = f ∘ σ` is a linear isometry
`L²(μ) → L²(m)`, and it intertwines the kernel operator of `k` with the kernel operator of the
pulled-back kernel `k(σ u, σ v)`:

`U K = K_σ U`,

since `∫ k(σ u, σ v) f(σ v) dm(v) = ∫ k(σ u, y) f(y) dμ(y)`.  If `σ` has a measure-preserving
almost-everywhere inverse `τ`, then `U` is unitary with inverse `f ↦ f ∘ τ` and `K_σ = U K U⁻¹`.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α δ : Type*} [MeasurableSpace α] [MeasurableSpace δ] {μ : Measure α} {m : Measure δ}

/-- Composition with a measure-preserving map, `f ↦ f ∘ σ`, as an operator `L²(μ) → L²(m)`. -/
def compL2 {σ : δ → α} (hσ : MeasurePreserving σ m μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 m :=
  (Lp.compMeasurePreservingₗᵢ ℂ σ hσ).toContinuousLinearMap

theorem compL2_coeFn {σ : δ → α} (hσ : MeasurePreserving σ m μ) (f : Lp ℂ 2 μ) :
    (compL2 hσ f : δ → ℂ) =ᵐ[m] f ∘ σ :=
  Lp.coeFn_compMeasurePreserving f hσ

theorem norm_compL2_apply {σ : δ → α} (hσ : MeasurePreserving σ m μ) (f : Lp ℂ 2 μ) :
    ‖compL2 hσ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f hσ

/-- A measure-preserving almost-everywhere inverse makes the composition operators inverse. -/
theorem compL2_comp_compL2 {σ : δ → α} (hσ : MeasurePreserving σ m μ) {τ : α → δ}
    (hτ : MeasurePreserving τ μ m) (hστ : ∀ᵐ x ∂μ, σ (τ x) = x) :
    compL2 hτ ∘L compL2 hσ = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  refine Lp.ext ?_
  have h1 := compL2_coeFn hτ (compL2 hσ f)
  have h2 : ((compL2 hσ f : δ → ℂ) ∘ τ) =ᵐ[μ] ((f : α → ℂ) ∘ σ) ∘ τ :=
    (compL2_coeFn hσ f).comp_tendsto hτ.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h1, h2, hστ] with x h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  simp [h3]

namespace SqIntKernel

variable [SFinite μ] [SFinite m]

/-- The kernel `k(σ u, σ v)` pulled back along a measure-preserving map. -/
def pullback (k : SqIntKernel μ μ) {σ : δ → α} (hσ : MeasurePreserving σ m μ) :
    SqIntKernel m m where
  toFun u v := k.toFun (σ u) (σ v)
  measurable := k.measurable.comp (hσ.measurable.prodMap hσ.measurable)
  energy_lt_top := by
    have hin : ∀ u, ∫⁻ v, ‖k.toFun (σ u) (σ v)‖ₑ ^ 2 ∂m = k.rowEnergy (σ u) := fun u =>
      hσ.lintegral_comp ((k.measurable_left (σ u)).enorm.pow_const 2)
    simp_rw [hin]
    rw [hσ.lintegral_comp k.measurable_rowEnergy]
    exact k.energy_lt_top

omit [SFinite m] in
theorem pullback_toFun (k : SqIntKernel μ μ) {σ : δ → α} (hσ : MeasurePreserving σ m μ)
    (u v : δ) : (k.pullback hσ).toFun u v = k.toFun (σ u) (σ v) := rfl

/-- **Transport.**  `U K = K_σ U` for `U f = f ∘ σ`. -/
theorem compL2_comp_op (k : SqIntKernel μ μ) {σ : δ → α} (hσ : MeasurePreserving σ m μ) :
    compL2 hσ ∘L k.op = (k.pullback hσ).op ∘L compL2 hσ := by
  ext1 f
  refine Lp.ext ?_
  have h1 := compL2_coeFn hσ (k.op f)
  have h2 : ((k.op f : α → ℂ) ∘ σ) =ᵐ[m] (k.apply f) ∘ σ :=
    (k.op_coeFn f).comp_tendsto hσ.quasiMeasurePreserving.tendsto_ae
  have h3 := (k.pullback hσ).op_coeFn (compL2 hσ f)
  filter_upwards [h1, h2, h3] with u h1 h2 h3
  rw [ContinuousLinearMap.comp_apply, h1, h2, ContinuousLinearMap.comp_apply, h3]
  simp only [Function.comp_apply, apply, pullback_toFun]
  have hf := compL2_coeFn hσ f
  rw [integral_congr_ae (hf.mono fun v hv => by rw [hv, Function.comp_apply])]
  have hg : AEStronglyMeasurable (fun y => k.toFun (σ u) y * f y) (Measure.map σ m) := by
    rw [hσ.map_eq]
    exact ((k.measurable_left (σ u)).aestronglyMeasurable).mul (Lp.aestronglyMeasurable f)
  have := integral_map hσ.measurable.aemeasurable hg
  rw [hσ.map_eq] at this
  exact this

/-- **Unitary transport.**  With a measure-preserving a.e. inverse `τ`, `K_σ = U K U⁻¹`. -/
theorem pullback_op_eq (k : SqIntKernel μ μ) {σ : δ → α} (hσ : MeasurePreserving σ m μ)
    {τ : α → δ} (hτ : MeasurePreserving τ μ m) (hτσ : ∀ᵐ u ∂m, τ (σ u) = u) :
    (k.pullback hσ).op = compL2 hσ ∘L k.op ∘L compL2 hτ := by
  rw [← ContinuousLinearMap.comp_assoc, compL2_comp_op, ContinuousLinearMap.comp_assoc,
    compL2_comp_compL2 hτ hσ hτσ, ContinuousLinearMap.comp_id]

end SqIntKernel

end

end GaloisForLFunctions.HTGeometry
