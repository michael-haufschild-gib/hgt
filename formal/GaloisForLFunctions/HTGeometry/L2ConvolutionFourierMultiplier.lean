import GaloisForLFunctions.HTGeometry.L2FourierMultiplier
import GaloisForLFunctions.HTGeometry.BoundedMultiplierHilbert
import GaloisForLFunctions.HTGeometry.CausalFourierBridge
import GaloisForLFunctions.HTGeometry.L2FourierIntegralBridge
import GaloisForLFunctions.HTGeometry.SchurKernelOperator

/-!
# Convolution operators on `L²(ℝ)` are Fourier multipliers

For an integrable measurable profile `g`, the kernel `g(y - z)` is a Schur kernel on `ℝ` with bound
`‖g‖₁`, and its bounded operator on `L²(ℝ)` is the Fourier multiplier with the symbol `𝓕 g`
(mathlib convention `𝓕 g (w) = ∫ e^{-2πixw} g(x) dx`).  The proof checks the identity on Schwartz
functions, where the operator is the classical convolution and the classical convolution theorem
applies, and extends it by density.

Also: Fourier multipliers with almost everywhere equal symbols coincide, the adjoint of a
multiplier is the multiplier of the conjugate symbol, and a Schur kernel tilted by a coordinate
difference `(ψ y - ψ z) k(y,z)` is the commutator `[M_ψ, K]` on the domain of `M_ψ`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory FourierTransform Filter
open scoped ENNReal NNReal Convolution

namespace GaloisForLFunctions.HTGeometry

/-! ### The classical Fourier transform of an integrable function -/

/-- `‖𝓕 g (w)‖ ≤ ‖g‖₁`. -/
theorem norm_fourier_apply_le_integral_norm (g : ℝ → ℂ) (w : ℝ) : ‖𝓕 g w‖ ≤ ∫ x, ‖g x‖ := by
  rw [Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [Circle.norm_smul]

theorem continuous_fourier_of_integrable' {g : ℝ → ℂ} (hg : Integrable g) : Continuous (𝓕 g) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg

/-- `𝓕 (c g) = c 𝓕 g`. -/
theorem fourier_const_mul_apply (c : ℂ) (g : ℝ → ℂ) (w : ℝ) :
    𝓕 (fun x => c * g x) w = c * 𝓕 g w := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
  congr 1
  funext x
  simp only [Circle.smul_def, smul_eq_mul]
  ring

/-- The unitary Fourier transform of an `L²` class with integrable representative is almost
everywhere its classical Fourier integral. -/
theorem fourierL2_coeFn_ae_eq_fourier (u : Lp ℂ 2 (volume : Measure ℝ))
    (hu : Integrable (u : ℝ → ℂ)) : (fourierL2 ℝ u : ℝ → ℂ) =ᵐ[volume] 𝓕 (u : ℝ → ℂ) := by
  have hb := coeFn_fourierTransform_ae_eq_fourierIntegral u hu
  have hcoe := MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hu)
  filter_upwards [hb] with w hw
  change ((𝓕 u : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) w = _
  rw [hw, Real.Lp.fourierTransform_apply, Real.fourier_real_eq, Real.fourier_real_eq]
  refine integral_congr_ae ?_
  filter_upwards [hcoe] with x hx
  rw [hx]

/-! ### Algebra of Fourier multipliers -/

/-- Fourier multipliers with almost everywhere equal symbols coincide. -/
theorem fourierMulCLM_congr_ae {φ ψ : ℝ → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ) {C D : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (hae : φ =ᵐ[volume] ψ) : fourierMulCLM hφ hC0 hC = fourierMulCLM hψ hD0 hD := by
  refine ContinuousLinearMap.ext fun f => ?_
  rw [fourierMulCLM_apply, fourierMulCLM_apply,
    lpBoundedMulCLM_congr (p := 2) (μ := (volume : Measure ℝ)) hφ hψ hC0 hC hD0 hD hae]

theorem adjoint_fourierL2 : ContinuousLinearMap.adjoint (fourierL2 ℝ) = fourierL2inv ℝ := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun u v => ?_).symm
  have h := (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u) v
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

theorem adjoint_fourierL2inv : ContinuousLinearMap.adjoint (fourierL2inv ℝ) = fourierL2 ℝ := by
  rw [← adjoint_fourierL2, ContinuousLinearMap.adjoint_adjoint]

/-- **The adjoint of a Fourier multiplier is the multiplier of the conjugate symbol.** -/
theorem adjoint_fourierMulCLM {φ ψ : ℝ → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ) {C D : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ ξ, ‖ψ ξ‖ ≤ D)
    (hconj : ∀ ξ, ψ ξ = (starRingEnd ℂ) (φ ξ)) :
    ContinuousLinearMap.adjoint (fourierMulCLM hφ hC0 hC) = fourierMulCLM hψ hD0 hD := by
  have e : fourierMulCLM hφ hC0 hC = (fourierL2inv ℝ).comp
      ((lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hφ hC0 hC).comp (fourierL2 ℝ)) := rfl
  rw [e, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, adjoint_fourierL2inv,
    adjoint_fourierL2, ← lpBoundedMulCLM_eq_adjoint_conj_general hφ hC0 hC hψ hD0 hD hconj]
  rfl

/-- A Fourier multiplier with a real symbol is self-adjoint. -/
theorem isSelfAdjoint_fourierMulCLM {φ : ℝ → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ ξ, ‖φ ξ‖ ≤ C) (hreal : ∀ ξ, (starRingEnd ℂ) (φ ξ) = φ ξ) :
    IsSelfAdjoint (fourierMulCLM hφ hC0 hC) :=
  adjoint_fourierMulCLM hφ hφ hC0 hC hC0 hC fun ξ => (hreal ξ).symm

/-! ### Convolution kernels -/

/-- The convolution kernel `g(y - z)` of an integrable measurable profile; Schur bound `‖g‖₁`. -/
def convolutionKernel (g : ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g) :
    SchurKernel (volume : Measure ℝ) where
  toFun y z := g (y - z)
  measurable := hgm.comp (measurable_fst.sub measurable_snd)
  bound := (∫⁻ x, ‖g x‖ₑ).toNNReal
  row y := by
    rw [lintegral_sub_left_eq_self (fun x => ‖g x‖ₑ) y, ENNReal.coe_toNNReal hg.2.ne]
  col z := by
    rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) z, ENNReal.coe_toNNReal hg.2.ne]

theorem convolutionKernel_toFun (g : ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g) (y z : ℝ) :
    (convolutionKernel g hgm hg).toFun y z = g (y - z) := rfl

/-- On a Schwartz function the convolution operator is the classical convolution. -/
theorem convolutionKernel_op_toLp (g : ℝ → ℂ) (hgm : Measurable g) (hg : Integrable g)
    (f : SchwartzMap ℝ ℂ) :
    ((convolutionKernel g hgm hg).op (f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume]
      ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) := by
  filter_upwards [(convolutionKernel g hgm hg).op_coeFn (f.toLp 2 volume)] with y hy
  rw [hy, SchurKernel.apply, convolution_def]
  refine integral_congr_ae ?_
  filter_upwards [f.coeFn_toLp 2 volume] with z hz
  rw [convolutionKernel_toFun, hz, ContinuousLinearMap.mul_apply', mul_comm]

/-- **A convolution operator on `L²(ℝ)` is the Fourier multiplier with symbol `𝓕 g`.** -/
theorem convolutionKernel_op_eq_fourierMulCLM (g : ℝ → ℂ) (hgm : Measurable g)
    (hg : Integrable g) :
    (convolutionKernel g hgm hg).op =
      fourierMulCLM (continuous_fourier_of_integrable' hg).measurable
        (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g) := by
  set T := (convolutionKernel g hgm hg).op
  set M := fourierMulCLM (continuous_fourier_of_integrable' hg).measurable
    (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g)
  have hdense := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (by norm_num)
    (μ := (volume : Measure ℝ))
  have key : ∀ f : SchwartzMap ℝ ℂ, T (f.toLp 2 volume) = M (f.toLp 2 volume) := by
    intro f
    have hconv : Integrable ((f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] g) :=
      f.integrable.integrable_convolution _ hg
    have hTint : Integrable (T (f.toLp 2 volume) : ℝ → ℂ) :=
      hconv.congr (convolutionKernel_op_toLp g hgm hg f).symm
    have hF1 := fourierL2_coeFn_ae_eq_fourier (T (f.toLp 2 volume)) hTint
    have hF2 : 𝓕 (T (f.toLp 2 volume) : ℝ → ℂ) = fun w => 𝓕 (f : ℝ → ℂ) w * 𝓕 g w := by
      funext w
      rw [← RHTower.fourier_mul_convolution_eq_of_integrable f.integrable hg,
        Real.fourier_real_eq, Real.fourier_real_eq]
      refine integral_congr_ae ?_
      filter_upwards [convolutionKernel_op_toLp g hgm hg f] with x hx
      rw [hx]
    have hMf : fourierL2 ℝ (M (f.toLp 2 volume)) =
        lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
          (continuous_fourier_of_integrable' hg).measurable
          (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g)
          (fourierL2 ℝ (f.toLp 2 volume)) := by
      rw [fourierMulCLM_apply, fourierL2_fourierL2inv]
    have hSf : (fourierL2 ℝ (f.toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 (f : ℝ → ℂ) := by
      change ((𝓕 (f.toLp 2 volume) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] _
      rw [SchwartzMap.toLp_fourier_eq]
      filter_upwards [(𝓕 f).coeFn_toLp 2 volume] with w hw
      rw [hw, SchwartzMap.fourier_coe]
    have hinj : fourierL2 ℝ (T (f.toLp 2 volume)) = fourierL2 ℝ (M (f.toLp 2 volume)) := by
      rw [hMf]
      refine Lp.ext ?_
      filter_upwards [hF1, lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
        (continuous_fourier_of_integrable' hg).measurable
        (integral_nonneg fun x => norm_nonneg (g x)) (norm_fourier_apply_le_integral_norm g)
        (fourierL2 ℝ (f.toLp 2 volume)), hSf] with w h1 h2 h3
      rw [h1, h2, hF2, h3, mul_comm]
    have := congrArg (fourierL2inv ℝ) hinj
    simpa only [fourierL2inv_fourierL2] using this
  have hfun := hdense.equalizer T.continuous M.continuous (funext fun f => key f)
  exact ContinuousLinearMap.ext fun f => congrFun hfun f

/-! ### Tilted kernels are commutators -/

namespace SchurKernel

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- **Coordinate commutator.**  If `k₁(y,z) = (ψ y - ψ z) k(y,z)`, then for `f ∈ L²` with
`ψ f ∈ L²` (represented by `g`), `K₁ f = ψ · K f - K g` almost everywhere: the bounded operator
`K₁` extends the commutator `[M_ψ, K]` from the domain of `M_ψ`. -/
theorem op_ae_eq_commutator (k k₁ : SchurKernel μ) (ψ : α → ℂ)
    (hk : ∀ y z, k₁.toFun y z = (ψ y - ψ z) * k.toFun y z) (f g : Lp ℂ 2 μ)
    (hg : (g : α → ℂ) =ᵐ[μ] fun z => ψ z * f z) :
    (k₁.op f : α → ℂ) =ᵐ[μ] fun y => ψ y * (k.op f : α → ℂ) y - (k.op g : α → ℂ) y := by
  filter_upwards [k₁.op_coeFn f, k.op_coeFn f, k.op_coeFn g, k.ae_integrable f,
    k.ae_integrable g] with y h1 h2 h3 hi1 hi2
  rw [h1, h2, h3, SchurKernel.apply, SchurKernel.apply, SchurKernel.apply, ← integral_const_mul]
  have hi2' : Integrable (fun z => k.toFun y z * (ψ z * f z)) μ := by
    refine hi2.congr ?_
    filter_upwards [hg] with z hz
    rw [hz]
  rw [← integral_sub (hi1.const_mul (ψ y)) hi2]
  refine integral_congr_ae ?_
  filter_upwards [hg] with z hz
  rw [hk, hz]
  ring

end SchurKernel

end GaloisForLFunctions.HTGeometry
