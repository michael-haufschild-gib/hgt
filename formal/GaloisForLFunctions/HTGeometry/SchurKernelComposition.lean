import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.HTGeometry.ExponentialFeatureTangentSpace

/-!
# Composition, Hilbert–Schmidt pairing and trace of Schur kernel operators

For Schur kernels `k₁, k₂` on an s-finite measure space:

* kernels that agree almost everywhere define the same operator (`op_eq_of_ae`);
* the composed kernel `(k₁ ∘ k₂)(y,z) = ∫ k₁(y,a) k₂(a,z) dμ(a)` is a Schur kernel with bound
  `‖k₁‖_S ‖k₂‖_S`, and its operator is `k₁.op ∘ k₂.op` (`comp_op`);
* for square-integrable kernels on a separable `L²(μ)`, the Hilbert–Schmidt pairing is the kernel
  pairing `⟨k₁.op, k₂.op⟩_HS = ∬ \bar k₁ k₂` (`hsInner_op`), and the trace of the product is
  `tr(k₁.op ∘ k₂.op) = ∬ k₁(z,y) k₂(y,z)` (`opTrace_comp_op`).

The pairing is computed row by row: for almost every `y` the row `k(y,·)` is an `L²` vector `r_y`
with `(k.op f)(y) = ⟪r̄_y, f⟫`, and Parseval in a countable Hilbert basis sums the diagonal.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

namespace SchurKernel

/-- Kernels agreeing almost everywhere define the same operator. -/
theorem op_eq_of_ae {k₁ k₂ : SchurKernel μ}
    (h : ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, k₁.toFun y z = k₂.toFun y z) : k₁.op = k₂.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [k₁.op_coeFn f, k₂.op_coeFn f, h] with y h1 h2 hy
  rw [h1, h2]
  simp only [apply]
  exact integral_congr_ae (hy.mono fun z hz => by simp only [hz])

/-! ### Composition -/

omit [SFinite μ] in
theorem measurable_comp_integrand (k₁ k₂ : SchurKernel μ) :
    Measurable (Function.uncurry fun (p : α × α) (a : α) => k₁.toFun p.1 a * k₂.toFun a p.2) :=
  (k₁.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).mul
    (k₂.measurable.comp (measurable_snd.prodMk measurable_fst.snd))

theorem measurable_comp_toFun (k₁ k₂ : SchurKernel μ) :
    Measurable (Function.uncurry fun y z => ∫ a, k₁.toFun y a * k₂.toFun a z ∂μ) :=
  ((k₁.measurable_comp_integrand k₂).stronglyMeasurable.integral_prod_right (ν := μ)).measurable

omit [SFinite μ] in
theorem enorm_integral_mul_le (k₁ k₂ : SchurKernel μ) (y z : α) :
    ‖∫ a, k₁.toFun y a * k₂.toFun a z ∂μ‖ₑ ≤ ∫⁻ a, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun _ => enorm_mul _ _))

theorem comp_row (k₁ k₂ : SchurKernel μ) (y : α) :
    ∫⁻ z, ‖∫ a, k₁.toFun y a * k₂.toFun a z ∂μ‖ₑ ∂μ ≤ ((k₁.bound * k₂.bound : ℝ≥0) : ℝ≥0∞) := by
  have hm : AEMeasurable (Function.uncurry fun z a => ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ)
      (μ.prod μ) :=
    (((k₁.measurable_left y).enorm.comp measurable_snd).mul
      (k₂.measurable.enorm.comp measurable_swap)).aemeasurable
  calc ∫⁻ z, ‖∫ a, k₁.toFun y a * k₂.toFun a z ∂μ‖ₑ ∂μ
      ≤ ∫⁻ z, ∫⁻ a, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ ∂μ ∂μ :=
        lintegral_mono fun z => k₁.enorm_integral_mul_le k₂ y z
    _ = ∫⁻ a, ∫⁻ z, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ ∂μ ∂μ := lintegral_lintegral_swap hm
    _ = ∫⁻ a, ‖k₁.toFun y a‖ₑ * ∫⁻ z, ‖k₂.toFun a z‖ₑ ∂μ ∂μ :=
        lintegral_congr fun a => lintegral_const_mul _ (k₂.measurable_left a).enorm
    _ ≤ ∫⁻ a, ‖k₁.toFun y a‖ₑ * k₂.bound ∂μ :=
        lintegral_mono fun a => by gcongr; exact k₂.row a
    _ = (∫⁻ a, ‖k₁.toFun y a‖ₑ ∂μ) * k₂.bound :=
        lintegral_mul_const _ (k₁.measurable_left y).enorm
    _ ≤ (k₁.bound : ℝ≥0∞) * k₂.bound := by gcongr; exact k₁.row y
    _ = ((k₁.bound * k₂.bound : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_mul _ _).symm

theorem comp_col (k₁ k₂ : SchurKernel μ) (z : α) :
    ∫⁻ y, ‖∫ a, k₁.toFun y a * k₂.toFun a z ∂μ‖ₑ ∂μ ≤ ((k₁.bound * k₂.bound : ℝ≥0) : ℝ≥0∞) := by
  have hm : AEMeasurable (Function.uncurry fun y a => ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ)
      (μ.prod μ) :=
    (k₁.measurable.enorm.mul ((k₂.measurable_right z).enorm.comp measurable_snd)).aemeasurable
  calc ∫⁻ y, ‖∫ a, k₁.toFun y a * k₂.toFun a z ∂μ‖ₑ ∂μ
      ≤ ∫⁻ y, ∫⁻ a, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ ∂μ ∂μ :=
        lintegral_mono fun y => k₁.enorm_integral_mul_le k₂ y z
    _ = ∫⁻ a, ∫⁻ y, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ ∂μ ∂μ := lintegral_lintegral_swap hm
    _ = ∫⁻ a, (∫⁻ y, ‖k₁.toFun y a‖ₑ ∂μ) * ‖k₂.toFun a z‖ₑ ∂μ :=
        lintegral_congr fun a => lintegral_mul_const _ (k₁.measurable_right a).enorm
    _ ≤ ∫⁻ a, (k₁.bound : ℝ≥0∞) * ‖k₂.toFun a z‖ₑ ∂μ :=
        lintegral_mono fun a => by gcongr; exact k₁.col a
    _ = (k₁.bound : ℝ≥0∞) * ∫⁻ a, ‖k₂.toFun a z‖ₑ ∂μ :=
        lintegral_const_mul _ (k₂.measurable_right z).enorm
    _ ≤ (k₁.bound : ℝ≥0∞) * k₂.bound := by gcongr; exact k₂.col z
    _ = ((k₁.bound * k₂.bound : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_mul _ _).symm

/-- The composed kernel `(k₁ ∘ k₂)(y,z) = ∫ k₁(y,a) k₂(a,z) dμ(a)`. -/
def comp (k₁ k₂ : SchurKernel μ) : SchurKernel μ where
  toFun y z := ∫ a, k₁.toFun y a * k₂.toFun a z ∂μ
  measurable := k₁.measurable_comp_toFun k₂
  bound := k₁.bound * k₂.bound
  row y := k₁.comp_row k₂ y
  col z := k₁.comp_col k₂ z

theorem comp_toFun (k₁ k₂ : SchurKernel μ) (y z : α) :
    (comp k₁ k₂).toFun y z = ∫ a, k₁.toFun y a * k₂.toFun a z ∂μ := rfl

/-- **The operator of the composed kernel is the composition of the operators.** -/
theorem comp_op (k₁ k₂ : SchurKernel μ) : (comp k₁ k₂).op = k₁.op ∘L k₂.op := by
  ext1 f
  apply Lp.ext
  have hf := (Lp.stronglyMeasurable f).measurable
  set G : α → ℝ≥0∞ := fun a => ∫⁻ z, ‖k₂.toFun a z‖ₑ * ‖(f : α → ℂ) z‖ₑ ∂μ with hGdef
  have hGm : Measurable G :=
    (k₂.measurable_enorm.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right'
  have hf2 : ∫⁻ z, ‖(f : α → ℂ) z‖ₑ ^ 2 ∂μ < ∞ := by
    have := Lp.eLpNorm_lt_top f
    rw [eLpNorm_two_eq] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this
  have hG2 : ∫⁻ a, G a ^ 2 ∂μ < ∞ :=
    (k₂.lintegral_sq_le hf).trans_lt (ENNReal.mul_lt_top (by simp) hf2)
  have hsq := lintegral_sq_kernel_le (μ := μ) (ν := μ) (K := fun y a => ‖k₁.toFun y a‖ₑ)
    (f := G) (A := k₁.bound) (B := k₁.bound) k₁.measurable_enorm hGm k₁.row k₁.col
  have hmeas : Measurable fun y => (∫⁻ a, ‖k₁.toFun y a‖ₑ * G a ∂μ) ^ 2 :=
    ((k₁.measurable_enorm.mul (hGm.comp measurable_snd)).lintegral_prod_right').pow_const 2
  have hfin : ∀ᵐ y ∂μ, (∫⁻ a, ‖k₁.toFun y a‖ₑ * G a ∂μ) ^ 2 < ∞ :=
    ae_lt_top hmeas (hsq.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.coe_lt_top) hG2)).ne
  filter_upwards [(comp k₁ k₂).op_coeFn f, k₁.op_coeFn (k₂.op f), hfin] with y h1 h2 hy
  rw [ContinuousLinearMap.comp_apply, h2, h1]
  simp only [apply, comp_toFun]
  have h3 : (fun a => k₁.toFun y a * (k₂.op f : α → ℂ) a) =ᵐ[μ]
      fun a => k₁.toFun y a * ∫ z, k₂.toFun a z * (f : α → ℂ) z ∂μ := by
    filter_upwards [k₂.op_coeFn f] with a ha
    rw [ha]
    rfl
  rw [integral_congr_ae h3]
  have hFm : Measurable (Function.uncurry fun a z => k₁.toFun y a * k₂.toFun a z *
      (f : α → ℂ) z) :=
    (((k₁.measurable_left y).comp measurable_fst).mul k₂.measurable).mul (hf.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun a z => k₁.toFun y a * k₂.toFun a z *
      (f : α → ℂ) z) (μ.prod μ) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hFm.enorm.aemeasurable]
    have hlt : ∫⁻ a, ‖k₁.toFun y a‖ₑ * G a ∂μ < ∞ := by
      by_contra hc
      rw [not_lt, top_le_iff] at hc
      rw [hc] at hy
      simp at hy
    refine lt_of_le_of_lt (le_of_eq ?_) hlt
    refine lintegral_congr fun a => ?_
    show ∫⁻ z, ‖k₁.toFun y a * k₂.toFun a z * (f : α → ℂ) z‖ₑ ∂μ = _
    simp_rw [enorm_mul]
    show _ = ‖k₁.toFun y a‖ₑ * ∫⁻ z, ‖k₂.toFun a z‖ₑ * ‖(f : α → ℂ) z‖ₑ ∂μ
    calc ∫⁻ z, ‖k₁.toFun y a‖ₑ * ‖k₂.toFun a z‖ₑ * ‖(f : α → ℂ) z‖ₑ ∂μ
        = ∫⁻ z, ‖k₁.toFun y a‖ₑ * (‖k₂.toFun a z‖ₑ * ‖(f : α → ℂ) z‖ₑ) ∂μ :=
          lintegral_congr fun z => by ring
      _ = _ := lintegral_const_mul _ ((k₂.measurable_left a).enorm.mul hf.enorm)
  calc ∫ z, (∫ a, k₁.toFun y a * k₂.toFun a z ∂μ) * (f : α → ℂ) z ∂μ
      = ∫ z, ∫ a, k₁.toFun y a * k₂.toFun a z * (f : α → ℂ) z ∂μ ∂μ :=
        integral_congr_ae (Eventually.of_forall fun z => (integral_mul_const _ _).symm)
    _ = ∫ a, ∫ z, k₁.toFun y a * k₂.toFun a z * (f : α → ℂ) z ∂μ ∂μ :=
        (integral_integral_swap hint).symm
    _ = ∫ a, k₁.toFun y a * ∫ z, k₂.toFun a z * (f : α → ℂ) z ∂μ ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun a => ?_)
        simp only
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)

/-! ### Rows of a square-integrable kernel -/

section Rows

variable (k : SchurKernel μ)

open scoped Classical in
/-- The conjugated row `z ↦ \overline{k(y,z)}` as an `L²` vector (zero when it is not in `L²`). -/
def rowVec (y : α) : Lp ℂ 2 μ :=
  if h : MemLp (fun z => (starRingEnd ℂ) (k.toFun y z)) 2 μ then h.toLp _ else 0

omit [SFinite μ] in
theorem memLp_row_of_lt_top {y : α} (hy : ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ < ∞) :
    MemLp (fun z => (starRingEnd ℂ) (k.toFun y z)) 2 μ := by
  refine ⟨(Complex.continuous_conj.measurable.comp (k.measurable_left y)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_two_eq]
  simp only [RCLike.enorm_conj]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hy.ne

theorem ae_row_lt_top (hk2 : ∫⁻ y, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) :
    ∀ᵐ y ∂μ, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ < ∞ :=
  ae_lt_top ((k.measurable_enorm.pow_const 2).lintegral_prod_right') hk2.ne

omit [SFinite μ] in
theorem rowVec_coeFn {y : α} (hy : ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ < ∞) :
    (k.rowVec y : α → ℂ) =ᵐ[μ] fun z => (starRingEnd ℂ) (k.toFun y z) := by
  rw [rowVec, dif_pos (k.memLp_row_of_lt_top hy)]
  exact MemLp.coeFn_toLp _

/-- On square-integrable rows the operator is the inner product against the conjugated row. -/
theorem op_apply_eq_inner_rowVec (hk2 : ∫⁻ y, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞)
    (f : Lp ℂ 2 μ) : ∀ᵐ y ∂μ, (k.op f : α → ℂ) y = inner ℂ (k.rowVec y) f := by
  filter_upwards [k.op_coeFn f, k.ae_row_lt_top hk2] with y h1 hy
  rw [h1, apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [k.rowVec_coeFn hy] with z hz
  rw [hz, RCLike.inner_apply, Complex.conj_conj]
  ring

end Rows

/-! ### The Hilbert–Schmidt pairing and the trace -/

omit [SFinite μ] in
theorem integral_norm_inner_le (u v : Lp ℂ 2 μ) :
    ∫ y, ‖(inner ℂ ((u : α → ℂ) y) ((v : α → ℂ) y) : ℂ)‖ ∂μ ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
  have hu : Integrable (fun y => ‖(u : α → ℂ) y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
  have hv : Integrable (fun y => ‖(v : α → ℂ) y‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  rw [norm_sq_L2_eq_integral u, norm_sq_L2_eq_integral v, ← integral_add hu hv,
    ← integral_div]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
    ((hu.add hv).div_const 2) (Eventually.of_forall fun y => ?_)
  have h := norm_inner_le_norm (𝕜 := ℂ) ((u : α → ℂ) y) ((v : α → ℂ) y)
  nlinarith [sq_nonneg (‖(u : α → ℂ) y‖ - ‖(v : α → ℂ) y‖), norm_nonneg ((u : α → ℂ) y),
    norm_nonneg ((v : α → ℂ) y)]

/-- **The Hilbert–Schmidt pairing of two square-integrable kernels** is the kernel pairing
`⟨k₁.op, k₂.op⟩_HS = ∬ \bar k₁ k₂`. -/
theorem hsInner_op [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] (k₁ k₂ : SchurKernel μ)
    (h₁ : ∫⁻ y, ∫⁻ z, ‖k₁.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞)
    (h₂ : ∫⁻ y, ∫⁻ z, ‖k₂.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) :
    ContinuousLinearMap.hsInner k₁.op k₂.op =
      ∫ y, ∫ z, (starRingEnd ℂ) (k₁.toFun y z) * k₂.toFun y z ∂μ ∂μ := by
  set b := ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 μ)
  letI : Countable (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose := b.orthonormal.countable_index
  have hS := k₁.isHilbertSchmidt_op h₁
  have hT := k₂.isHilbertSchmidt_op h₂
  set F : (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose → α → ℂ := fun i y =>
    inner ℂ ((k₁.op (b i) : α → ℂ) y) ((k₂.op (b i) : α → ℂ) y) with hFdef
  have hFint : ∀ i, Integrable (F i) μ := fun i => L2.integrable_inner _ _
  have hFsum : Summable fun i => ∫ y, ‖F i y‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
      (fun i => integral_norm_inner_le _ _) (((hS.summable b).add (hT.summable b)).div_const 2)
  have hstep : ContinuousLinearMap.hsInner k₁.op k₂.op = ∑' i, ∫ y, F i y ∂μ := by
    rw [ContinuousLinearMap.hsInner]
    exact tsum_congr fun i => L2.inner_def _ _
  rw [hstep, integral_tsum_of_summable_integral_norm hFint hFsum]
  have hall : ∀ᵐ y ∂μ, ∀ i, F i y = inner ℂ (b i) (k₁.rowVec y) * inner ℂ (k₂.rowVec y) (b i) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [k₁.op_apply_eq_inner_rowVec h₁ (b i), k₂.op_apply_eq_inner_rowVec h₂ (b i)]
      with y hy1 hy2
    simp only [hFdef, hy1, hy2, RCLike.inner_apply, inner_conj_symm]
    ring
  refine integral_congr_ae ?_
  filter_upwards [hall, k₁.ae_row_lt_top h₁, k₂.ae_row_lt_top h₂] with y hy hy1 hy2
  rw [tsum_congr hy]
  have hswap : ∀ i, inner ℂ (b i) (k₁.rowVec y) * inner ℂ (k₂.rowVec y) (b i) =
      inner ℂ (k₂.rowVec y) (b i) * inner ℂ (b i) (k₁.rowVec y) := fun i => mul_comm _ _
  rw [tsum_congr hswap, b.tsum_inner_mul_inner, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [k₁.rowVec_coeFn hy1, k₂.rowVec_coeFn hy2] with z hz1 hz2
  rw [hz1, hz2, RCLike.inner_apply, Complex.conj_conj]

omit [SFinite μ] in
theorem adjoint_toFun_sq (k : SchurKernel μ) (y z : α) :
    ‖k.adjoint.toFun y z‖ₑ ^ 2 = ‖k.toFun z y‖ₑ ^ 2 := by
  rw [adjoint_toFun, RCLike.enorm_conj]

theorem lintegral_adjoint_sq (k : SchurKernel μ) :
    ∫⁻ y, ∫⁻ z, ‖k.adjoint.toFun y z‖ₑ ^ 2 ∂μ ∂μ = ∫⁻ y, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ ∂μ := by
  simp_rw [adjoint_toFun_sq]
  exact lintegral_lintegral_swap ((k.measurable_enorm.pow_const 2).comp measurable_swap).aemeasurable

/-- **Trace of a product of square-integrable kernel operators.**
`tr(k₁.op ∘ k₂.op) = ∫_y ∫_z k₁(z,y) k₂(y,z)`. -/
theorem opTrace_comp_op [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] (k₁ k₂ : SchurKernel μ)
    (h₁ : ∫⁻ y, ∫⁻ z, ‖k₁.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞)
    (h₂ : ∫⁻ y, ∫⁻ z, ‖k₂.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) :
    ContinuousLinearMap.opTrace (k₁.op ∘L k₂.op) =
      ∫ y, ∫ z, k₁.toFun z y * k₂.toFun y z ∂μ ∂μ := by
  rw [ContinuousLinearMap.opTrace_comp_eq_hsInner, adjoint_op,
    hsInner_op k₁.adjoint k₂ ((lintegral_adjoint_sq k₁).trans_lt h₁) h₂]
  simp only [adjoint_toFun, Complex.conj_conj]


/-- The trace of `k₁† ∘ k₂` is the integral of the composed kernel along the diagonal:
`tr(k₁.op† ∘ k₂.op) = ∫_y ∫_a \bar k₁(a,y) k₂(a,y)`. -/
theorem opTrace_adjoint_comp_op [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] (k₁ k₂ : SchurKernel μ)
    (h₁ : ∫⁻ y, ∫⁻ z, ‖k₁.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞)
    (h₂ : ∫⁻ y, ∫⁻ z, ‖k₂.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) :
    ContinuousLinearMap.opTrace (k₁.adjoint.op ∘L k₂.op) =
      ∫ y, (comp k₁.adjoint k₂).toFun y y ∂μ := by
  have h₁' : ∫⁻ y, ∫⁻ z, ‖k₁.adjoint.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞ :=
    (lintegral_adjoint_sq k₁).trans_lt h₁
  rw [ContinuousLinearMap.opTrace_comp_comm (k₁.adjoint.isHilbertSchmidt_op h₁')
    (k₂.isHilbertSchmidt_op h₂), opTrace_comp_op k₂ k₁.adjoint h₂ h₁']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [comp_toFun]
  exact integral_congr_ae (Eventually.of_forall fun a => mul_comm _ _)

theorem enorm_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

/-- The diagonal of a composed kernel of two square-integrable kernels is integrable. -/
theorem integrable_comp_adjoint_diag (k₁ k₂ : SchurKernel μ)
    (h₁ : ∫⁻ y, ∫⁻ z, ‖k₁.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞)
    (h₂ : ∫⁻ y, ∫⁻ z, ‖k₂.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) :
    Integrable (fun y => (comp k₁.adjoint k₂).toFun y y) μ := by
  refine ⟨((comp k₁.adjoint k₂).measurable.comp (measurable_id.prodMk measurable_id)).aestronglyMeasurable,
    ?_⟩
  rw [HasFiniteIntegral]
  have hsw : ∀ k : SchurKernel μ, ∫⁻ y, ∫⁻ a, ‖k.toFun a y‖ₑ ^ 2 ∂μ ∂μ =
      ∫⁻ a, ∫⁻ y, ‖k.toFun a y‖ₑ ^ 2 ∂μ ∂μ := fun k =>
    lintegral_lintegral_swap ((k.measurable_enorm.pow_const 2).comp measurable_swap).aemeasurable
  calc ∫⁻ y, ‖(comp k₁.adjoint k₂).toFun y y‖ₑ ∂μ
      ≤ ∫⁻ y, ∫⁻ a, (‖k₁.toFun a y‖ₑ ^ 2 + ‖k₂.toFun a y‖ₑ ^ 2) ∂μ ∂μ := by
        refine lintegral_mono fun y => ?_
        refine (enorm_integral_mul_le k₁.adjoint k₂ y y).trans (lintegral_mono fun a => ?_)
        rw [adjoint_toFun, RCLike.enorm_conj]
        exact enorm_mul_le_sq_add_sq _ _
    _ = (∫⁻ y, ∫⁻ a, ‖k₁.toFun a y‖ₑ ^ 2 ∂μ ∂μ) + ∫⁻ y, ∫⁻ a, ‖k₂.toFun a y‖ₑ ^ 2 ∂μ ∂μ := by
        rw [← lintegral_add_left]
        · exact lintegral_congr fun y => lintegral_add_left
            ((k₁.measurable_right y).enorm.pow_const 2) _
        · exact ((k₁.measurable_enorm.pow_const 2).comp measurable_swap).lintegral_prod_right'
    _ < ∞ := by
        rw [hsw k₁, hsw k₂]
        exact ENNReal.add_lt_top.mpr ⟨h₁, h₂⟩

end SchurKernel

end

end GaloisForLFunctions.HTGeometry
