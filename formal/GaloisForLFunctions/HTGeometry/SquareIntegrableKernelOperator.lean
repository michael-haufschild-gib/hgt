import GaloisForLFunctions.HTGeometry.SchurKernelOperator
import GaloisForLFunctions.HTGeometry.MinkowskiIntegralInequality

/-!
# Square-integrable kernel operators between two `L²` spaces

A measurable kernel `k : β → α → ℂ` with finite energy `∬ |k(y, x)|² dμ(x) dν(y) < ∞` defines the
bounded operator

`(K f)(y) = ∫ k(y, x) f(x) dμ(x)`,  `K : L²(μ) → L²(ν)`,

with `‖K‖² ≤ ∬ |k|²`: for almost every `y` the row `k(y, ·)` is square integrable and
Cauchy–Schwarz bounds `|(K f)(y)|²` by its energy times `‖f‖²`.  The operator is Hilbert–Schmidt
with `‖K‖²_HS = ∬ |k|²` exactly: `(K eᵢ)(y) = ⟪r̄_y, eᵢ⟫` for the conjugate row `r̄_y`, and
Parseval in any Hilbert basis sums these to `‖r_y‖²`.

The adjoint is the kernel operator of `(x, y) ↦ conj k(y, x)`, and composition is the kernel
operator of the composed kernel `(k₂ ⋆ k₁)(z, x) = ∫ k₂(z, y) k₁(y, x) dν(y)`; both are Fubini
arguments whose integrability comes from Cauchy–Schwarz against the kernel energies.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ρ : Measure γ}

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued integrals, squared. -/
theorem sq_lintegral_mul_le_mul {δ : Type*} [MeasurableSpace δ] {m : Measure δ}
    {a b : δ → ℝ≥0∞} (ha : AEMeasurable a m) (hb : AEMeasurable b m) :
    (∫⁻ t, a t * b t ∂m) ^ 2 ≤ (∫⁻ t, a t ^ 2 ∂m) * ∫⁻ t, b t ^ 2 ∂m := by
  have h := lintegral_mul_le_sqrt_mul_sqrt (μ := m) ha hb
  calc (∫⁻ t, a t * b t ∂m) ^ 2
      ≤ ((∫⁻ t, a t ^ 2 ∂m) ^ ((1 : ℝ) / 2) * (∫⁻ t, b t ^ 2 ∂m) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ t, a t ^ 2 ∂m) * ∫⁻ t, b t ^ 2 ∂m := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc] at h
  simp at h

/-- A kernel `k : β → α → ℂ` with finite energy `∬ |k|² dμ dν`. -/
structure SqIntKernel (ν : Measure β) (μ : Measure α) where
  toFun : β → α → ℂ
  measurable : Measurable (Function.uncurry toFun)
  energy_lt_top : ∫⁻ y, ∫⁻ x, ‖toFun y x‖ₑ ^ 2 ∂μ ∂ν < ∞

namespace SqIntKernel

/-! ## The operator -/

section Operator

variable (k : SqIntKernel ν μ)

/-- The energy `∬ |k|² dμ dν`. -/
def energy : ℝ≥0∞ := ∫⁻ y, ∫⁻ x, ‖k.toFun y x‖ₑ ^ 2 ∂μ ∂ν

/-- The row energy `R(y) = ∫ |k(y, x)|² dμ(x)`. -/
def rowEnergy (y : β) : ℝ≥0∞ := ∫⁻ x, ‖k.toFun y x‖ₑ ^ 2 ∂μ

theorem energy_eq : k.energy = ∫⁻ y, k.rowEnergy y ∂ν := rfl

theorem energy_ne_top : k.energy ≠ ∞ := k.energy_lt_top.ne

theorem measurable_enorm : Measurable (Function.uncurry fun y x => ‖k.toFun y x‖ₑ) :=
  k.measurable.enorm

theorem measurable_left (y : β) : Measurable (k.toFun y) :=
  k.measurable.comp (measurable_const.prodMk measurable_id)

theorem measurable_right (x : α) : Measurable fun y => k.toFun y x :=
  k.measurable.comp (measurable_id.prodMk measurable_const)

theorem measurable_rowEnergy [SFinite μ] : Measurable k.rowEnergy :=
  (k.measurable_enorm.pow_const 2).lintegral_prod_right'

theorem ae_rowEnergy_lt_top [SFinite μ] : ∀ᵐ y ∂ν, k.rowEnergy y < ∞ :=
  ae_lt_top k.measurable_rowEnergy k.energy_ne_top

/-- The kernel action `(K f)(y) = ∫ k(y, x) f(x) dμ(x)`. -/
def apply (f : α → ℂ) (y : β) : ℂ := ∫ x, k.toFun y x * f x ∂μ

theorem enorm_apply_le (f : α → ℂ) (y : β) :
    ‖k.apply f y‖ₑ ≤ ∫⁻ x, ‖k.toFun y x‖ₑ * ‖f x‖ₑ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun _ => enorm_mul _ _))

theorem sq_lintegral_mul_le {f : α → ℂ} (hf : Measurable f) (y : β) :
    (∫⁻ x, ‖k.toFun y x‖ₑ * ‖f x‖ₑ ∂μ) ^ 2 ≤ k.rowEnergy y * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
  sq_lintegral_mul_le_mul (k.measurable_left y).enorm.aemeasurable hf.enorm.aemeasurable

theorem lintegral_enorm_apply_sq_le [SFinite μ] {f : α → ℂ} (hf : Measurable f) :
    ∫⁻ y, ‖k.apply f y‖ₑ ^ 2 ∂ν ≤ k.energy * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  calc ∫⁻ y, ‖k.apply f y‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ y, k.rowEnergy y * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ∂ν :=
        lintegral_mono fun y =>
          (pow_le_pow_left' (k.enorm_apply_le f y) 2).trans (k.sq_lintegral_mul_le hf y)
    _ = k.energy * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := lintegral_mul_const _ k.measurable_rowEnergy

theorem stronglyMeasurable_apply [SFinite μ] {f : α → ℂ} (hf : Measurable f) :
    StronglyMeasurable (k.apply f) :=
  StronglyMeasurable.integral_prod_right (f := fun y x => k.toFun y x * f x)
    (k.measurable.mul (hf.comp measurable_snd)).stronglyMeasurable

theorem eLpNorm_apply_le [SFinite μ] {f : α → ℂ} (hf : Measurable f) :
    eLpNorm (k.apply f) 2 ν ≤ k.energy ^ ((1 : ℝ) / 2) * eLpNorm f 2 μ := by
  rw [SchurKernel.eLpNorm_two_eq, SchurKernel.eLpNorm_two_eq]
  have h := ENNReal.rpow_le_rpow (k.lintegral_enorm_apply_sq_le hf)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h

theorem memLp_apply [SFinite μ] (f : Lp ℂ 2 μ) : MemLp (k.apply f) 2 ν :=
  ⟨(k.stronglyMeasurable_apply (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable,
    (k.eLpNorm_apply_le (Lp.stronglyMeasurable f).measurable).trans_lt
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) k.energy_ne_top)
        (Lp.eLpNorm_lt_top f))⟩

theorem lintegral_enorm_sq_lt_top (f : Lp ℂ 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ∞ := by
  have := Lp.eLpNorm_lt_top f
  rw [SchurKernel.eLpNorm_two_eq] at this
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this

/-- For `f ∈ L²` and almost every `y`, `x ↦ k(y, x) f(x)` is integrable. -/
theorem ae_integrable [SFinite μ] (f : Lp ℂ 2 μ) :
    ∀ᵐ y ∂ν, Integrable (fun x => k.toFun y x * f x) μ := by
  have hf := (Lp.stronglyMeasurable f).measurable
  filter_upwards [k.ae_rowEnergy_lt_top] with y hy
  refine ⟨((k.measurable_left y).mul hf).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hsq := k.sq_lintegral_mul_le hf y
  have hlt : (∫⁻ x, ‖k.toFun y x‖ₑ * ‖f x‖ₑ ∂μ) ^ 2 < ∞ :=
    hsq.trans_lt (ENNReal.mul_lt_top hy (lintegral_enorm_sq_lt_top f))
  have hlt' := lt_top_of_sq_lt_top hlt
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun _ => enorm_mul _ _)) hlt'

theorem apply_add [SFinite μ] (f g : Lp ℂ 2 μ) :
    k.apply (f + g : Lp ℂ 2 μ) =ᵐ[ν] k.apply f + k.apply g := by
  filter_upwards [k.ae_integrable f, k.ae_integrable g] with y hf hg
  simp only [apply, Pi.add_apply]
  rw [← integral_add hf hg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [hx, Pi.add_apply, mul_add]

theorem apply_smul (c : ℂ) (f : Lp ℂ 2 μ) :
    k.apply (c • f : Lp ℂ 2 μ) = c • k.apply f := by
  funext y
  simp only [apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]
  ring

/-- The bounded operator `L²(μ) → L²(ν)` of a square-integrable kernel. -/
def op [SFinite μ] : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f => (k.memLp_apply f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact (MemLp.toLp_eq_toLp_iff _ _).mpr (k.apply_add f g)
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        congr 1
        exact k.apply_smul c f }
    (k.energy.toReal ^ ((1 : ℝ) / 2)) (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have h := k.eLpNorm_apply_le (Lp.stronglyMeasurable f).measurable
      calc (eLpNorm (k.apply f) 2 ν).toReal
          ≤ (k.energy ^ ((1 : ℝ) / 2) * eLpNorm (f : α → ℂ) 2 μ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top
              (ENNReal.rpow_ne_top_of_nonneg (by norm_num) k.energy_ne_top)
              (Lp.eLpNorm_ne_top f)) h
        _ = k.energy.toReal ^ ((1 : ℝ) / 2) * (eLpNorm (f : α → ℂ) 2 μ).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_rpow])

theorem op_coeFn [SFinite μ] (f : Lp ℂ 2 μ) : (k.op f : β → ℂ) =ᵐ[ν] k.apply f :=
  MemLp.coeFn_toLp (k.memLp_apply f)

theorem norm_op_le [SFinite μ] : ‖k.op‖ ≤ k.energy.toReal ^ ((1 : ℝ) / 2) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem inner_op [SFinite μ] (g : Lp ℂ 2 ν) (f : Lp ℂ 2 μ) :
    ⟪g, k.op f⟫_ℂ = ∫ y, conj (g y) * k.apply f y ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [k.op_coeFn f] with y hy
  rw [hy, RCLike.inner_apply, mul_comm]

/-- Kernels agreeing almost everywhere define the same operator. -/
theorem op_congr [SFinite μ] {k' : SqIntKernel ν μ}
    (h : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, k.toFun y x = k'.toFun y x) : k.op = k'.op := by
  ext1 f
  refine Lp.ext ?_
  filter_upwards [k.op_coeFn f, k'.op_coeFn f, h] with y h1 h2 hy
  rw [h1, h2, apply, apply]
  refine integral_congr_ae ?_
  filter_upwards [hy] with x hx
  rw [hx]

end Operator

/-! ## Hilbert–Schmidt norm -/

section HilbertSchmidt

variable [SFinite μ] (k : SqIntKernel ν μ)

omit [SFinite μ] in
theorem memLp_conj_row {y : β} (hy : k.rowEnergy y < ∞) :
    MemLp (fun x => conj (k.toFun y x)) 2 μ := by
  refine ⟨(Complex.continuous_conj.measurable.comp (k.measurable_left y)).aestronglyMeasurable, ?_⟩
  rw [SchurKernel.eLpNorm_two_eq]
  simp only [RCLike.enorm_conj]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hy.ne

omit [SFinite μ] in
theorem ofReal_norm_conj_row_sq {y : β} (hy : k.rowEnergy y < ∞) :
    ENNReal.ofReal (‖(k.memLp_conj_row hy).toLp _‖ ^ 2) = k.rowEnergy y := by
  have hne : eLpNorm (fun x => conj (k.toFun y x)) 2 μ ≠ ∞ := (k.memLp_conj_row hy).2.ne
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top hne),
    SchurKernel.eLpNorm_two_sq]
  simp only [RCLike.enorm_conj, rowEnergy]

theorem ae_op_eq_inner (e : Lp ℂ 2 μ) :
    ∀ᵐ y ∂ν, ∀ hy : k.rowEnergy y < ∞,
      (k.op e : β → ℂ) y = ⟪(k.memLp_conj_row hy).toLp _, e⟫_ℂ := by
  filter_upwards [k.op_coeFn e] with y hy' hy
  rw [hy', apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(k.memLp_conj_row hy).coeFn_toLp] with x hx
  rw [hx, RCLike.inner_apply, Complex.conj_conj, mul_comm]

theorem ofReal_norm_op_sq (e : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖k.op e‖ ^ 2) = ∫⁻ y, ‖(k.op e : β → ℂ) y‖ₑ ^ 2 ∂ν := by
  have hne : eLpNorm (k.op e : β → ℂ) 2 ν ≠ ∞ := Lp.eLpNorm_ne_top _
  rw [Lp.norm_def, ← ENNReal.toReal_pow, ENNReal.ofReal_toReal (ENNReal.pow_ne_top hne),
    SchurKernel.eLpNorm_two_sq]

theorem ae_sum_ofReal_norm_op_sq {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (t : Finset ι) :
    ∀ᵐ y ∂ν, ∀ hy : k.rowEnergy y < ∞, ∑ i ∈ t, ‖(k.op (b i) : β → ℂ) y‖ₑ ^ 2
      = ENNReal.ofReal (∑ i ∈ t, ‖⟪b i, (k.memLp_conj_row hy).toLp _⟫_ℂ‖ ^ 2) := by
  have hall : ∀ᵐ y ∂ν, ∀ i ∈ t, ∀ hy : k.rowEnergy y < ∞,
      (k.op (b i) : β → ℂ) y = ⟪(k.memLp_conj_row hy).toLp _, b i⟫_ℂ :=
    (eventually_all_finset t).mpr fun i _ => k.ae_op_eq_inner (b i)
  filter_upwards [hall] with y hy hyR
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hy i hi hyR, norm_inner_symm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- **Bessel for kernel operators.**  `∑_{i ∈ t} ‖K eᵢ‖² ≤ ∬ |k|²` for every finite family of a
Hilbert basis. -/
theorem sum_ofReal_norm_op_sq_le {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (t : Finset ι) :
    ∑ i ∈ t, ENNReal.ofReal (‖k.op (b i)‖ ^ 2) ≤ k.energy := by
  simp_rw [k.ofReal_norm_op_sq]
  rw [← lintegral_finsetSum' t fun i _ =>
    ((Lp.stronglyMeasurable (k.op (b i))).measurable.enorm.pow_const 2).aemeasurable, energy_eq]
  refine lintegral_mono_ae ?_
  filter_upwards [k.ae_sum_ofReal_norm_op_sq b t, k.ae_rowEnergy_lt_top] with y hy hyR
  rw [hy hyR, ← k.ofReal_norm_conj_row_sq hyR]
  exact ENNReal.ofReal_le_ofReal (b.orthonormal.sum_inner_products_le _)

/-- **Parseval for kernel operators.**  `∑ᵢ ‖K eᵢ‖² = ∬ |k|²` in `ℝ≥0∞`, for every countable Hilbert
basis. -/
theorem tsum_ofReal_norm_op_sq {ι : Type*} [Countable ι] (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) :
    ∑' i, ENNReal.ofReal (‖k.op (b i)‖ ^ 2) = k.energy := by
  simp_rw [k.ofReal_norm_op_sq]
  rw [← lintegral_tsum fun i =>
    ((Lp.stronglyMeasurable (k.op (b i))).measurable.enorm.pow_const 2).aemeasurable]
  rw [energy_eq]
  refine lintegral_congr_ae ?_
  have hall : ∀ᵐ y ∂ν, ∀ i, ∀ hy : k.rowEnergy y < ∞,
      (k.op (b i) : β → ℂ) y = ⟪(k.memLp_conj_row hy).toLp _, b i⟫_ℂ := by
    rw [ae_all_iff]
    exact fun i => k.ae_op_eq_inner (b i)
  filter_upwards [hall, k.ae_rowEnergy_lt_top] with y hy hyR
  calc ∑' i, ‖(k.op (b i) : β → ℂ) y‖ₑ ^ 2
      = ∑' i, ENNReal.ofReal (‖⟪b i, (k.memLp_conj_row hyR).toLp _⟫_ℂ‖ ^ 2) := by
        refine tsum_congr fun i => ?_
        rw [hy i hyR, norm_inner_symm, ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
    _ = ENNReal.ofReal (∑' i, ‖⟪b i, (k.memLp_conj_row hyR).toLp _⟫_ℂ‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity)
          (b.summable_norm_inner_sq _)).symm
    _ = k.rowEnergy y := by
        rw [b.tsum_norm_inner_sq, k.ofReal_norm_conj_row_sq hyR]

/-- Square-integrable kernels give Hilbert–Schmidt operators. -/
theorem isHilbertSchmidt_op : ContinuousLinearMap.IsHilbertSchmidt k.op := by
  set b := ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 μ)
  show Summable fun i => ‖k.op (b i)‖ ^ 2
  refine summable_of_sum_le (fun i => sq_nonneg _) (c := k.energy.toReal) fun t => ?_
  have h := k.sum_ofReal_norm_op_sq_le b t
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity] at h
  exact (ENNReal.ofReal_le_iff_le_toReal k.energy_ne_top).mp h

/-- **`‖K‖²_HS = ∬ |k|²`** on a separable `L²(μ)`. -/
theorem hsNormSq_op [TopologicalSpace.SeparableSpace (Lp ℂ 2 μ)] :
    ContinuousLinearMap.hsNormSq k.op = k.energy.toReal := by
  set b := ContinuousLinearMap.hsBasis ℂ (Lp ℂ 2 μ)
  haveI : Countable (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose := b.orthonormal.countable_index
  have h := k.tsum_ofReal_norm_op_sq b
  rw [← h, ENNReal.tsum_toReal_eq fun i => ENNReal.ofReal_ne_top]
  exact tsum_congr fun i => (ENNReal.toReal_ofReal (by positivity)).symm

end HilbertSchmidt

/-! ## Adjoint -/

section Adjoint

variable [SFinite μ] [SFinite ν] (k : SqIntKernel ν μ)

theorem lintegral_prod_enorm_sq :
    ∫⁻ p : α × β, ‖k.toFun p.2 p.1‖ₑ ^ 2 ∂μ.prod ν = k.energy := by
  have hm : Measurable fun p : α × β => ‖k.toFun p.2 p.1‖ₑ ^ 2 :=
    (k.measurable.comp measurable_swap).enorm.pow_const 2
  rw [lintegral_prod _ hm.aemeasurable, lintegral_lintegral_swap hm.aemeasurable]
  rfl

/-- The adjoint kernel `(x, y) ↦ conj k(y, x)`. -/
def adjoint : SqIntKernel μ ν where
  toFun x y := conj (k.toFun y x)
  measurable := Complex.continuous_conj.measurable.comp (k.measurable.comp measurable_swap)
  energy_lt_top := by
    simp only [RCLike.enorm_conj]
    have hm : Measurable fun p : α × β => ‖k.toFun p.2 p.1‖ₑ ^ 2 :=
      (k.measurable.comp measurable_swap).enorm.pow_const 2
    rw [← lintegral_prod _ hm.aemeasurable]
    exact (k.lintegral_prod_enorm_sq).symm ▸ k.energy_lt_top

theorem adjoint_toFun (x : α) (y : β) : k.adjoint.toFun x y = conj (k.toFun y x) := rfl

/-- The triple product `k(y, x) conj(g y) f(x)` is integrable on `μ × ν` for `f, g ∈ L²`. -/
theorem integrable_triple (g : Lp ℂ 2 ν) (f : Lp ℂ 2 μ) :
    Integrable (fun p : α × β => k.toFun p.2 p.1 * (conj (g p.2) * f p.1)) (μ.prod ν) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hmeas : Measurable fun p : α × β => k.toFun p.2 p.1 * (conj (g p.2) * f p.1) :=
    (k.measurable.comp measurable_swap).mul
      ((Complex.continuous_conj.measurable.comp (hg.comp measurable_snd)).mul
        (hf.comp measurable_fst))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hCS := lintegral_mul_le_sqrt_mul_sqrt (μ := μ.prod ν)
    (f := fun p : α × β => ‖k.toFun p.2 p.1‖ₑ)
    (g := fun p : α × β => ‖f p.1‖ₑ * ‖g p.2‖ₑ)
    (k.measurable.comp measurable_swap).enorm.aemeasurable
    ((hf.comp measurable_fst).enorm.mul (hg.comp measurable_snd).enorm).aemeasurable
  have hprod : ∫⁻ p : α × β, (‖f p.1‖ₑ * ‖g p.2‖ₑ) ^ 2 ∂μ.prod ν
      = (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := by
    simp_rw [mul_pow]
    exact lintegral_prod_mul (hf.enorm.pow_const 2).aemeasurable
      (hg.enorm.pow_const 2).aemeasurable
  rw [k.lintegral_prod_enorm_sq, hprod] at hCS
  refine lt_of_le_of_lt (le_of_eq ?_) (hCS.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) k.energy_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (lintegral_enorm_sq_lt_top f).ne (lintegral_enorm_sq_lt_top g).ne))))
  refine lintegral_congr fun p => ?_
  rw [enorm_mul, enorm_mul, RCLike.enorm_conj]
  ring

/-- **The adjoint of a kernel operator is the kernel operator of the adjoint kernel.** -/
theorem adjoint_op : ContinuousLinearMap.adjoint k.op = k.adjoint.op := by
  refine ((ContinuousLinearMap.eq_adjoint_iff k.adjoint.op k.op).mpr fun g f => ?_).symm
  have hF := k.integrable_triple g f
  rw [k.inner_op, L2.inner_def]
  have hL : ∫ x, ⟪(k.adjoint.op g : α → ℂ) x, (f : α → ℂ) x⟫_ℂ ∂μ
      = ∫ x, ∫ y, k.toFun y x * (conj (g y) * f x) ∂ν ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [k.adjoint.op_coeFn g] with x hx
    rw [hx, RCLike.inner_apply, apply, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [adjoint_toFun, map_mul, Complex.conj_conj]
    ring
  have hR : ∫ y, conj (g y) * k.apply f y ∂ν
      = ∫ y, ∫ x, k.toFun y x * (conj (g y) * f x) ∂μ ∂ν := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [apply]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hL, hR, ← integral_prod _ hF, integral_prod_symm _ hF]

end Adjoint

/-! ## Composition -/

section Composition

variable [SFinite μ] [SFinite ν]

/-- The column energy `C(x) = ∫ |k(y, x)|² dν(y)`. -/
def colEnergy (k : SqIntKernel ν μ) (x : α) : ℝ≥0∞ := ∫⁻ y, ‖k.toFun y x‖ₑ ^ 2 ∂ν

omit [SFinite μ] in
theorem measurable_colEnergy (k : SqIntKernel ν μ) : Measurable k.colEnergy := by
  have h : Measurable (Function.uncurry fun (x : α) (y : β) => ‖k.toFun y x‖ₑ ^ 2) :=
    (k.measurable.comp measurable_swap).enorm.pow_const 2
  exact h.lintegral_prod_right'

theorem lintegral_colEnergy (k : SqIntKernel ν μ) : ∫⁻ x, k.colEnergy x ∂μ = k.energy := by
  have hm : Measurable fun p : α × β => ‖k.toFun p.2 p.1‖ₑ ^ 2 :=
    (k.measurable.comp measurable_swap).enorm.pow_const 2
  exact lintegral_lintegral_swap hm.aemeasurable

/-- The composed kernel `(k₂ ⋆ k₁)(z, x) = ∫ k₂(z, y) k₁(y, x) dν(y)`. -/
def comp (k₂ : SqIntKernel ρ ν) (k₁ : SqIntKernel ν μ) : SqIntKernel ρ μ where
  toFun z x := ∫ y, k₂.toFun z y * k₁.toFun y x ∂ν
  measurable := by
    have h : StronglyMeasurable fun q : (γ × α) × β => k₂.toFun q.1.1 q.2 * k₁.toFun q.2 q.1.2 :=
      ((k₂.measurable.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (k₁.measurable.comp (measurable_snd.prodMk measurable_fst.snd))).stronglyMeasurable
    exact h.integral_prod_right'.measurable
  energy_lt_top := by
    have hpt : ∀ z x, ‖∫ y, k₂.toFun z y * k₁.toFun y x ∂ν‖ₑ ^ 2
        ≤ k₂.rowEnergy z * k₁.colEnergy x := by
      intro z x
      refine (pow_le_pow_left' ((enorm_integral_le_lintegral_enorm _).trans
        (le_of_eq (lintegral_congr fun _ => enorm_mul _ _))) 2).trans ?_
      exact sq_lintegral_mul_le_mul (k₂.measurable_left z).enorm.aemeasurable
        (k₁.measurable_right x).enorm.aemeasurable
    calc ∫⁻ z, ∫⁻ x, ‖∫ y, k₂.toFun z y * k₁.toFun y x ∂ν‖ₑ ^ 2 ∂μ ∂ρ
        ≤ ∫⁻ z, ∫⁻ x, k₂.rowEnergy z * k₁.colEnergy x ∂μ ∂ρ :=
          lintegral_mono fun z => lintegral_mono fun x => hpt z x
      _ = k₂.energy * k₁.energy := by
          simp_rw [lintegral_const_mul _ k₁.measurable_colEnergy, lintegral_colEnergy]
          rw [lintegral_mul_const _ k₂.measurable_rowEnergy]
          rfl
      _ < ∞ := ENNReal.mul_lt_top k₂.energy_lt_top k₁.energy_lt_top

theorem comp_toFun (k₂ : SqIntKernel ρ ν) (k₁ : SqIntKernel ν μ) (z : γ) (x : α) :
    (k₂.comp k₁).toFun z x = ∫ y, k₂.toFun z y * k₁.toFun y x ∂ν := rfl

/-- **The operator of a composed kernel is the composition of the operators.** -/
theorem op_comp (k₂ : SqIntKernel ρ ν) (k₁ : SqIntKernel ν μ) :
    (k₂.comp k₁).op = k₂.op ∘L k₁.op := by
  ext1 f
  refine Lp.ext ?_
  have hf := (Lp.stronglyMeasurable f).measurable
  filter_upwards [(k₂.comp k₁).op_coeFn f, k₂.op_coeFn (k₁.op f), k₂.ae_rowEnergy_lt_top]
    with z h1 h2 hz
  rw [h1, ContinuousLinearMap.comp_apply, h2]
  have hG : Integrable (Function.uncurry fun (y : β) (x : α) =>
      k₂.toFun z y * (k₁.toFun y x * f x)) (ν.prod μ) := by
    have hmeas : Measurable (Function.uncurry fun (y : β) (x : α) =>
        k₂.toFun z y * (k₁.toFun y x * f x)) :=
      ((k₂.measurable_left z).comp measurable_fst).mul (k₁.measurable.mul (hf.comp measurable_snd))
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have hb : AEMeasurable (fun y => ∫⁻ x, ‖k₁.toFun y x‖ₑ * ‖f x‖ₑ ∂μ) ν :=
      (k₁.measurable_enorm.mul (hf.comp measurable_snd).enorm).lintegral_prod_right'.aemeasurable
    have hCS := sq_lintegral_mul_le_mul (m := ν) (k₂.measurable_left z).enorm.aemeasurable hb
    have hb2 : ∫⁻ y, (∫⁻ x, ‖k₁.toFun y x‖ₑ * ‖f x‖ₑ ∂μ) ^ 2 ∂ν
        ≤ k₁.energy * ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
      (lintegral_mono fun y => k₁.sq_lintegral_mul_le hf y).trans
        (le_of_eq (lintegral_mul_const _ k₁.measurable_rowEnergy))
    have hfin : (∫⁻ y, ‖k₂.toFun z y‖ₑ * ∫⁻ x, ‖k₁.toFun y x‖ₑ * ‖f x‖ₑ ∂μ ∂ν) ^ 2 < ∞ :=
      hCS.trans_lt (ENNReal.mul_lt_top hz ((hb2.trans_lt (ENNReal.mul_lt_top k₁.energy_lt_top
        (lintegral_enorm_sq_lt_top f)))))
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_of_sq_lt_top hfin)
    rw [lintegral_prod _ hmeas.enorm.aemeasurable]
    refine lintegral_congr fun y => ?_
    simp only [Function.uncurry_apply_pair, enorm_mul]
    rw [← lintegral_const_mul' _ _ enorm_ne_top]
  have hL : (k₂.comp k₁).apply f z = ∫ x, ∫ y, k₂.toFun z y * (k₁.toFun y x * f x) ∂ν ∂μ := by
    simp only [apply, comp_toFun]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  have hR : k₂.apply (k₁.op f) z = ∫ y, ∫ x, k₂.toFun z y * (k₁.toFun y x * f x) ∂μ ∂ν := by
    simp only [apply]
    refine integral_congr_ae ?_
    filter_upwards [k₁.op_coeFn f] with y hy
    rw [hy, apply, ← integral_const_mul]
  rw [hL, hR, integral_integral_swap hG]

end Composition

end SqIntKernel

end

end GaloisForLFunctions.HTGeometry
