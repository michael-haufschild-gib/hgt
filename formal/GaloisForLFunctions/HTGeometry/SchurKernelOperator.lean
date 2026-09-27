import Mathlib
import GaloisForLFunctions.HTGeometry.SchurTest

/-!
# Integral operators with Schur-bounded kernels on `L²(μ)`

A measurable kernel `k : α → α → ℂ` with row and column bounds

`∫ |k(y,z)| dμ(z) ≤ A`,  `∫ |k(y,z)| dμ(y) ≤ A`

defines a bounded operator `(T f)(y) = ∫ k(y,z) f(z) dμ(z)` on `L²(μ)` of norm at most `A`
(Schur's test), for any s-finite `μ`.  This module packages the operator, its pointwise formula,
the sesquilinear form `⟪g, T f⟫ = ∬ \bar g(y) k(y,z) f(z)`, the adjoint kernel, and two facts about
square-integrable kernels: they send bounded weakly null sequences to norm-null sequences, and their
matrix against a disjoint family of normalized indicators is square summable.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]

/-- A kernel with Schur row and column bounds. -/
structure SchurKernel (μ : Measure α) where
  toFun : α → α → ℂ
  measurable : Measurable (Function.uncurry toFun)
  bound : ℝ≥0
  row : ∀ y, ∫⁻ z, ‖toFun y z‖ₑ ∂μ ≤ bound
  col : ∀ z, ∫⁻ y, ‖toFun y z‖ₑ ∂μ ≤ bound

namespace SchurKernel

variable (k : SchurKernel μ)

omit [SFinite μ] in
theorem measurable_enorm : Measurable (Function.uncurry fun y z => ‖k.toFun y z‖ₑ) :=
  k.measurable.enorm

omit [SFinite μ] in
theorem measurable_left (y : α) : Measurable (k.toFun y) :=
  k.measurable.comp (measurable_const.prodMk measurable_id)

omit [SFinite μ] in
theorem measurable_right (z : α) : Measurable fun y => k.toFun y z :=
  k.measurable.comp (measurable_id.prodMk measurable_const)

/-- The kernel action `(T f)(y) = ∫ k(y,z) f(z) dμ(z)`. -/
def apply (f : α → ℂ) (y : α) : ℂ := ∫ z, k.toFun y z * f z ∂μ

/-- The Schur estimate for the modulus of the kernel. -/
theorem lintegral_sq_le {f : α → ℂ} (hf : Measurable f) :
    ∫⁻ y, (∫⁻ z, ‖k.toFun y z‖ₑ * ‖f z‖ₑ ∂μ) ^ 2 ∂μ ≤
      (k.bound : ℝ≥0∞) ^ 2 * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  have h := lintegral_sq_kernel_le (μ := μ) (ν := μ) (K := fun y z => ‖k.toFun y z‖ₑ)
    (f := fun z => ‖f z‖ₑ) (A := k.bound) (B := k.bound) k.measurable_enorm hf.enorm k.row k.col
  rwa [← sq] at h

omit [SFinite μ] in
theorem enorm_apply_le (f : α → ℂ) (y : α) :
    ‖k.apply f y‖ₑ ≤ ∫⁻ z, ‖k.toFun y z‖ₑ * ‖f z‖ₑ ∂μ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  exact lintegral_congr fun z => enorm_mul _ _

theorem stronglyMeasurable_apply {f : α → ℂ} (hf : Measurable f) :
    StronglyMeasurable (k.apply f) := by
  refine StronglyMeasurable.integral_prod_right (f := fun y z => k.toFun y z * f z) ?_
  exact (k.measurable.mul (hf.comp measurable_snd)).stronglyMeasurable

theorem lintegral_enorm_apply_sq_le {f : α → ℂ} (hf : Measurable f) :
    ∫⁻ y, ‖k.apply f y‖ₑ ^ 2 ∂μ ≤ (k.bound : ℝ≥0∞) ^ 2 * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ :=
  (lintegral_mono fun y => pow_le_pow_left' (k.enorm_apply_le f y) 2).trans (k.lintegral_sq_le hf)

omit [SFinite μ] in
theorem eLpNorm_two_eq (f : α → ℂ) :
    eLpNorm f 2 μ = (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

omit [SFinite μ] in
theorem eLpNorm_two_sq (f : α → ℂ) : eLpNorm f 2 μ ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_two_eq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_apply_le {f : α → ℂ} (hf : Measurable f) :
    eLpNorm (k.apply f) 2 μ ≤ k.bound * eLpNorm f 2 μ := by
  rw [eLpNorm_two_eq, eLpNorm_two_eq]
  have h := ENNReal.rpow_le_rpow (k.lintegral_enorm_apply_sq_le hf) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem memLp_apply (f : Lp ℂ 2 μ) : MemLp (k.apply f) 2 μ :=
  ⟨(k.stronglyMeasurable_apply (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable,
    (k.eLpNorm_apply_le (Lp.stronglyMeasurable f).measurable).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (Lp.eLpNorm_lt_top f))⟩

/-- For `f ∈ L²`, `z ↦ k(y,z) f(z)` is integrable for almost every `y`. -/
theorem ae_integrable (f : Lp ℂ 2 μ) :
    ∀ᵐ y ∂μ, Integrable (fun z => k.toFun y z * f z) μ := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hfin : ∫⁻ y, (∫⁻ z, ‖k.toFun y z‖ₑ * ‖f z‖ₑ ∂μ) ^ 2 ∂μ ≠ ∞ :=
    ((k.lintegral_sq_le hf).trans_lt (ENNReal.mul_lt_top (by simp)
      (by
        have := Lp.eLpNorm_lt_top f
        rw [eLpNorm_two_eq] at this
        exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this))).ne
  have hmeas : Measurable fun y => (∫⁻ z, ‖k.toFun y z‖ₑ * ‖f z‖ₑ ∂μ) ^ 2 :=
    ((k.measurable_enorm.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right').pow_const 2
  filter_upwards [ae_lt_top hmeas hfin] with y hy
  refine ⟨((k.measurable_left y).mul hf).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hlt : ∫⁻ z, ‖k.toFun y z‖ₑ * ‖f z‖ₑ ∂μ < ∞ := by
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hy
    simp at hy
  refine lt_of_le_of_lt (le_of_eq ?_) hlt
  exact lintegral_congr fun z => enorm_mul _ _

theorem apply_add (f g : Lp ℂ 2 μ) :
    k.apply (f + g : Lp ℂ 2 μ) =ᵐ[μ] k.apply f + k.apply g := by
  filter_upwards [k.ae_integrable f, k.ae_integrable g] with y hf hg
  simp only [apply, Pi.add_apply]
  rw [← integral_add hf hg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add f g] with z hz
  rw [hz, Pi.add_apply, mul_add]

omit [SFinite μ] in
theorem apply_smul (c : ℂ) (f : Lp ℂ 2 μ) :
    k.apply (c • f : Lp ℂ 2 μ) = c • k.apply f := by
  funext y
  simp only [apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c f] with z hz
  rw [hz, Pi.smul_apply, smul_eq_mul]
  ring

/-- The bounded operator of a Schur kernel. -/
def op : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
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
    k.bound (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have h := k.eLpNorm_apply_le (Lp.stronglyMeasurable f).measurable
      calc (eLpNorm (k.apply f) 2 μ).toReal
          ≤ ((k.bound : ℝ≥0∞) * eLpNorm (f : α → ℂ) 2 μ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
              (Lp.eLpNorm_ne_top f)) h
        _ = k.bound * (eLpNorm (f : α → ℂ) 2 μ).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.coe_toReal])

theorem op_coeFn (f : Lp ℂ 2 μ) : (k.op f : α → ℂ) =ᵐ[μ] k.apply f :=
  MemLp.coeFn_toLp (k.memLp_apply f)

theorem norm_op_le : ‖k.op‖ ≤ k.bound :=
  LinearMap.mkContinuous_norm_le _ k.bound.2 _

/-! ### The sesquilinear form and the adjoint -/

theorem lintegral_triple_lt_top (f g : Lp ℂ 2 μ) :
    ∫⁻ y, ‖(g : α → ℂ) y‖ₑ * ∫⁻ z, ‖k.toFun y z‖ₑ * ‖(f : α → ℂ) z‖ₑ ∂μ ∂μ < ∞ := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hI : Measurable fun y => ∫⁻ z, ‖k.toFun y z‖ₑ * ‖(f : α → ℂ) z‖ₑ ∂μ :=
    (k.measurable_enorm.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right'
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg.enorm.aemeasurable
    hI.aemeasurable
  refine lt_of_le_of_lt h (ENNReal.mul_lt_top ?_ ?_)
  · have := Lp.eLpNorm_lt_top g
    rw [eLpNorm_two_eq] at this
    simpa [ENNReal.rpow_two] using this
  · have h2 := (k.lintegral_sq_le hf).trans_lt (ENNReal.mul_lt_top (by simp) (by
      have := Lp.eLpNorm_lt_top f
      rw [eLpNorm_two_eq] at this
      exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp this))
    simp only [ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.ne

theorem integrable_triple (f g : Lp ℂ 2 μ) :
    Integrable (fun p : α × α => (starRingEnd ℂ) ((g : α → ℂ) p.1) * k.toFun p.1 p.2 *
      (f : α → ℂ) p.2) (μ.prod μ) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hg := (Lp.stronglyMeasurable g).measurable
  have hmeas : Measurable fun p : α × α => (starRingEnd ℂ) ((g : α → ℂ) p.1) *
      k.toFun p.1 p.2 * (f : α → ℂ) p.2 :=
    ((Complex.continuous_conj.measurable.comp (hg.comp measurable_fst)).mul k.measurable).mul
      (hf.comp measurable_snd)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hmeas.enorm.aemeasurable]
  refine lt_of_le_of_lt (le_of_eq ?_) (k.lintegral_triple_lt_top f g)
  refine lintegral_congr fun y => ?_
  show ∫⁻ z, ‖(starRingEnd ℂ) ((g : α → ℂ) y) * k.toFun y z * (f : α → ℂ) z‖ₑ ∂μ = _
  simp_rw [enorm_mul, RCLike.enorm_conj]
  have hm : Measurable fun z => ‖k.toFun y z‖ₑ * ‖(f : α → ℂ) z‖ₑ :=
    (k.measurable_left y).enorm.mul hf.enorm
  rw [← lintegral_const_mul _ hm]
  exact lintegral_congr fun z => by ring

/-- `⟪g, T f⟫ = ∬ \bar g(y) k(y,z) f(z)`. -/
theorem inner_op (f g : Lp ℂ 2 μ) :
    inner ℂ g (k.op f) = ∫ y, ∫ z, (starRingEnd ℂ) ((g : α → ℂ) y) * k.toFun y z *
      (f : α → ℂ) z ∂μ ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [k.op_coeFn f] with y hy
  rw [hy, RCLike.inner_apply, apply, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

/-- The adjoint kernel `k*(y,z) = \overline{k(z,y)}`. -/
def adjoint : SchurKernel μ where
  toFun y z := (starRingEnd ℂ) (k.toFun z y)
  measurable := Complex.continuous_conj.measurable.comp (k.measurable.comp measurable_swap)
  bound := k.bound
  row y := by simpa only [RCLike.enorm_conj] using k.col y
  col z := by simpa only [RCLike.enorm_conj] using k.row z

omit [SFinite μ] in
theorem adjoint_toFun (y z : α) : k.adjoint.toFun y z = (starRingEnd ℂ) (k.toFun z y) := rfl

/-- The operator of the adjoint kernel is the Hilbert adjoint. -/
theorem adjoint_op : ContinuousLinearMap.adjoint k.op = k.adjoint.op := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have hint : Integrable (Function.uncurry fun a b => (starRingEnd ℂ) ((x : α → ℂ) a) *
      k.toFun a b * (y : α → ℂ) b) (μ.prod μ) := k.integrable_triple y x
  rw [← inner_conj_symm, k.adjoint.inner_op, k.inner_op, integral_integral_swap hint,
    ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [adjoint_toFun, map_mul, Complex.conj_conj]
  ring

/-- A Hermitian kernel gives a self-adjoint operator. -/
theorem isSelfAdjoint_op (h : ∀ y z, (starRingEnd ℂ) (k.toFun z y) = k.toFun y z) :
    IsSelfAdjoint k.op := by
  have hk : k.adjoint = k := by
    cases k with
    | mk toFun measurable bound row col =>
      simp only [adjoint, mk.injEq, and_true]
      funext y z
      exact h y z
  change ContinuousLinearMap.adjoint k.op = k.op
  rw [adjoint_op, hk]

/-- The sum of two Schur kernels. -/
def add (k₁ k₂ : SchurKernel μ) : SchurKernel μ where
  toFun y z := k₁.toFun y z + k₂.toFun y z
  measurable := k₁.measurable.add k₂.measurable
  bound := k₁.bound + k₂.bound
  row y := by
    refine (lintegral_mono fun z => enorm_add_le _ _).trans ?_
    rw [lintegral_add_left (k₁.measurable_left y).enorm, ENNReal.coe_add]
    exact add_le_add (k₁.row y) (k₂.row y)
  col z := by
    refine (lintegral_mono fun y => enorm_add_le _ _).trans ?_
    rw [lintegral_add_left (k₁.measurable_right z).enorm, ENNReal.coe_add]
    exact add_le_add (k₁.col z) (k₂.col z)

theorem add_op (k₁ k₂ : SchurKernel μ) : (add k₁ k₂).op = k₁.op + k₂.op := by
  ext1 f
  apply Lp.ext
  filter_upwards [(add k₁ k₂).op_coeFn f, k₁.op_coeFn f, k₂.op_coeFn f,
    Lp.coeFn_add (k₁.op f) (k₂.op f), k₁.ae_integrable f, k₂.ae_integrable f]
    with y h h1 h2 h3 i1 i2
  rw [_root_.add_apply, h3, Pi.add_apply, h, h1, h2]
  simp only [apply, add]
  rw [← integral_add i1 i2]
  exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)

/-! ### Square-integrable kernels -/

/-- A square-integrable kernel sends bounded weakly null sequences to norm-null sequences. -/
theorem tendsto_norm_op_of_weaklyNull
    (hk2 : ∫⁻ y, ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ ∂μ < ∞) {φ : ℕ → Lp ℂ 2 μ}
    (hb : ∀ n, ‖φ n‖ ≤ 1) (hw : ∀ g : Lp ℂ 2 μ, Tendsto (fun n => inner ℂ g (φ n)) atTop (𝓝 0)) :
    Tendsto (fun n => ‖k.op (φ n)‖) atTop (𝓝 0) := by
  set R : α → ℝ≥0∞ := fun y => ∫⁻ z, ‖k.toFun y z‖ₑ ^ 2 ∂μ
  have hRm : Measurable R := (k.measurable_enorm.pow_const 2).lintegral_prod_right'
  have hRfin : ∀ᵐ y ∂μ, R y < ∞ := ae_lt_top hRm hk2.ne
  -- the kernel rows as `L²` vectors
  have hrow : ∀ y, R y < ∞ → MemLp (fun z => (starRingEnd ℂ) (k.toFun y z)) 2 μ := by
    intro y hy
    refine ⟨(Complex.continuous_conj.measurable.comp (k.measurable_left y)).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_two_eq]
    simp only [RCLike.enorm_conj]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hy.ne
  have hpt : ∀ᵐ y ∂μ, ∀ n, (k.op (φ n) : α → ℂ) y = k.apply (φ n) y :=
    ae_all_iff.mpr fun n => k.op_coeFn (φ n)
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n => ‖(k.op (φ n) : α → ℂ) y‖ₑ ^ 2) atTop (𝓝 0) := by
    filter_upwards [hRfin, hpt] with y hy hpty
    have hin : ∀ n, k.apply (φ n) y = inner ℂ ((hrow y hy).toLp _) (φ n) := by
      intro n
      rw [L2.inner_def, apply]
      refine integral_congr_ae ?_
      filter_upwards [(hrow y hy).coeFn_toLp] with z hz
      rw [hz, RCLike.inner_apply, Complex.conj_conj]
      ring
    have h := hw ((hrow y hy).toLp _)
    have h2 : Tendsto (fun n => ‖(k.op (φ n) : α → ℂ) y‖ₑ) atTop (𝓝 0) := by
      have := (continuous_enorm.tendsto 0).comp h
      simp only [enorm_zero, Function.comp_def] at this
      refine this.congr fun n => ?_
      rw [hpty n, hin n]
    have h3 := ((ENNReal.continuous_pow 2).tendsto 0).comp h2
    rw [zero_pow two_ne_zero] at h3
    exact h3
  have hbound : ∀ n, (fun y => ‖(k.op (φ n) : α → ℂ) y‖ₑ ^ 2) ≤ᵐ[μ] R := by
    intro n
    filter_upwards [hpt] with y hpty
    rw [hpty n]
    refine (pow_le_pow_left' (k.enorm_apply_le (φ n) y) 2).trans ?_
    have hf := (Lp.stronglyMeasurable (φ n)).measurable
    have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
      (k.measurable_left y).enorm.aemeasurable hf.enorm.aemeasurable
    have hφ : (∫⁻ z, ‖(φ n : α → ℂ) z‖ₑ ^ (2 : ℝ) ∂μ) ≤ 1 := by
      have h1 : eLpNorm (φ n : α → ℂ) 2 μ ≤ 1 := by
        have := hb n
        rw [Lp.norm_def] at this
        exact (ENNReal.toReal_le_toReal (Lp.eLpNorm_ne_top _) ENNReal.one_ne_top).mp
          (by simpa using this)
      simp only [ENNReal.rpow_two]
      rw [← eLpNorm_two_sq]
      exact pow_le_one₀ bot_le h1
    calc (∫⁻ z, ‖k.toFun y z‖ₑ * ‖(φ n : α → ℂ) z‖ₑ ∂μ) ^ 2
        ≤ ((∫⁻ z, ‖k.toFun y z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫⁻ z, ‖(φ n : α → ℂ) z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) ^ 2 :=
          pow_le_pow_left' hCS 2
      _ ≤ ((∫⁻ z, ‖k.toFun y z‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * 1) ^ 2 := by
          gcongr
          exact ENNReal.rpow_le_one hφ (by norm_num)
      _ = R y := by
          rw [mul_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          simp [R]
  have hdom := tendsto_lintegral_of_dominated_convergence R
    (fun n => ((Lp.stronglyMeasurable (k.op (φ n))).measurable.enorm.pow_const 2)) hbound
    hk2.ne hlim
  rw [lintegral_zero] at hdom
  have h4 := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp hdom
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h4
  have h5 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h4
  rw [ENNReal.toReal_zero] at h5
  refine h5.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [Lp.norm_def, eLpNorm_two_eq]

omit [SFinite μ] in
/-- Cauchy–Schwarz against the constant function: `(∫ g)² ≤ ν(univ) ∫ g²`. -/
theorem sq_lintegral_le_measure_mul {β : Type*} [MeasurableSpace β] (ν : Measure β)
    {g : β → ℝ≥0∞} (hg : AEMeasurable g ν) :
    (∫⁻ x, g x ∂ν) ^ 2 ≤ ν Set.univ * ∫⁻ x, g x ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two (f := fun _ => 1)
    (g := g) aemeasurable_const hg
  simp only [Pi.mul_apply, one_mul, one_pow, lintegral_const, ENNReal.rpow_two] at h
  calc (∫⁻ x, g x ∂ν) ^ 2
      ≤ ((ν Set.univ) ^ (1 / (2 : ℝ)) * (∫⁻ x, g x ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left' h 2
    _ = ν Set.univ * ∫⁻ x, g x ^ 2 ∂ν := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-! ### Normalized cell indicators -/

section Cells

variable {ι : Type*} (I : ι → Set α) (hI : ∀ i, MeasurableSet (I i)) (hfin : ∀ i, μ (I i) ≠ ∞)

/-- The normalization constant `μ(I)^{-1/2}`. -/
def cellConst (i : ι) : ℝ := (μ (I i)).toReal ^ (-(1 / 2 : ℝ))

/-- The normalized cell indicator `μ(I)^{-1/2} 1_I`. -/
def cellVec (i : ι) : Lp ℂ 2 μ := indicatorConstLp 2 (hI i) (hfin i) ((cellConst (μ := μ) I i : ℝ) : ℂ)

omit [SFinite μ] in
theorem cellConst_sq_mul {i : ι} (hpos : μ (I i) ≠ 0) (hfin' : μ (I i) ≠ ∞) :
    cellConst (μ := μ) I i ^ 2 * (μ (I i)).toReal = 1 := by
  have h : 0 < (μ (I i)).toReal := ENNReal.toReal_pos hpos hfin'
  rw [cellConst, ← Real.rpow_natCast, ← Real.rpow_mul h.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

omit [SFinite μ] in
/-- Disjoint cells of positive finite measure give an orthonormal family. -/
theorem orthonormal_cellVec (hpos : ∀ i, μ (I i) ≠ 0) (hdisj : Pairwise (Function.onFun Disjoint I)) :
    Orthonormal ℂ (cellVec I hI hfin) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [cellVec, cellVec, L2.inner_indicatorConstLp_indicatorConstLp (hI i) (hI j) (hfin i) (hfin j)]
  split_ifs with hij
  · subst hij
    rw [Set.inter_self, RCLike.inner_apply, Complex.conj_ofReal, Measure.real, Complex.real_smul,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    have := cellConst_sq_mul I (hpos i) (hfin i)
    rw [show (cellConst (μ := μ) I i * cellConst (μ := μ) I i) = cellConst (μ := μ) I i ^ 2 by ring,
      mul_comm, this, Complex.ofReal_one]
  · rw [(hdisj hij).inter_eq, Measure.real, measure_empty, ENNReal.toReal_zero, zero_smul]

theorem inner_cellVec_op (i j : ι) :
    inner ℂ (cellVec I hI hfin i) (k.op (cellVec I hI hfin j)) =
      ((cellConst (μ := μ) I i * cellConst (μ := μ) I j : ℝ) : ℂ) *
        ∫ y in I i, ∫ z in I j, k.toFun y z ∂μ ∂μ := by
  rw [k.inner_op]
  have hi : (cellVec I hI hfin i : α → ℂ) =ᵐ[μ] (I i).indicator
      (fun _ => ((cellConst (μ := μ) I i : ℝ) : ℂ)) := indicatorConstLp_coeFn
  have hj : (cellVec I hI hfin j : α → ℂ) =ᵐ[μ] (I j).indicator
      (fun _ => ((cellConst (μ := μ) I j : ℝ) : ℂ)) := indicatorConstLp_coeFn
  have inner_eq : ∀ y, ∫ z, (starRingEnd ℂ) ((cellVec I hI hfin i : α → ℂ) y) * k.toFun y z *
      (cellVec I hI hfin j : α → ℂ) z ∂μ =
      (starRingEnd ℂ) ((cellVec I hI hfin i : α → ℂ) y) * ((cellConst (μ := μ) I j : ℝ) : ℂ) *
        ∫ z in I j, k.toFun y z ∂μ := by
    intro y
    rw [mul_assoc, ← integral_const_mul, ← integral_indicator (hI j), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hj] with z hz
    rw [hz]
    by_cases hzj : z ∈ I j
    · simp only [Set.indicator_of_mem hzj]; ring
    · simp only [Set.indicator_of_notMem hzj, mul_zero]
  simp_rw [inner_eq]
  rw [← integral_indicator (hI i), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hi] with y hy
  rw [hy]
  by_cases hyi : y ∈ I i
  · simp only [Set.indicator_of_mem hyi, Complex.conj_ofReal]
    push_cast; ring
  · simp only [Set.indicator_of_notMem hyi, map_zero, zero_mul, mul_zero]

omit [SFinite μ] in
theorem enorm_setIntegral_setIntegral_le (i j : ι) :
    ‖∫ y in I i, ∫ z in I j, k.toFun y z ∂μ ∂μ‖ₑ ≤
      ∫⁻ y in I i, ∫⁻ z in I j, ‖k.toFun y z‖ₑ ∂μ ∂μ :=
  (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun _ =>
    enorm_integral_le_lintegral_enorm _)

/-- **Cell Hilbert–Schmidt bound.** Each cell matrix element is controlled by the kernel mass on
the corresponding rectangle. -/
theorem enorm_inner_cellVec_op_sq_le (hpos : ∀ i, μ (I i) ≠ 0) (i j : ι) :
    ‖inner ℂ (cellVec I hI hfin i) (k.op (cellVec I hI hfin j))‖ₑ ^ 2 ≤
      ∫⁻ p in I i ×ˢ I j, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ) := by
  rw [inner_cellVec_op, enorm_mul, mul_pow]
  have hrect : ∫⁻ y in I i, ∫⁻ z in I j, ‖k.toFun y z‖ₑ ∂μ ∂μ =
      ∫⁻ p in I i ×ˢ I j, ‖k.toFun p.1 p.2‖ₑ ∂(μ.prod μ) := by
    rw [← Measure.prod_restrict, lintegral_prod (fun p : α × α => ‖k.toFun p.1 p.2‖ₑ)
      (by exact k.measurable_enorm.aemeasurable)]
  have hCS := sq_lintegral_le_measure_mul ((μ.prod μ).restrict (I i ×ˢ I j))
    (g := fun p => ‖k.toFun p.1 p.2‖ₑ) (by exact k.measurable_enorm.aemeasurable)
  rw [Measure.restrict_apply_univ, Measure.prod_prod] at hCS
  have hmass : ‖((cellConst (μ := μ) I i * cellConst (μ := μ) I j : ℝ) : ℂ)‖ₑ ^ 2 *
      (μ (I i) * μ (I j)) = 1 := by
    have hci := cellConst_sq_mul I (hpos i) (hfin i)
    have hcj := cellConst_sq_mul I (hpos j) (hfin j)
    have h0i : 0 ≤ cellConst (μ := μ) I i := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h0j : 0 ≤ cellConst (μ := μ) I j := Real.rpow_nonneg ENNReal.toReal_nonneg _
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg h0i h0j), ← ENNReal.ofReal_toReal (hfin i), ← ENNReal.ofReal_toReal (hfin j),
      ← ENNReal.ofReal_pow (mul_nonneg h0i h0j), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show (cellConst (μ := μ) I i * cellConst (μ := μ) I j) ^ 2 *
        ((μ (I i)).toReal * (μ (I j)).toReal) =
        (cellConst (μ := μ) I i ^ 2 * (μ (I i)).toReal) *
          (cellConst (μ := μ) I j ^ 2 * (μ (I j)).toReal) by ring, hci, hcj]
    simp
  calc ‖((cellConst (μ := μ) I i * cellConst (μ := μ) I j : ℝ) : ℂ)‖ₑ ^ 2 *
        ‖∫ y in I i, ∫ z in I j, k.toFun y z ∂μ ∂μ‖ₑ ^ 2
      ≤ ‖((cellConst (μ := μ) I i * cellConst (μ := μ) I j : ℝ) : ℂ)‖ₑ ^ 2 *
          (∫⁻ p in I i ×ˢ I j, ‖k.toFun p.1 p.2‖ₑ ∂(μ.prod μ)) ^ 2 := by
        gcongr
        rw [← hrect]
        exact enorm_setIntegral_setIntegral_le k I i j
    _ ≤ ‖((cellConst (μ := μ) I i * cellConst (μ := μ) I j : ℝ) : ℂ)‖ₑ ^ 2 *
          ((μ (I i) * μ (I j)) * ∫⁻ p in I i ×ˢ I j, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ)) := by
        gcongr
    _ = _ := by rw [← mul_assoc, hmass, one_mul]

/-- **Square-summable cell matrix.** For disjoint cells the squared matrix elements over any finite
set of index pairs are bounded by the total square mass of the kernel. -/
theorem sum_enorm_inner_cellVec_op_sq_le (hpos : ∀ i, μ (I i) ≠ 0)
    (hdisj : Pairwise (Function.onFun Disjoint I)) (s : Finset (ι × ι)) :
    ∑ q ∈ s, ‖inner ℂ (cellVec I hI hfin q.1) (k.op (cellVec I hI hfin q.2))‖ₑ ^ 2 ≤
      ∫⁻ p, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ) := by
  have hrect : (s : Set (ι × ι)).PairwiseDisjoint fun q => I q.1 ×ˢ I q.2 := by
    intro q _ q' _ hqq'
    rcases q with ⟨a, b⟩
    rcases q' with ⟨a', b'⟩
    by_cases ha : a = a'
    · subst ha
      have hb : b ≠ b' := fun h => hqq' (by rw [h])
      exact Set.disjoint_prod.mpr (Or.inr (hdisj hb))
    · exact Set.disjoint_prod.mpr (Or.inl (hdisj ha))
  calc ∑ q ∈ s, ‖inner ℂ (cellVec I hI hfin q.1) (k.op (cellVec I hI hfin q.2))‖ₑ ^ 2
      ≤ ∑ q ∈ s, ∫⁻ p in I q.1 ×ˢ I q.2, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ) :=
        Finset.sum_le_sum fun q _ => k.enorm_inner_cellVec_op_sq_le I hI hfin hpos q.1 q.2
    _ = ∫⁻ p in ⋃ q ∈ s, I q.1 ×ˢ I q.2, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ) :=
        (lintegral_biUnion_finset hrect (fun q _ => (hI q.1).prod (hI q.2)) _).symm
    _ ≤ ∫⁻ p, ‖k.toFun p.1 p.2‖ₑ ^ 2 ∂(μ.prod μ) := setLIntegral_le_lintegral _ _

end Cells

end SchurKernel

end

end GaloisForLFunctions.HTGeometry
