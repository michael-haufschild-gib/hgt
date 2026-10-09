import GaloisForLFunctions.HTGeometry.CompactKernelAlgebra
import GaloisForLFunctions.RHTower.ConnesKernelOperatorGeneral
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The integral representation of the compact kernel algebra on `L²(ℝ)`

A continuous compactly supported kernel `k` acts on `L²(ℝ)` by `(T_k ξ)(x) = ∫ k(x, y) ξ(y) dy`:

* the conjugate rows `y ↦ conj k(x, y)` form a continuous compactly supported field in `L²(ℝ)`, so
  `x ↦ ⟨row x, ·⟩` is a square-integrable field of functionals and `T_k` is the corresponding
  Hilbert–Schmidt (hence compact) operator;
* on the dense core `C_c(ℝ) ⊆ L²(ℝ)` the operator is the explicit integral, which proves
  `T_{k₁ k₂} = T_{k₁} T_{k₂}` and `T_{k*} = T_k†` (Fubini), so `k ↦ T_k` is a `*`-representation;
* **Schur's test**: `‖T_k‖ ≤ ‖k‖₁ = ∫ ‖F(s, ·)‖_∞ ds`, the `L¹(ℝ, C₀(ℝ))` norm of `k` in the twisted
  convolution picture `F(s, x) = k(x, x - s)` (row and column integrals are both bounded by it);
* the rank-one kernels `φ(x) conj ψ(y)` are matrix units, `e_{φψ} e_{φ'ψ'} = ⟨ψ, φ'⟩ e_{φψ'}`,
  `e_{φψ}* = e_{ψφ}`, and act as the rank-one operators `|φ⟩⟨ψ|`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal CompactlySupported

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance factTwoNeTopKernelL2 : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- `L²(ℝ)`. -/
abbrev L2Real : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- A continuous compactly supported function as an element of `L²(ℝ)`. -/
def ccToL2 {g : ℝ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) : L2Real :=
  (hg.memLp_of_hasCompactSupport hs).toLp g

theorem ccToL2_ae {g : ℝ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) :
    (ccToL2 hg hs : ℝ → ℂ) =ᵐ[volume] g :=
  MemLp.coeFn_toLp _

/-- The `L²` norm of a function bounded by `C` and vanishing off a compact set `S` is at most
`C √|S|`. -/
theorem norm_ccToL2_le {g : ℝ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) {S : Set ℝ}
    (hS : IsCompact S) (hgS : ∀ y ∉ S, g y = 0) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖g y‖ ≤ C) :
    ‖ccToL2 hg hs‖ ≤ C * ((volume S).toReal) ^ (1 / 2 : ℝ) := by
  rw [ccToL2, Lp.norm_toLp]
  have hsub : Function.support g ⊆ S := fun y hy => by
    by_contra h
    exact hy (hgS y h)
  rw [← eLpNorm_restrict_eq_of_support_subset hsub]
  have hb : ∀ᵐ y ∂(volume.restrict S), ‖g y‖ ≤ C := Filter.Eventually.of_forall hC
  have h := eLpNorm_le_of_ae_bound (p := 2) hb
  have hfin : volume S ≠ ⊤ := hS.measure_lt_top.ne
  rw [Measure.restrict_apply_univ] at h
  refine (ENNReal.toReal_mono (by
    refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hfin) h).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_rpow]
  norm_num
  ring

theorem ccToL2_sub {g g' : ℝ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g)
    (hg' : Continuous g') (hs' : HasCompactSupport g') :
    ccToL2 hg hs - ccToL2 hg' hs' = ccToL2 (hg.sub hg') (hs.sub hs') :=
  (MemLp.toLp_sub _ _).symm

/-- The inner product with a continuous compactly supported function. -/
theorem inner_ccToL2 {g : ℝ → ℂ} (hg : Continuous g) (hs : HasCompactSupport g) (ξ : L2Real) :
    inner ℂ (ccToL2 hg hs) ξ = ∫ y, star (g y) * ξ y := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ccToL2_ae hg hs] with y hy
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]

namespace KernelAlg

/-- The underlying compactly supported continuous kernel. -/
def toCc (k : KernelAlg) : C_c(ℝ × ℝ, ℂ) := k

theorem toFun_eq (k : KernelAlg) (p : ℝ × ℝ) : k.toFun p = k.toCc p := rfl

theorem continuous_conjRow (k : KernelAlg) (x : ℝ) : Continuous fun y => star (k.toFun (x, y)) :=
  (k.continuous_toFun.comp (continuous_const.prodMk continuous_id)).star

theorem toFun_eq_zero_of_snd (k : KernelAlg) {x y : ℝ}
    (hy : y ∉ KernelCore.sndSupp k.toCc) : k.toFun (x, y) = 0 :=
  KernelCore.eq_zero_of_snd_notMem _ hy

theorem toFun_eq_zero_of_fst (k : KernelAlg) {x y : ℝ}
    (hx : x ∉ KernelCore.fstSupp k.toCc) : k.toFun (x, y) = 0 :=
  KernelCore.eq_zero_of_fst_notMem _ hx

theorem hasCompactSupport_conjRow (k : KernelAlg) (x : ℝ) :
    HasCompactSupport fun y => star (k.toFun (x, y)) :=
  HasCompactSupport.intro (KernelCore.isCompact_sndSupp k.toCc) fun y hy => by
    simp [k.toFun_eq_zero_of_snd hy]

/-- The conjugate row `y ↦ conj k(x, y)` of a kernel, in `L²(ℝ)`. -/
def row (k : KernelAlg) (x : ℝ) : L2Real := ccToL2 (k.continuous_conjRow x) (k.hasCompactSupport_conjRow x)

theorem row_eq_zero (k : KernelAlg) {x : ℝ}
    (hx : x ∉ KernelCore.fstSupp k.toCc) : k.row x = 0 := by
  have h : (fun y => star (k.toFun (x, y))) = fun _ => 0 := funext fun y => by
    simp [k.toFun_eq_zero_of_fst hx]
  unfold row ccToL2
  simp only [h]
  exact MemLp.toLp_zero _

theorem continuous_row (k : KernelAlg) : Continuous k.row := by
  have huc := (k.hasCompactSupport_toFun).uniformContinuous_of_continuous k.continuous_toFun
  set S := KernelCore.sndSupp k.toCc
  have hS : IsCompact S := KernelCore.isCompact_sndSupp k.toCc
  set m : ℝ := ((volume S).toReal) ^ (1 / 2 : ℝ)
  have hm : 0 ≤ m := by positivity
  refine Metric.continuous_iff.mpr fun x ε hε => ?_
  obtain ⟨δ, hδ, hδk⟩ := Metric.uniformContinuous_iff.mp huc (ε / (2 * (m + 1)))
    (by positivity)
  refine ⟨δ, hδ, fun x' hx' => ?_⟩
  rw [dist_eq_norm, row, row, ccToL2_sub]
  refine (norm_ccToL2_le _ _ hS (fun y hy => by
    simp [k.toFun_eq_zero_of_snd hy]) (by positivity : (0 : ℝ) ≤ ε / (2 * (m + 1)))
    fun y => ?_).trans_lt ?_
  · have h := hδk (a := (x', y)) (b := (x, y)) (by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      exact hx')
    rw [dist_eq_norm] at h
    simp only [Pi.sub_apply]
    rw [← star_sub, norm_star]
    exact h.le
  · have h1 : ε / (2 * (m + 1)) * m ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

/-- The functional field `x ↦ ⟨row x, ·⟩ = ∫ k(x, y) · dy` of a kernel. -/
def field (k : KernelAlg) (x : ℝ) : L2Real →L[ℂ] ℂ := innerSL ℂ (k.row x)

theorem field_apply (k : KernelAlg) (x : ℝ) (ξ : L2Real) :
    k.field x ξ = ∫ y, k.toFun (x, y) * ξ y := by
  rw [field, innerSL_apply_apply, row, inner_ccToL2]
  simp

theorem continuous_field (k : KernelAlg) : Continuous k.field :=
  (innerSL ℂ (E := L2Real)).continuous.comp k.continuous_row

theorem hasCompactSupport_field (k : KernelAlg) : HasCompactSupport k.field :=
  HasCompactSupport.intro (KernelCore.isCompact_fstSupp k.toCc) fun x hx => by
    rw [field, k.row_eq_zero hx, map_zero]

/-- The field as a square-integrable field of functionals. -/
def fieldL2 (k : KernelAlg) : Lp (L2Real →L[ℂ] ℂ) 2 (volume : Measure ℝ) :=
  (k.continuous_field.memLp_of_hasCompactSupport k.hasCompactSupport_field).toLp k.field

/-- **The integral operator** `(T_k ξ)(x) = ∫ k(x, y) ξ(y) dy` on `L²(ℝ)`. -/
def op (k : KernelAlg) : L2Real →L[ℂ] L2Real :=
  RHTower.connesKernelOperator volume k.fieldL2

theorem op_ae (k : KernelAlg) (ξ : L2Real) :
    (k.op ξ : ℝ → ℂ) =ᵐ[volume] fun x => ∫ y, k.toFun (x, y) * ξ y := by
  have h1 := RHTower.connesKernelApply_ae volume k.fieldL2 ξ
  have h2 : (k.fieldL2 : ℝ → L2Real →L[ℂ] ℂ) =ᵐ[volume] k.field := MemLp.coeFn_toLp _
  filter_upwards [h1, h2] with x hx1 hx2
  rw [op, RHTower.connesKernelOperator_apply, hx1, hx2, field_apply]

theorem isHilbertSchmidt_op (k : KernelAlg) : ContinuousLinearMap.IsHilbertSchmidt k.op :=
  RHTower.isHilbertSchmidt_connesKernelOperator volume k.fieldL2

end KernelAlg

/-! ## The dense core `C_c(ℝ) ⊆ L²(ℝ)` -/

/-- A compactly supported continuous function in `L²(ℝ)`. -/
def cc2 (g : C_c(ℝ, ℂ)) : L2Real := ccToL2 g.continuous g.hasCompactSupport

theorem cc2_ae (g : C_c(ℝ, ℂ)) : (cc2 g : ℝ → ℂ) =ᵐ[volume] g := ccToL2_ae _ _

theorem inner_cc2 (f : C_c(ℝ, ℂ)) (ξ : L2Real) : inner ℂ (cc2 f) ξ = ∫ y, star (f y) * ξ y :=
  inner_ccToL2 _ _ ξ

theorem inner_cc2_cc2 (f h : C_c(ℝ, ℂ)) : inner ℂ (cc2 f) (cc2 h) = ∫ y, star (f y) * h y := by
  rw [inner_cc2]
  refine integral_congr_ae ?_
  filter_upwards [cc2_ae h] with y hy
  rw [hy]

theorem denseRange_cc2 : DenseRange cc2 := by
  refine Metric.denseRange_iff.mpr fun ξ ε hε => ?_
  obtain ⟨g, hgs, hgξ, hgc, hgm⟩ := (Lp.memLp ξ).exists_hasCompactSupport_eLpNorm_sub_le
    (by norm_num) (ε := ENNReal.ofReal (ε / 2)) (by simpa using hε)
  refine ⟨⟨⟨g, hgc⟩, hgs⟩, ?_⟩
  rw [dist_eq_norm, Lp.norm_def]
  have hae : (fun x => ξ x - g x) =ᵐ[volume] ⇑(ξ - cc2 ⟨⟨g, hgc⟩, hgs⟩) := by
    filter_upwards [Lp.coeFn_sub ξ (cc2 ⟨⟨g, hgc⟩, hgs⟩), cc2_ae ⟨⟨g, hgc⟩, hgs⟩] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
    rfl
  rw [← eLpNorm_congr_ae hae]
  have hfin : eLpNorm (fun x => ξ x - g x) 2 volume ≠ ⊤ := (hgξ.trans_lt ENNReal.ofReal_lt_top).ne
  calc (eLpNorm (fun x => ξ x - g x) 2 volume).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hgξ
    _ = ε / 2 := ENNReal.toReal_ofReal (by positivity)
    _ < ε := by linarith

namespace KernelAlg

/-- The kernel applied to a compactly supported continuous function:
`(k g)(x) = ∫ k(x, y) g(y) dy`. -/
def applyCc (k : KernelAlg) (g : C_c(ℝ, ℂ)) : C_c(ℝ, ℂ) where
  toFun x := ∫ y, k.toFun (x, y) * g y
  continuous_toFun := by
    have h : (fun x : ℝ => ∫ y, k.toFun (x, y) * g y) =
        fun x => ∫ y in KernelCore.sndSupp k.toCc, k.toFun (x, y) * g y := by
      funext x
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        rw [k.toFun_eq_zero_of_snd hy, zero_mul]).symm
    rw [h]
    exact continuous_parametric_integral_of_continuous
      ((k.continuous_toFun.comp (continuous_fst.prodMk continuous_snd)).mul
        (g.continuous.comp continuous_snd)) (KernelCore.isCompact_sndSupp k.toCc)
  hasCompactSupport' := HasCompactSupport.intro (KernelCore.isCompact_fstSupp k.toCc) fun x hx => by
    simp [k.toFun_eq_zero_of_fst hx]

theorem applyCc_apply (k : KernelAlg) (g : C_c(ℝ, ℂ)) (x : ℝ) :
    k.applyCc g x = ∫ y, k.toFun (x, y) * g y := rfl

theorem integrable_kernel_mul (k : KernelAlg) (x : ℝ) {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable fun y => k.toFun (x, y) * g y := by
  refine Continuous.integrable_of_hasCompactSupport
    ((k.continuous_toFun.comp (continuous_const.prodMk continuous_id)).mul hg) ?_
  exact HasCompactSupport.intro (KernelCore.isCompact_sndSupp k.toCc) fun y hy => by
    simp [k.toFun_eq_zero_of_snd hy]

theorem op_cc2 (k : KernelAlg) (g : C_c(ℝ, ℂ)) : k.op (cc2 g) = cc2 (k.applyCc g) := by
  refine Lp.ext ?_
  filter_upwards [k.op_ae (cc2 g), cc2_ae (k.applyCc g)] with x h1 h2
  rw [h1, h2, applyCc_apply]
  refine integral_congr_ae ?_
  filter_upwards [cc2_ae g] with y hy
  rw [hy]

theorem applyCc_mul (k₁ k₂ : KernelAlg) (g : C_c(ℝ, ℂ)) :
    (k₁ * k₂).applyCc g = k₁.applyCc (k₂.applyCc g) := by
  ext x
  simp only [applyCc_apply, mul_apply]
  have hL : (fun y => (∫ w, k₁.toFun (x, w) * k₂.toFun (w, y)) * g y) =
      fun y => ∫ w, k₁.toFun (x, w) * k₂.toFun (w, y) * g y := by
    funext y
    exact (integral_mul_const _ _).symm
  have hR : (fun w => k₁.toFun (x, w) * ∫ y, k₂.toFun (w, y) * g y) =
      fun w => ∫ y, k₁.toFun (x, w) * k₂.toFun (w, y) * g y := by
    funext w
    rw [← integral_const_mul]
    simp only [mul_assoc]
  rw [hL, hR]
  refine integral_integral_swap ?_
  rw [← Measure.volume_eq_prod]
  refine Continuous.integrable_of_hasCompactSupport (by
    have h1 := k₁.continuous_toFun
    have h2 := k₂.continuous_toFun
    fun_prop) ?_
  refine HasCompactSupport.intro (g.hasCompactSupport.isCompact.prod
    (KernelCore.isCompact_sndSupp k₁.toCc)) ?_
  rintro ⟨y, w⟩ hyw
  simp only [mem_prod, not_and_or] at hyw
  rcases hyw with hy | hw
  · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  · simp [Function.uncurry, k₁.toFun_eq_zero_of_snd hw]

/-- **The integral operators are multiplicative**: `T_{k₁ k₂} = T_{k₁} T_{k₂}`. -/
theorem op_mul (k₁ k₂ : KernelAlg) : (k₁ * k₂).op = k₁.op * k₂.op := by
  refine DFunLike.coe_injective (denseRange_cc2.equalizer (k₁ * k₂).op.continuous
    (k₁.op * k₂.op).continuous (funext fun g => ?_))
  simp only [Function.comp_apply, mul_apply_eq_comp, op_cc2, applyCc_mul]

theorem cc2_add (f h : C_c(ℝ, ℂ)) : cc2 (f + h) = cc2 f + cc2 h :=
  MemLp.toLp_add (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)
    (h.continuous.memLp_of_hasCompactSupport h.hasCompactSupport)

theorem cc2_smul (c : ℂ) (f : C_c(ℝ, ℂ)) : cc2 (c • f) = c • cc2 f :=
  MemLp.toLp_const_smul c (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)

theorem applyCc_add (k₁ k₂ : KernelAlg) (g : C_c(ℝ, ℂ)) :
    (k₁ + k₂).applyCc g = k₁.applyCc g + k₂.applyCc g := by
  ext x
  simp only [applyCc_apply, add_apply, CompactlySupportedContinuousMap.coe_add, Pi.add_apply,
    add_mul]
  exact integral_add (k₁.integrable_kernel_mul x g.continuous)
    (k₂.integrable_kernel_mul x g.continuous)

theorem applyCc_smul (c : ℂ) (k : KernelAlg) (g : C_c(ℝ, ℂ)) :
    (c • k).applyCc g = c • k.applyCc g := by
  ext x
  simp only [applyCc_apply, smul_apply, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem op_add (k₁ k₂ : KernelAlg) : (k₁ + k₂).op = k₁.op + k₂.op := by
  refine DFunLike.coe_injective (denseRange_cc2.equalizer (k₁ + k₂).op.continuous
    (k₁.op + k₂.op).continuous (funext fun g => ?_))
  simp only [Function.comp_apply, _root_.add_apply, op_cc2, applyCc_add, cc2_add]

theorem op_smul (c : ℂ) (k : KernelAlg) : (c • k).op = c • k.op := by
  refine DFunLike.coe_injective (denseRange_cc2.equalizer (c • k).op.continuous
    (c • k.op).continuous (funext fun g => ?_))
  simp only [Function.comp_apply, _root_.smul_apply, op_cc2, applyCc_smul, cc2_smul]

theorem op_zero : (0 : KernelAlg).op = 0 := by
  simpa using op_smul 0 (0 : KernelAlg)

/-- The adjoint pairing on the dense core. -/
theorem inner_op_star_cc2 (k : KernelAlg) (g h : C_c(ℝ, ℂ)) :
    inner ℂ ((star k).op (cc2 g)) (cc2 h) = inner ℂ (cc2 g) (k.op (cc2 h)) := by
  rw [op_cc2, op_cc2, inner_cc2_cc2, inner_cc2_cc2]
  simp only [applyCc_apply, star_apply]
  have hL : (fun x => star (∫ y, star (k.toFun (y, x)) * g y) * h x) =
      fun x => ∫ y, k.toFun (y, x) * star (g y) * h x := by
    funext x
    rw [show star (∫ y, star (k.toFun (y, x)) * g y) =
        (starRingEnd ℂ) (∫ y, star (k.toFun (y, x)) * g y) from rfl, ← integral_conj,
      ← integral_mul_const]
    congr 1
    funext y
    simp [mul_comm]
  have hR : (fun y => star (g y) * ∫ x, k.toFun (y, x) * h x) =
      fun y => ∫ x, k.toFun (y, x) * star (g y) * h x := by
    funext y
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hL, hR]
  refine integral_integral_swap ?_
  rw [← Measure.volume_eq_prod]
  refine Continuous.integrable_of_hasCompactSupport (by
    have h1 := k.continuous_toFun
    fun_prop) ?_
  refine HasCompactSupport.intro (h.hasCompactSupport.isCompact.prod
    g.hasCompactSupport.isCompact) ?_
  rintro ⟨x, y⟩ hxy
  simp only [mem_prod, not_and_or] at hxy
  rcases hxy with hx | hy
  · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hx]
  · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]

/-- **The integral operators respect the involution**: `T_{k*} = T_k†`. -/
theorem op_star (k : KernelAlg) : (star k).op = ContinuousLinearMap.adjoint k.op := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro ξ η
  -- density in the second argument, then the first
  have hη : ∀ g : C_c(ℝ, ℂ), ∀ ζ : L2Real,
      inner ℂ ((star k).op ζ) (cc2 g) = inner ℂ ζ (k.op (cc2 g)) := by
    intro g ζ
    have := denseRange_cc2.equalizer (f := cc2)
      (g := fun ζ => inner ℂ ((star k).op ζ) (cc2 g))
      (h := fun ζ => inner ℂ ζ (k.op (cc2 g)))
      (by fun_prop) (by fun_prop) (funext fun h => inner_op_star_cc2 k h g)
    exact congrFun this ζ
  have := denseRange_cc2.equalizer (f := cc2)
    (g := fun ζ => inner ℂ ((star k).op ξ) ζ) (h := fun ζ => inner ℂ ξ (k.op ζ))
    (by fun_prop) (by fun_prop) (funext fun g => hη g ξ)
  exact congrFun this η

/-! ### The `L¹(ℝ, C₀(ℝ))` norm -/

/-- The fibre `x ↦ k(x, x - s)`: the value at `s` of the function `F(s, ·) ∈ C₀(ℝ)` corresponding
to `k` in the twisted convolution picture `F(s, x) = k(x, x - s)`. -/
def fibre (k : KernelAlg) (s : ℝ) : C_c(ℝ, ℂ) where
  toFun x := k.toFun (x, x - s)
  continuous_toFun := k.continuous_toFun.comp (continuous_id.prodMk (continuous_id.sub continuous_const))
  hasCompactSupport' := HasCompactSupport.intro (KernelCore.isCompact_fstSupp k.toCc) fun x hx => by
    simp [k.toFun_eq_zero_of_fst hx]

theorem fibre_apply (k : KernelAlg) (s x : ℝ) : k.fibre s x = k.toFun (x, x - s) := rfl

/-- The sup norm `‖F(s, ·)‖_∞` of a fibre. -/
def fibreNorm (k : KernelAlg) (s : ℝ) : ℝ := ‖(k.fibre s).toBoundedContinuousFunction‖

theorem norm_toFun_le_fibreNorm (k : KernelAlg) (s x : ℝ) : ‖k.toFun (x, x - s)‖ ≤ k.fibreNorm s :=
  (k.fibre s).toBoundedContinuousFunction.norm_coe_le_norm x

theorem fibreNorm_nonneg (k : KernelAlg) (s : ℝ) : 0 ≤ k.fibreNorm s := norm_nonneg _

theorem continuous_fibreNorm (k : KernelAlg) : Continuous k.fibreNorm := by
  have huc := (k.hasCompactSupport_toFun).uniformContinuous_of_continuous k.continuous_toFun
  refine Metric.continuous_iff.mpr fun s ε hε => ?_
  obtain ⟨δ, hδ, hδk⟩ := Metric.uniformContinuous_iff.mp huc (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun s' hs' => ?_⟩
  rw [Real.dist_eq]
  refine (abs_norm_sub_norm_le _ _).trans_lt ?_
  refine lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_)
    (half_lt_self hε)
  have h := hδk (a := (x, x - s')) (b := (x, x - s)) (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    simp only [sub_sub_sub_cancel_left]
    rw [max_eq_right (abs_nonneg _), abs_sub_comm, ← Real.dist_eq]
    exact hs')
  rw [dist_eq_norm] at h
  exact h.le

/-- The shadow `π₁(supp k) - π₂(supp k)` containing every nonzero fibre. -/
def fibreSupp (k : KernelAlg) : Set ℝ :=
  (fun p : ℝ × ℝ => p.1 - p.2) '' (KernelCore.fstSupp k.toCc ×ˢ KernelCore.sndSupp k.toCc)

theorem isCompact_fibreSupp (k : KernelAlg) : IsCompact k.fibreSupp :=
  ((KernelCore.isCompact_fstSupp k.toCc).prod (KernelCore.isCompact_sndSupp k.toCc)).image
    (continuous_fst.sub continuous_snd)

theorem fibre_eq_zero (k : KernelAlg) {s : ℝ} (hs : s ∉ k.fibreSupp) : k.fibre s = 0 := by
  ext x
  rw [fibre_apply]
  by_contra h
  apply hs
  refine ⟨(x, x - s), ⟨?_, ?_⟩, by simp⟩
  · by_contra hx
    exact h (k.toFun_eq_zero_of_fst hx)
  · by_contra hy
    exact h (k.toFun_eq_zero_of_snd hy)

theorem hasCompactSupport_fibreNorm (k : KernelAlg) : HasCompactSupport k.fibreNorm :=
  HasCompactSupport.intro k.isCompact_fibreSupp fun s hs => by
    rw [fibreNorm, k.fibre_eq_zero hs]
    have h0 : (0 : C_c(ℝ, ℂ)).toBoundedContinuousFunction = 0 :=
      BoundedContinuousFunction.ext fun _ => rfl
    rw [h0, norm_zero]

theorem integrable_fibreNorm (k : KernelAlg) : Integrable k.fibreNorm :=
  k.continuous_fibreNorm.integrable_of_hasCompactSupport k.hasCompactSupport_fibreNorm

/-- **The `L¹(ℝ, C₀(ℝ))` norm** `‖F‖₁ = ∫ ‖F(s, ·)‖_∞ ds` of the twisted convolution picture. -/
def l1Norm (k : KernelAlg) : ℝ := ∫ s, k.fibreNorm s

theorem l1Norm_nonneg (k : KernelAlg) : 0 ≤ k.l1Norm :=
  integral_nonneg k.fibreNorm_nonneg

theorem integrable_norm_row (k : KernelAlg) (x : ℝ) : Integrable fun y => ‖k.toFun (x, y)‖ :=
  (k.continuous_toFun.comp (continuous_const.prodMk continuous_id)).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (KernelCore.isCompact_sndSupp k.toCc) fun y hy => by
      simp [k.toFun_eq_zero_of_snd hy])

theorem integrable_norm_col (k : KernelAlg) (y : ℝ) : Integrable fun x => ‖k.toFun (x, y)‖ :=
  (k.continuous_toFun.comp (continuous_id.prodMk continuous_const)).norm.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (KernelCore.isCompact_fstSupp k.toCc) fun x hx => by
      simp [k.toFun_eq_zero_of_fst hx])

/-- Row bound: `∫ |k(x, y)| dy ≤ ‖k‖₁`. -/
theorem integral_norm_row_le (k : KernelAlg) (x : ℝ) :
    ∫ y, ‖k.toFun (x, y)‖ ≤ k.l1Norm := by
  rw [← integral_sub_left_eq_self (fun y => ‖k.toFun (x, y)‖) volume x]
  refine integral_mono ?_ k.integrable_fibreNorm fun s => k.norm_toFun_le_fibreNorm s x
  exact (k.integrable_norm_row x).comp_sub_left x

/-- Column bound: `∫ |k(x, y)| dx ≤ ‖k‖₁`. -/
theorem integral_norm_col_le (k : KernelAlg) (y : ℝ) :
    ∫ x, ‖k.toFun (x, y)‖ ≤ k.l1Norm := by
  rw [← integral_add_right_eq_self (fun x => ‖k.toFun (x, y)‖) y]
  refine integral_mono ?_ k.integrable_fibreNorm fun s => ?_
  · exact (k.integrable_norm_col y).comp_add_right y
  · have := k.norm_toFun_le_fibreNorm s (s + y)
    simpa using this

theorem norm_cc2_sq (f : C_c(ℝ, ℂ)) : ‖cc2 f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_cc2_cc2, ← integral_re]
  · congr 1
    funext x
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
  · exact (f.continuous.star.mul f.continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_left

/-- **Schur's test**: `‖T_k g‖ ≤ ‖k‖₁ ‖g‖` on the dense core. -/
theorem norm_cc2_applyCc_le (k : KernelAlg) (g : C_c(ℝ, ℂ)) :
    ‖cc2 (k.applyCc g)‖ ≤ k.l1Norm * ‖cc2 g‖ := by
  have hN := k.l1Norm_nonneg
  have hint2 : ∀ x, Integrable fun y => ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 := fun x =>
    (((k.continuous_toFun.comp (continuous_const.prodMk continuous_id)).norm).mul
      (g.continuous.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (KernelCore.isCompact_sndSupp k.toCc) fun y hy => by
        simp [k.toFun_eq_zero_of_snd hy])
  have hpt : ∀ x, ‖k.applyCc g x‖ ^ 2 ≤ k.l1Norm * ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 := by
    intro x
    have h1 : ‖k.applyCc g x‖ ≤ ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ := by
      rw [applyCc_apply]
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_mul]
    have hcs := sq_integral_weighted_le (μ := volume) (w := fun y => ‖k.toFun (x, y)‖)
      (g := fun y => ‖g y‖) (fun y => norm_nonneg _)
      (k.integrable_norm_row x).aestronglyMeasurable g.continuous.norm.aestronglyMeasurable
      (k.integrable_norm_row x) (hint2 x)
    calc ‖k.applyCc g x‖ ^ 2 ≤ (∫ y, ‖k.toFun (x, y)‖ * ‖g y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∫ y, ‖k.toFun (x, y)‖) * ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 := hcs
      _ ≤ k.l1Norm * ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (k.integral_norm_row_le x)
            (integral_nonneg fun y => by positivity)
  have hF : Integrable (Function.uncurry fun x y => ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2)
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    refine Continuous.integrable_of_hasCompactSupport (by
      have := k.continuous_toFun
      have := g.continuous
      fun_prop) ?_
    exact (k.hasCompactSupport_toFun.norm.mul_right (f' := fun p : ℝ × ℝ => ‖g p.2‖ ^ 2))
  have hswap : ∫ x, ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 =
      ∫ y, ‖g y‖ ^ 2 * ∫ x, ‖k.toFun (x, y)‖ := by
    rw [integral_integral_swap hF]
    congr 1
    funext y
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  have hsq : ‖cc2 (k.applyCc g)‖ ^ 2 ≤ (k.l1Norm * ‖cc2 g‖) ^ 2 := by
    rw [norm_cc2_sq, mul_pow, norm_cc2_sq]
    calc ∫ x, ‖k.applyCc g x‖ ^ 2 ≤ ∫ x, k.l1Norm * ∫ y, ‖k.toFun (x, y)‖ * ‖g y‖ ^ 2 := by
          refine integral_mono ?_ ?_ hpt
          · exact ((k.applyCc g).continuous.norm.pow 2).integrable_of_hasCompactSupport
              (HasCompactSupport.intro (k.applyCc g).hasCompactSupport.isCompact fun x hx => by
                simp [image_eq_zero_of_notMem_tsupport hx])
          · exact (hF.integral_prod_left).const_mul _
      _ = k.l1Norm * ∫ y, ‖g y‖ ^ 2 * ∫ x, ‖k.toFun (x, y)‖ := by
          rw [integral_const_mul, hswap]
      _ ≤ k.l1Norm * ∫ y, ‖g y‖ ^ 2 * k.l1Norm := by
          refine mul_le_mul_of_nonneg_left (integral_mono ?_ ?_ fun y => ?_) hN
          · exact hF.integral_prod_right.congr (Filter.Eventually.of_forall fun y => by
              simp only [Function.uncurry]
              rw [integral_mul_const, mul_comm])
          · exact ((g.continuous.norm.pow 2).integrable_of_hasCompactSupport
              (HasCompactSupport.intro g.hasCompactSupport.isCompact fun x hx => by
                simp [image_eq_zero_of_notMem_tsupport hx])).mul_const _
          · exact mul_le_mul_of_nonneg_left (k.integral_norm_col_le y) (by positivity)
      _ = k.l1Norm ^ 2 * ∫ y, ‖g y‖ ^ 2 := by
          rw [integral_mul_const]
          ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **`‖T_k‖ ≤ ‖k‖₁`**: the integral representation is bounded by the `L¹(ℝ, C₀(ℝ))` norm. -/
theorem norm_op_le_l1Norm (k : KernelAlg) : ‖k.op‖ ≤ k.l1Norm := by
  refine ContinuousLinearMap.opNorm_le_bound _ k.l1Norm_nonneg fun ξ => ?_
  have hclosed : IsClosed {ζ : L2Real | ‖k.op ζ‖ ≤ k.l1Norm * ‖ζ‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hdense : Dense (Set.range cc2) := denseRange_cc2
  have hsub : Set.range cc2 ⊆ {ζ : L2Real | ‖k.op ζ‖ ≤ k.l1Norm * ‖ζ‖} := by
    rintro _ ⟨g, rfl⟩
    rw [Set.mem_setOf_eq, op_cc2]
    exact k.norm_cc2_applyCc_le g
  exact (hclosed.closure_subset_iff.mpr hsub) (hdense ξ)

/-! ### Rank-one kernels: matrix units -/

/-- The rank-one kernel `(x, y) ↦ φ(x) conj ψ(y)`. -/
def rankOneKernel (φ ψ : C_c(ℝ, ℂ)) : KernelAlg :=
  (show C_c(ℝ × ℝ, ℂ) from
  { toFun := fun p => φ p.1 * star (ψ p.2)
    continuous_toFun := by
      have := φ.continuous
      have := ψ.continuous
      fun_prop
    hasCompactSupport' := HasCompactSupport.intro
      (φ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact) fun p hp => by
        simp only [mem_prod, not_and_or] at hp
        rcases hp with h | h
        · simp [image_eq_zero_of_notMem_tsupport h]
        · simp [image_eq_zero_of_notMem_tsupport h] })

theorem rankOneKernel_apply (φ ψ : C_c(ℝ, ℂ)) (x y : ℝ) :
    (rankOneKernel φ ψ).toFun (x, y) = φ x * star (ψ y) := rfl

theorem applyCc_rankOneKernel (φ ψ g : C_c(ℝ, ℂ)) :
    (rankOneKernel φ ψ).applyCc g = inner ℂ (cc2 ψ) (cc2 g) • φ := by
  ext x
  rw [applyCc_apply, inner_cc2_cc2, CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, mul_comm, ← integral_const_mul]
  congr 1
  funext y
  rw [rankOneKernel_apply]
  ring

/-- **The integral operator of a rank-one kernel is the rank-one operator** `|φ⟩⟨ψ|`. -/
theorem op_rankOneKernel (φ ψ : C_c(ℝ, ℂ)) :
    (rankOneKernel φ ψ).op = InnerProductSpace.rankOne ℂ (cc2 φ) (cc2 ψ) := by
  refine DFunLike.coe_injective (denseRange_cc2.equalizer (rankOneKernel φ ψ).op.continuous
    (InnerProductSpace.rankOne ℂ (cc2 φ) (cc2 ψ)).continuous (funext fun g => ?_))
  simp only [Function.comp_apply, op_cc2, applyCc_rankOneKernel, cc2_smul,
    InnerProductSpace.rankOne_def, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- Matrix-unit relations: `e_{φψ} e_{φ'ψ'} = ⟨ψ, φ'⟩ e_{φψ'}`. -/
theorem rankOneKernel_mul (φ ψ φ' ψ' : C_c(ℝ, ℂ)) :
    rankOneKernel φ ψ * rankOneKernel φ' ψ' = inner ℂ (cc2 ψ) (cc2 φ') • rankOneKernel φ ψ' := by
  refine ext fun ⟨x, z⟩ => ?_
  rw [mul_apply, smul_apply, rankOneKernel_apply, inner_cc2_cc2, ← integral_mul_const]
  congr 1
  funext y
  simp only [rankOneKernel_apply]
  ring

theorem star_rankOneKernel (φ ψ : C_c(ℝ, ℂ)) : star (rankOneKernel φ ψ) = rankOneKernel ψ φ := by
  refine ext fun ⟨x, y⟩ => ?_
  rw [star_apply, rankOneKernel_apply, rankOneKernel_apply, StarMul.star_mul, star_star,
    mul_comm]

/-- **The integral (Schrödinger) representation** of the kernel algebra on `L²(ℝ)`. -/
def opHom : KernelAlg →⋆ₙₐ[ℂ] (L2Real →L[ℂ] L2Real) where
  toFun := op
  map_smul' := op_smul
  map_zero' := op_zero
  map_add' := op_add
  map_mul' := op_mul
  map_star' := op_star

theorem opHom_apply (k : KernelAlg) : opHom k = k.op := rfl

end KernelAlg

end GaloisForLFunctions.HTGeometry
