import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The flat primitive and its Fourier functional calculus

On mean-zero compact tests `f` (continuous, compactly supported, `∫ f = 0`) the flat primitive is
`(Hf)(x) = ∫_{-∞}^x f`.  It is again a compactly supported `C¹` function, and in mathlib's
Fourier convention `𝓕 f (w) = ∫ e^{-2πixw} f(x) dx`

`𝓕 (i Hf) (w) = σ(w) 𝓕 f (w)`,  `σ(w) = (2πw)⁻¹`,  `w ≠ 0`.

(With `ξ = -2πw`, the frequency of the convention `f̂(ξ) = ∫ f e^{iξx}`, this is `σ = -1/ξ`.)

`S = iH` is realized as the maximal Fourier multiplier by `σ`: its domain is the set of
`u ∈ L²(ℝ)` with `σ · 𝓕u ∈ L²`, and it contains every test, on which it acts as `iH`.  `S` is
symmetric.  Its bounded Borel functional calculus is `Φ(S) = 𝓕⁻¹ M_{Φ∘σ} 𝓕`: it is multiplicative,
unital, `*`-preserving, bounded by `sup |Φ|`, and for non-real `λ` the function `(t - λ)⁻¹` is sent
to the two-sided inverse of `S - λ`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory FourierTransform Filter Set Topology Real
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

/-! ### Mean-zero compact tests and their primitives -/

/-- A mean-zero compact test: continuous, compactly supported, with integral zero. -/
structure FlatTest (f : ℝ → ℂ) : Prop where
  continuous : Continuous f
  hasCompactSupport : HasCompactSupport f
  integral_eq_zero : ∫ x, f x = 0

/-- The flat primitive `(Hf)(x) = ∫_{-∞}^x f`. -/
def flatPrimitive (f : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y in Iic x, f y

namespace FlatTest

variable {f : ℝ → ℂ}

theorem integrable (hf : FlatTest f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport

theorem memLp (hf : FlatTest f) : MemLp f 2 volume :=
  hf.continuous.memLp_of_hasCompactSupport hf.hasCompactSupport

theorem exists_bound (hf : FlatTest f) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x, R < |x| → f x = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hf.hasCompactSupport.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun x hx => image_eq_zero_of_notMem_tsupport fun hmem => ?_⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact absurd (lt_of_le_of_lt (this.trans (le_max_left R 0)) hx) (lt_irrefl _)

theorem flatPrimitive_eq_intervalIntegral (hf : FlatTest f) {a : ℝ} (ha : ∀ y ≤ a, f y = 0)
    (x : ℝ) : flatPrimitive f x = ∫ y in a..x, f y := by
  have h0 : ∫ y in Iic a, f y = 0 := setIntegral_eq_zero_of_forall_eq_zero fun y hy => ha y hy
  rw [← intervalIntegral.integral_Iic_sub_Iic hf.integrable.integrableOn hf.integrable.integrableOn,
    h0, sub_zero, flatPrimitive]

theorem hasDerivAt_flatPrimitive (hf : FlatTest f) (x : ℝ) :
    HasDerivAt (flatPrimitive f) (f x) x := by
  obtain ⟨R, hR0, hR⟩ := hf.exists_bound
  have ha : ∀ y ≤ -(R + 1), f y = 0 := fun y hy => hR y (by
    rw [abs_of_neg (by linarith)]; linarith)
  have e : flatPrimitive f = fun x => ∫ y in -(R + 1)..x, f y :=
    funext (hf.flatPrimitive_eq_intervalIntegral ha)
  rw [e]
  exact (hf.continuous.integral_hasStrictDerivAt _ x).hasDerivAt

theorem differentiable_flatPrimitive (hf : FlatTest f) : Differentiable ℝ (flatPrimitive f) :=
  fun x => (hf.hasDerivAt_flatPrimitive x).differentiableAt

theorem continuous_flatPrimitive (hf : FlatTest f) : Continuous (flatPrimitive f) :=
  hf.differentiable_flatPrimitive.continuous

theorem deriv_flatPrimitive (hf : FlatTest f) : deriv (flatPrimitive f) = f :=
  funext fun x => (hf.hasDerivAt_flatPrimitive x).deriv

/-- The primitive of a mean-zero compact test vanishes outside the support interval. -/
theorem flatPrimitive_eq_zero (hf : FlatTest f) {R : ℝ} (hR : ∀ x, R < |x| → f x = 0) {x : ℝ}
    (hx : R < |x|) : flatPrimitive f x = 0 := by
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    have ha : ∀ y ≤ -(|R| + 1), f y = 0 := fun y hy => hR y (by
      linarith [neg_le_abs y, le_abs_self R])
    rw [hf.flatPrimitive_eq_intervalIntegral ha x, intervalIntegral.integral_of_le (by
      linarith [abs_nonneg R]),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_, hf.integral_eq_zero]
    rcases le_or_gt y (-(|R| + 1)) with h1 | h1
    · exact ha y h1
    · have h2 : x < y := by
        by_contra h2
        exact hy ⟨h1, le_of_not_gt h2⟩
      exact hR y (by linarith [le_abs_self y])
  · rw [abs_of_neg h0] at hx
    exact setIntegral_eq_zero_of_forall_eq_zero fun y (hy : y ≤ x) => hR y (by
      rw [abs_of_neg (by linarith)]; linarith)

theorem hasCompactSupport_flatPrimitive (hf : FlatTest f) : HasCompactSupport (flatPrimitive f) := by
  obtain ⟨R, _, hR⟩ := hf.exists_bound
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact hf.flatPrimitive_eq_zero hR hx

theorem integrable_flatPrimitive (hf : FlatTest f) : Integrable (flatPrimitive f) :=
  hf.continuous_flatPrimitive.integrable_of_hasCompactSupport hf.hasCompactSupport_flatPrimitive

theorem memLp_flatPrimitive (hf : FlatTest f) : MemLp (fun x => Complex.I * flatPrimitive f x) 2 volume :=
  (hf.continuous_flatPrimitive.memLp_of_hasCompactSupport hf.hasCompactSupport_flatPrimitive).const_mul
    Complex.I

/-- `(2πiw) 𝓕(Hf)(w) = 𝓕 f(w)`. -/
theorem fourier_flatPrimitive (hf : FlatTest f) (w : ℝ) :
    (2 * π * Complex.I * w) * 𝓕 (flatPrimitive f) w = 𝓕 f w := by
  have h := Real.fourier_deriv hf.integrable_flatPrimitive hf.differentiable_flatPrimitive
    (by rw [hf.deriv_flatPrimitive]; exact hf.integrable)
  rw [hf.deriv_flatPrimitive] at h
  rw [h]
  rfl

end FlatTest

/-! ### The symbol of `S = iH` -/

/-- The Fourier symbol of the flat primitive `S = iH`: `σ(w) = (2πw)⁻¹` (`= -1/ξ`, `ξ = -2πw`). -/
def flatSymbol (w : ℝ) : ℝ := (2 * π * w)⁻¹

theorem measurable_flatSymbol : Measurable flatSymbol := by
  unfold flatSymbol; fun_prop

/-- **`S ↔ σ` on tests:** `𝓕 (i Hf) (w) = σ(w) 𝓕 f (w)` for `w ≠ 0`. -/
theorem FlatTest.fourier_I_flatPrimitive {f : ℝ → ℂ} (hf : FlatTest f) {w : ℝ} (hw : w ≠ 0) :
    𝓕 (fun x => Complex.I * flatPrimitive f x) w = (flatSymbol w : ℂ) * 𝓕 f w := by
  rw [fourier_const_mul_apply, ← hf.fourier_flatPrimitive w, flatSymbol]
  have hw' : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ### The maximal realization -/

/-- `σ · 𝓕u`. -/
def flatSymbolMul (u : Lp ℂ 2 (volume : Measure ℝ)) (w : ℝ) : ℂ :=
  (flatSymbol w : ℂ) * (fourierL2 ℝ u : ℝ → ℂ) w

/-- The maximal domain `{u ∈ L² : σ · 𝓕u ∈ L²}`. -/
def flatDomain : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := {u | MemLp (flatSymbolMul u) 2 volume}
  add_mem' := by
    intro u v hu hv
    refine (hu.add hv).ae_eq ?_
    filter_upwards [Lp.coeFn_add (fourierL2 ℝ u) (fourierL2 ℝ v)] with w hw
    simp only [flatSymbolMul, Pi.add_apply, map_add, hw, mul_add]
  zero_mem' := by
    refine (Lp.memLp (0 : Lp ℂ 2 (volume : Measure ℝ))).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with w hw
    simp only [flatSymbolMul, map_zero, hw, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c u hu
    refine (hu.const_mul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c (fourierL2 ℝ u)] with w hw
    simp only [flatSymbolMul, map_smul, hw, Pi.smul_apply, smul_eq_mul]
    ring

theorem mem_flatDomain {u : Lp ℂ 2 (volume : Measure ℝ)} :
    u ∈ flatDomain ↔ MemLp (flatSymbolMul u) 2 volume := Iff.rfl

/-- The action of `S` on its domain. -/
def flatPrimitiveLin : flatDomain →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun u := fourierL2inv ℝ ((mem_flatDomain.mp u.2).toLp _)
  map_add' u v := by
    rw [← map_add, ← MemLp.toLp_add]
    congr 1
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add (fourierL2 ℝ u) (fourierL2 ℝ v)] with w hw
    simp only [flatSymbolMul, Submodule.coe_add, map_add, hw, Pi.add_apply, mul_add]
  map_smul' c u := by
    rw [RingHom.id_apply, ← map_smul, ← MemLp.toLp_const_smul]
    congr 1
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul c (fourierL2 ℝ u)] with w hw
    simp only [flatSymbolMul, Submodule.coe_smul, map_smul, hw, Pi.smul_apply, smul_eq_mul]
    ring

/-- **The self-adjoint realization of `S = iH`:** the maximal Fourier multiplier by `σ`. -/
def flatPrimitiveOp : Lp ℂ 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ⟨flatDomain, flatPrimitiveLin⟩

theorem flatPrimitiveOp_domain : flatPrimitiveOp.domain = flatDomain := rfl

/-- `𝓕 (S u) = σ · 𝓕 u`. -/
theorem fourierL2_flatPrimitiveOp (u : flatPrimitiveOp.domain) :
    (fourierL2 ℝ (flatPrimitiveOp u) : ℝ → ℂ) =ᵐ[volume] flatSymbolMul u := by
  change (fourierL2 ℝ (fourierL2inv ℝ ((mem_flatDomain.mp u.2).toLp _)) : ℝ → ℂ) =ᵐ[volume] _
  rw [fourierL2_fourierL2inv]
  exact MemLp.coeFn_toLp _

/-- **Every mean-zero compact test lies in the domain of `S`, and `S f = i Hf`.** -/
theorem FlatTest.mem_flatDomain {f : ℝ → ℂ} (hf : FlatTest f) :
    hf.memLp.toLp f ∈ flatDomain := by
  have hP := hf.memLp_flatPrimitive
  have hPint : Integrable (hP.toLp _ : ℝ → ℂ) :=
    (hf.integrable_flatPrimitive.const_mul Complex.I).congr (MemLp.coeFn_toLp hP).symm
  have hfint : Integrable (hf.memLp.toLp f : ℝ → ℂ) := hf.integrable.congr (MemLp.coeFn_toLp _).symm
  refine (Lp.memLp (fourierL2 ℝ (hP.toLp _))).ae_eq ?_
  have hne : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))]
      with w hw using hw
  filter_upwards [fourierL2_coeFn_ae_eq_fourier _ hPint, fourierL2_coeFn_ae_eq_fourier _ hfint,
    hne] with w h1 h2 hw
  rw [h1, flatSymbolMul, h2]
  have e1 : 𝓕 (hP.toLp _ : ℝ → ℂ) w = 𝓕 (fun x => Complex.I * flatPrimitive f x) w := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hP] with x hx
    rw [hx]
  have e2 : 𝓕 (hf.memLp.toLp f : ℝ → ℂ) w = 𝓕 f w := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf.memLp] with x hx
    rw [hx]
  rw [e1, e2, hf.fourier_I_flatPrimitive hw]

theorem FlatTest.flatPrimitiveOp_apply {f : ℝ → ℂ} (hf : FlatTest f) :
    flatPrimitiveOp ⟨hf.memLp.toLp f, hf.mem_flatDomain⟩ = hf.memLp_flatPrimitive.toLp _ := by
  have hP := hf.memLp_flatPrimitive
  have hPint : Integrable (hP.toLp _ : ℝ → ℂ) :=
    (hf.integrable_flatPrimitive.const_mul Complex.I).congr (MemLp.coeFn_toLp hP).symm
  have hfint : Integrable (hf.memLp.toLp f : ℝ → ℂ) := hf.integrable.congr (MemLp.coeFn_toLp _).symm
  have hne : ∀ᵐ w ∂(volume : Measure ℝ), w ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))]
      with w hw using hw
  have key : fourierL2 ℝ (flatPrimitiveOp ⟨hf.memLp.toLp f, hf.mem_flatDomain⟩) =
      fourierL2 ℝ (hP.toLp _) := by
    refine Lp.ext ?_
    filter_upwards [fourierL2_flatPrimitiveOp ⟨hf.memLp.toLp f, hf.mem_flatDomain⟩,
      fourierL2_coeFn_ae_eq_fourier _ hPint, fourierL2_coeFn_ae_eq_fourier _ hfint, hne]
      with w h0 h1 h2 hw
    rw [h0, h1, flatSymbolMul, h2]
    have e1 : 𝓕 (hP.toLp _ : ℝ → ℂ) w = 𝓕 (fun x => Complex.I * flatPrimitive f x) w := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hP] with x hx
      rw [hx]
    have e2 : 𝓕 (hf.memLp.toLp f : ℝ → ℂ) w = 𝓕 f w := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hf.memLp] with x hx
      rw [hx]
    rw [e1, e2, hf.fourier_I_flatPrimitive hw]
  have := congrArg (fourierL2inv ℝ) key
  simpa only [fourierL2inv_fourierL2] using this

theorem inner_fourierL2inv_left (a v : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (fourierL2inv ℝ a) v = inner ℂ a (fourierL2 ℝ v) := by
  rw [← adjoint_fourierL2, ContinuousLinearMap.adjoint_inner_left]

/-- **`S` is symmetric.** -/
theorem inner_flatPrimitiveOp (u v : flatPrimitiveOp.domain) :
    inner ℂ (flatPrimitiveOp u) (v : Lp ℂ 2 (volume : Measure ℝ)) =
      inner ℂ (u : Lp ℂ 2 (volume : Measure ℝ)) (flatPrimitiveOp v) := by
  have hu := fourierL2_flatPrimitiveOp u
  have hv := fourierL2_flatPrimitiveOp v
  rw [← (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map (flatPrimitiveOp u),
    ← (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map (u : Lp ℂ 2 (volume : Measure ℝ)),
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with w h1 h2
  change inner ℂ ((fourierL2 ℝ (flatPrimitiveOp u) : ℝ → ℂ) w) ((fourierL2 ℝ v : ℝ → ℂ) w) =
    inner ℂ ((fourierL2 ℝ u : ℝ → ℂ) w) ((fourierL2 ℝ (flatPrimitiveOp v) : ℝ → ℂ) w)
  rw [h1, h2, flatSymbolMul, flatSymbolMul, RCLike.inner_apply', RCLike.inner_apply', map_mul,
    Complex.conj_ofReal]
  ring

/-! ### The bounded Borel functional calculus of `S` -/

/-- `Φ(S) = 𝓕⁻¹ M_{Φ∘σ} 𝓕` for a bounded Borel function `Φ`. -/
def flatCalculus {Φ : ℝ → ℂ} (hΦ : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖Φ t‖ ≤ C) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  fourierMulCLM (φ := fun w => Φ (flatSymbol w)) (hΦ.comp measurable_flatSymbol) hC0 fun _ => hC _

theorem norm_flatCalculus_le {Φ : ℝ → ℂ} (hΦ : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖Φ t‖ ≤ C) : ‖flatCalculus hΦ hC0 hC‖ ≤ C :=
  norm_fourierMulCLM_le _ _ _

/-- The calculus is multiplicative. -/
theorem flatCalculus_comp {Φ Ψ : ℝ → ℂ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ) {C D : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖Φ t‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ t, ‖Ψ t‖ ≤ D) :
    (flatCalculus hΦ hC0 hC).comp (flatCalculus hΨ hD0 hD) =
      flatCalculus (hΦ.mul hΨ) (mul_nonneg hC0 hD0) fun t => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_mul (hC t) (hD t) (norm_nonneg _) hC0 :=
  fourierMulCLM_comp _ _ _ _ _ _ _ _ _ (Eventually.of_forall fun _ => rfl)

/-- The calculus is additive. -/
theorem flatCalculus_add {Φ Ψ : ℝ → ℂ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ) {C D : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ t, ‖Φ t‖ ≤ C) (hD0 : 0 ≤ D) (hD : ∀ t, ‖Ψ t‖ ≤ D) :
    flatCalculus (hΦ.add hΨ) (add_nonneg hC0 hD0) (fun t => (norm_add_le _ _).trans
      (add_le_add (hC t) (hD t))) = flatCalculus hΦ hC0 hC + flatCalculus hΨ hD0 hD :=
  fourierMulCLM_add _ _ _ _ _ _ _ _ _ (Eventually.of_forall fun _ => rfl)

/-- The calculus is unital. -/
theorem flatCalculus_one :
    flatCalculus (Φ := fun _ => (1 : ℂ)) measurable_const zero_le_one (fun _ => by simp) =
      ContinuousLinearMap.id ℂ _ :=
  fourierMulCLM_eq_id _ _ _ (Eventually.of_forall fun _ => rfl)

/-- The calculus preserves adjoints. -/
theorem adjoint_flatCalculus {Φ : ℝ → ℂ} (hΦ : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖Φ t‖ ≤ C) :
    ContinuousLinearMap.adjoint (flatCalculus hΦ hC0 hC) =
      flatCalculus (Complex.continuous_conj.measurable.comp hΦ) hC0
        (fun t => by simpa using hC t) :=
  adjoint_fourierMulCLM _ _ _ _ _ _ fun _ => rfl

/-- A real bounded Borel function of `S` is self-adjoint. -/
theorem isSelfAdjoint_flatCalculus {Φ : ℝ → ℂ} (hΦ : Measurable Φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ t, ‖Φ t‖ ≤ C) (hreal : ∀ t, (starRingEnd ℂ) (Φ t) = Φ t) :
    IsSelfAdjoint (flatCalculus hΦ hC0 hC) :=
  isSelfAdjoint_fourierMulCLM _ _ _ fun _ => hreal _

/-! ### Resolvents: the calculus is the functional calculus of `S` -/

section Resolvent

variable {lam : ℂ} (hlam : lam.im ≠ 0)
include hlam

theorem resolvent_denom_ne_zero (t : ℝ) : (t : ℂ) - lam ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hlam (by linarith)

theorem norm_resolvent_le (t : ℝ) : ‖((t : ℂ) - lam)⁻¹‖ ≤ |lam.im|⁻¹ := by
  rw [norm_inv]
  refine inv_anti₀ (abs_pos.mpr hlam) ?_
  calc |lam.im| = |((t : ℂ) - lam).im| := by simp
    _ ≤ ‖(t : ℂ) - lam‖ := Complex.abs_im_le_norm _

omit hlam in
theorem measurable_resolvent : Measurable fun t : ℝ => ((t : ℂ) - lam)⁻¹ := by fun_prop

/-- The resolvent `(S - λ)⁻¹` in the calculus. -/
def flatResolvent : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  flatCalculus (measurable_resolvent (lam := lam)) (inv_nonneg.mpr (abs_nonneg _)) (norm_resolvent_le hlam)

theorem fourierL2_flatResolvent (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (fourierL2 ℝ (flatResolvent hlam u) : ℝ → ℂ) =ᵐ[volume]
      fun w => ((flatSymbol w : ℂ) - lam)⁻¹ * (fourierL2 ℝ u : ℝ → ℂ) w := by
  change (fourierL2 ℝ (fourierL2inv ℝ _) : ℝ → ℂ) =ᵐ[volume] _
  rw [fourierL2_fourierL2inv]
  exact lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    ((measurable_resolvent (lam := lam)).comp measurable_flatSymbol) (inv_nonneg.mpr (abs_nonneg _))
    (fun w => norm_resolvent_le hlam _) _

/-- `(S - λ)⁻¹` maps `L²` into the domain of `S`. -/
theorem flatResolvent_mem_flatDomain (u : Lp ℂ 2 (volume : Measure ℝ)) :
    flatResolvent hlam u ∈ flatDomain := by
  have hb : ∀ w : ℝ, ‖(flatSymbol w : ℂ) * ((flatSymbol w : ℂ) - lam)⁻¹‖ ≤
      1 + ‖lam‖ * |lam.im|⁻¹ := by
    intro w
    have e : (flatSymbol w : ℂ) * ((flatSymbol w : ℂ) - lam)⁻¹ =
        1 + lam * ((flatSymbol w : ℂ) - lam)⁻¹ := by
      field_simp [resolvent_denom_ne_zero hlam (flatSymbol w)]
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_mul]
    gcongr
    exact norm_resolvent_le hlam _
  have hm : Measurable fun w : ℝ => (flatSymbol w : ℂ) * ((flatSymbol w : ℂ) - lam)⁻¹ :=
    (Complex.measurable_ofReal.comp measurable_flatSymbol).mul
      ((measurable_resolvent (lam := lam)).comp measurable_flatSymbol)
  have hL := Lp.memLp (lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ)) hm
    (by positivity) hb (fourierL2 ℝ u))
  refine hL.ae_eq ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ)) hm (by positivity) hb
    (fourierL2 ℝ u), fourierL2_flatResolvent hlam u] with w h1 h2
  rw [h1, flatSymbolMul, h2]
  ring

/-- **`(S - λ)(S - λ)⁻¹ = 1`.** -/
theorem flatPrimitiveOp_flatResolvent (u : Lp ℂ 2 (volume : Measure ℝ)) :
    flatPrimitiveOp ⟨flatResolvent hlam u, flatResolvent_mem_flatDomain hlam u⟩ -
      lam • flatResolvent hlam u = u := by
  refine (Lp.fourierTransformₗᵢ ℝ ℂ).injective (Lp.ext ?_)
  change (fourierL2 ℝ (_ - _) : ℝ → ℂ) =ᵐ[volume] (fourierL2 ℝ u : ℝ → ℂ)
  rw [map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (fourierL2 ℝ (flatPrimitiveOp
      ⟨flatResolvent hlam u, flatResolvent_mem_flatDomain hlam u⟩))
      (lam • fourierL2 ℝ (flatResolvent hlam u)),
    Lp.coeFn_smul lam (fourierL2 ℝ (flatResolvent hlam u)),
    fourierL2_flatPrimitiveOp ⟨flatResolvent hlam u, flatResolvent_mem_flatDomain hlam u⟩,
    fourierL2_flatResolvent hlam u] with w h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, flatSymbolMul, h4, smul_eq_mul]
  change (flatSymbol w : ℂ) * (((flatSymbol w : ℂ) - lam)⁻¹ * _) - lam * (((flatSymbol w : ℂ) - lam)⁻¹ * _) = _
  have hne := resolvent_denom_ne_zero hlam (flatSymbol w)
  field_simp

/-- **`(S - λ)⁻¹ (S - λ) = 1` on the domain.** -/
theorem flatResolvent_flatPrimitiveOp (u : flatPrimitiveOp.domain) :
    flatResolvent hlam (flatPrimitiveOp u - lam • (u : Lp ℂ 2 (volume : Measure ℝ))) = u := by
  refine (Lp.fourierTransformₗᵢ ℝ ℂ).injective (Lp.ext ?_)
  change (fourierL2 ℝ _ : ℝ → ℂ) =ᵐ[volume] (fourierL2 ℝ u : ℝ → ℂ)
  filter_upwards [fourierL2_flatResolvent hlam (flatPrimitiveOp u - lam • (u : Lp ℂ 2 (volume : Measure ℝ))),
    Lp.coeFn_sub (fourierL2 ℝ (flatPrimitiveOp u)) (lam • fourierL2 ℝ (u : Lp ℂ 2 (volume : Measure ℝ))),
    Lp.coeFn_smul lam (fourierL2 ℝ (u : Lp ℂ 2 (volume : Measure ℝ))),
    fourierL2_flatPrimitiveOp u] with w h1 h2 h3 h4
  rw [h1, map_sub, map_smul, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, flatSymbolMul, smul_eq_mul]
  have hne := resolvent_denom_ne_zero hlam (flatSymbol w)
  field_simp

end Resolvent

end GaloisForLFunctions.HTGeometry
