import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiplication by a bounded measurable function on `Lᵖ`

Pointwise multiplication by a measurable function bounded by `C` maps `Lᵖ` to itself with operator
norm at most `C`.  The estimate is the pointwise bound `‖φ x · f x‖ ≤ C ‖f x‖` integrated through
the `Lᵖ` seminorm, so no duality or interpolation is used.

This is the multiplier operator that the indicator cutoffs are special cases of, stated once for a
general bounded symbol.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

variable {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜] [SecondCountableTopology 𝕜]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [SecondCountableTopology 𝕜] [Fact (1 ≤ p)] in
/-- The `Lᵖ` seminorm of a bounded multiple is bounded by the symbol bound times the seminorm. -/
theorem eLpNorm_mul_le_of_bound {φ : α → 𝕜} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (g : α → 𝕜) :
    eLpNorm (fun x => φ x * g x) p μ ≤ ‖(C : ℝ)‖ₑ * eLpNorm g p μ := by
  have hmono : eLpNorm (fun x => φ x * g x) p μ ≤ eLpNorm ((C : ℝ) • g) p μ := by
    refine eLpNorm_mono_ae ?_
    filter_upwards with x
    rw [norm_mul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  exact hmono.trans_eq (eLpNorm_const_smul (C : ℝ) g p μ)

omit [Fact (1 ≤ p)] in
/-- A bounded measurable symbol multiplies every `Lᵖ` function into `Lᵖ`. -/
theorem memLp_mul_of_bound {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (f : Lp 𝕜 p μ) :
    MemLp (fun x => φ x * (f : α → 𝕜) x) p μ := by
  refine ⟨hφ.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f), ?_⟩
  refine lt_of_le_of_lt (eLpNorm_mul_le_of_bound hC0 hC _) ?_
  exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) (Lp.eLpNorm_ne_top f).lt_top

/-- Multiplication by a bounded measurable symbol, as a linear map on `Lᵖ`. -/
def lpBoundedMulLM {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) : Lp 𝕜 p μ →ₗ[𝕜] Lp 𝕜 p μ where
  toFun f := (memLp_mul_of_bound hφ hC0 hC f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC (f + g)),
      Lp.coeFn_add ((memLp_mul_of_bound hφ hC0 hC f).toLp _)
        ((memLp_mul_of_bound hφ hC0 hC g).toLp _),
      MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC f),
      MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC (c • f)),
      Lp.coeFn_smul c ((memLp_mul_of_bound hφ hC0 hC f).toLp _),
      MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC f),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplication by a bounded measurable symbol, as a continuous linear map on `Lᵖ` of operator
norm at most the symbol bound. -/
def lpBoundedMulCLM {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  LinearMap.mkContinuous (lpBoundedMulLM hφ hC0 hC) C (by
    intro f
    change ‖(memLp_mul_of_bound hφ hC0 hC f).toLp _‖ ≤ C * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    have hle := eLpNorm_mul_le_of_bound (p := p) (μ := μ) hC0 hC ((f : α → 𝕜))
    have hfin : eLpNorm ((f : α → 𝕜)) p μ ≠ ∞ := Lp.eLpNorm_ne_top f
    have htoReal :
        (eLpNorm (fun x => φ x * (f : α → 𝕜) x) p μ).toReal ≤
          (‖(C : ℝ)‖ₑ * eLpNorm ((f : α → 𝕜)) p μ).toReal := by
      refine ENNReal.toReal_mono ?_ hle
      exact ENNReal.mul_ne_top (by simp [enorm_eq_nnnorm]) hfin
    refine htoReal.trans ?_
    rw [ENNReal.toReal_mul]
    have hnorm : (‖(C : ℝ)‖ₑ).toReal = C := by
      simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC0]
    rw [hnorm])

@[simp] theorem lpBoundedMulCLM_coeFn {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (f : Lp 𝕜 p μ) :
    (lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC f : α → 𝕜) =ᵐ[μ]
      fun x => φ x * (f : α → 𝕜) x :=
  MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC0 hC f)

theorem norm_lpBoundedMulCLM_le {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) :
    ‖lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- Two bounded symbols agreeing almost everywhere induce the same multiplier. -/
theorem lpBoundedMulCLM_congr {φ ψ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hD0 : 0 ≤ D) (hD : ∀ x, ‖ψ x‖ ≤ D) (hae : φ =ᵐ[μ] ψ) :
    lpBoundedMulCLM (p := p) (μ := μ) hφ hC0 hC =
      lpBoundedMulCLM (p := p) (μ := μ) hψ hD0 hD := by
  ext f
  filter_upwards [lpBoundedMulCLM_coeFn (p := p) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := p) (μ := μ) hψ hD0 hD f, hae] with x h1 h2 h3
  rw [h1, h2, h3]

omit [SecondCountableTopology 𝕜] in
/-- An operator that acts almost everywhere as multiplication by a bounded symbol has operator
norm at most the symbol bound.  No identification of the operator with a multiplier is needed. -/
theorem norm_le_of_ae_mul {T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ} {ψ : α → 𝕜} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x, ‖ψ x‖ ≤ K)
    (hT : ∀ f : Lp 𝕜 p μ, ((T f : Lp 𝕜 p μ) : α → 𝕜) =ᵐ[μ]
      fun x => ψ x * (f : α → 𝕜) x) :
    ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK0 fun f => ?_
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hT f)]
  have hle := eLpNorm_mul_le_of_bound (p := p) (μ := μ) hK0 hK ((f : α → 𝕜))
  have hfin : eLpNorm ((f : α → 𝕜)) p μ ≠ ∞ := Lp.eLpNorm_ne_top f
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp [enorm_eq_nnnorm]) hfin) hle
  refine h.trans ?_
  rw [ENNReal.toReal_mul]
  have hnorm : (‖(K : ℝ)‖ₑ).toReal = K := by
    simp [enorm_eq_nnnorm, Real.norm_eq_abs, abs_of_nonneg hK0]
  rw [hnorm]

/-! ## Multipliers and the `L²` inner product -/

/-- **Multiplication by a real-valued bounded symbol is self-adjoint on `L²`.** -/
theorem lpBoundedMulCLM_inner_real {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (hreal : ∀ x, (starRingEnd 𝕜) (φ x) = φ x) (f g : Lp 𝕜 2 μ) :
    (inner 𝕜 (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f) g : 𝕜)
      = inner 𝕜 f (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul, hreal]
  ring

/-- **Multiplication by a unimodular bounded symbol preserves the `L²` inner product.** -/
theorem lpBoundedMulCLM_inner_unimodular {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (huni : ∀ x, (starRingEnd 𝕜) (φ x) * φ x = 1) (f g : Lp 𝕜 2 μ) :
    (inner 𝕜 (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC f)
        (lpBoundedMulCLM (p := 2) (μ := μ) hφ hC0 hC g) : 𝕜)
      = inner 𝕜 f g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC f,
    lpBoundedMulCLM_coeFn (p := 2) (μ := μ) hφ hC0 hC g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  calc (starRingEnd 𝕜) (φ x) * (starRingEnd 𝕜) ((f : α → 𝕜) x) * (φ x * (g : α → 𝕜) x)
      = ((starRingEnd 𝕜) (φ x) * φ x) *
          ((starRingEnd 𝕜) ((f : α → 𝕜) x) * (g : α → 𝕜) x) := by ring
    _ = (starRingEnd 𝕜) ((f : α → 𝕜) x) * (g : α → 𝕜) x := by rw [huni x, one_mul]

end MeasureTheory