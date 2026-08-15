import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Scalar multiplication by a bounded measurable symbol on vector-valued `Lᵖ`

Pointwise scalar multiplication by a measurable symbol bounded by `C` maps `Lᵖ(μ; H)` to itself with
operator norm at most `C`, for any normed space `H` over the scalar field.  The estimate is the
pointwise bound `‖φ x • f x‖ = ‖φ x‖‖f x‖ ≤ C‖f x‖` integrated through the `Lᵖ` seminorm; no duality
or interpolation is used.

This is the Hilbert-valued form of the bounded multiplier, and it is what conjugation by the
vector-valued Plancherel transform turns into a vector-valued Fourier multiplier.
-/

noncomputable section

namespace MeasureTheory

open scoped ENNReal

variable {α 𝕜 H : Type*} [MeasurableSpace α] [RCLike 𝕜]
variable [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` seminorm of a bounded scalar multiple is bounded by the symbol bound times the
seminorm. -/
theorem eLpNorm_smul_le_of_bound {φ : α → 𝕜} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (g : α → H) :
    eLpNorm (fun x => φ x • g x) p μ ≤ ENNReal.ofReal C * eLpNorm g p μ := by
  have hmono : eLpNorm (fun x => φ x • g x) p μ ≤ eLpNorm (((C : ℝ) : 𝕜) • g) p μ := by
    refine eLpNorm_mono_ae ?_
    filter_upwards with x
    rw [norm_smul, Pi.smul_apply, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)
  have heq := eLpNorm_const_smul (((C : ℝ) : 𝕜)) g p μ
  rw [heq] at hmono
  have hnorm : ‖(((C : ℝ) : 𝕜))‖ₑ = ENNReal.ofReal C := by
    rw [← ofReal_norm, RCLike.norm_ofReal, abs_of_nonneg hC0]
  rwa [hnorm] at hmono

omit [Fact (1 ≤ p)] in
/-- A bounded measurable symbol scales every `Lᵖ` function into `Lᵖ`. -/
theorem memLp_smul_of_bound {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) (f : Lp H p μ) :
    MemLp (fun x => φ x • (f : α → H) x) p μ := by
  refine ⟨hφ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f), ?_⟩
  refine lt_of_le_of_lt (eLpNorm_smul_le_of_bound hC0 hC _) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_ne_top f).lt_top

/-- Scalar multiplication by a bounded measurable symbol, as a linear map on vector-valued `Lᵖ`. -/
def lpBoundedSmulLM {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) : Lp H p μ →ₗ[𝕜] Lp H p μ where
  toFun f := (memLp_smul_of_bound hφ hC0 hC f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC (f + g)),
      Lp.coeFn_add ((memLp_smul_of_bound hφ hC0 hC f).toLp _)
        ((memLp_smul_of_bound hφ hC0 hC g).toLp _),
      MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC f),
      MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC g),
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC (c • f)),
      Lp.coeFn_smul c ((memLp_smul_of_bound hφ hC0 hC f).toLp _),
      MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC f),
      Lp.coeFn_smul c f] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
    rw [smul_comm]

/-- Scalar multiplication by a bounded measurable symbol, as a continuous linear map on
vector-valued `Lᵖ` of operator norm at most the symbol bound. -/
def lpBoundedSmulCLM {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C) : Lp H p μ →L[𝕜] Lp H p μ :=
  LinearMap.mkContinuous (lpBoundedSmulLM hφ hC0 hC) C (by
    intro f
    change ‖(memLp_smul_of_bound hφ hC0 hC f).toLp _‖ ≤ C * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    have hle := eLpNorm_smul_le_of_bound (p := p) (μ := μ) hC0 hC ((f : α → H))
    have hfin : eLpNorm ((f : α → H)) p μ ≠ ∞ := Lp.eLpNorm_ne_top f
    have htoReal :
        (eLpNorm (fun x => φ x • (f : α → H) x) p μ).toReal ≤
          (ENNReal.ofReal C * eLpNorm ((f : α → H)) p μ).toReal := by
      refine ENNReal.toReal_mono ?_ hle
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    refine htoReal.trans ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0])

@[simp] theorem lpBoundedSmulCLM_coeFn {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (f : Lp H p μ) :
    (lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hφ hC0 hC f : α → H) =ᵐ[μ]
      fun x => φ x • (f : α → H) x :=
  MemLp.coeFn_toLp (memLp_smul_of_bound hφ hC0 hC f)

theorem norm_lpBoundedSmulCLM_le {φ : α → 𝕜} (hφ : Measurable φ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) :
    ‖lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hφ hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- Two bounded symbols agreeing almost everywhere induce the same multiplier. -/
theorem lpBoundedSmulCLM_congr {φ ψ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    {C D : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C)
    (hD0 : 0 ≤ D) (hD : ∀ x, ‖ψ x‖ ≤ D) (hae : φ =ᵐ[μ] ψ) :
    lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hφ hC0 hC =
      lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hψ hD0 hD := by
  ext f
  filter_upwards [lpBoundedSmulCLM_coeFn (p := p) (μ := μ) (H := H) hφ hC0 hC f,
    lpBoundedSmulCLM_coeFn (p := p) (μ := μ) (H := H) hψ hD0 hD f, hae] with x h1 h2 h3
  rw [h1, h2, h3]

/-- **The composite of two scalar multipliers is the multiplier of the product symbol.** -/
theorem lpBoundedSmulCLM_comp {φ ψ χ : α → 𝕜} (hφ : Measurable φ) (hψ : Measurable ψ)
    (hχ : Measurable χ) {C D B : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x, ‖φ x‖ ≤ C) (hD0 : 0 ≤ D)
    (hD : ∀ x, ‖ψ x‖ ≤ D) (hB0 : 0 ≤ B) (hB : ∀ x, ‖χ x‖ ≤ B)
    (hae : ∀ᵐ x ∂μ, χ x = φ x * ψ x) :
    (lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hφ hC0 hC).comp
        (lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hψ hD0 hD)
      = lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hχ hB0 hB := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [lpBoundedSmulCLM_coeFn (p := p) (μ := μ) (H := H) hφ hC0 hC
      (lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hψ hD0 hD f),
    lpBoundedSmulCLM_coeFn (p := p) (μ := μ) (H := H) hψ hD0 hD f,
    lpBoundedSmulCLM_coeFn (p := p) (μ := μ) (H := H) hχ hB0 hB f, hae] with x h1 h2 h3 h4
  show ((lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hφ hC0 hC
      (lpBoundedSmulCLM (p := p) (μ := μ) (H := H) hψ hD0 hD f) : Lp H p μ) : α → H) x = _
  rw [h1, h2, h3, h4, mul_smul]

end MeasureTheory
