import Mathlib

/-!
# Young's convolution inequality `L¹ ⋆ L² → L²`

Neither mathlib nor this tree carries a convolution norm inequality.  This file proves the one
needed to see a half-line integral operator with an `L¹` kernel as a bounded operator on `L²`:

`‖k ⋆ f‖₂ ≤ ‖k‖₁ · ‖f‖₂`.

Everything is stated in `ℝ≥0∞` for the absolute values, so no integrability hypothesis is needed
anywhere; the proof is Cauchy--Schwarz against the weight `|k| dy` followed by Tonelli and
translation invariance.

* `lintegral_weighted_sq_le` — `(∫ K·G)² ≤ (∫K)·(∫ K·G²)`;
* **`lintegral_convolution_sq_le`** — the inequality in `ℝ≥0∞` form;
* **`lintegral_enorm_sq_le_of_convolution_bound`** — the form an operator bound consumes: a
  function dominated pointwise by a convolution majorant has square integral at most
  `‖K‖₁² · ‖F‖₂²`.
-/

open MeasureTheory ENNReal Filter

namespace GaloisForLFunctions.HTGeometry

/-- **Cauchy--Schwarz against a weight.**  For `ℝ≥0∞`-valued measurable functions,
`(∫ K·G)² ≤ (∫K)·(∫ K·G²)`. -/
theorem lintegral_weighted_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K G : α → ℝ≥0∞} (hK : Measurable K) (hG : Measurable G) :
    (∫⁻ y, K y * G y ∂μ) ^ 2 ≤ (∫⁻ y, K y ∂μ) * ∫⁻ y, K y * G y ^ 2 ∂μ := by
  have hconj : Real.HolderConjugate 2 2 := by
    constructor <;> norm_num
  have hsplit : ∀ y, K y * G y = (K y ^ ((1 : ℝ) / 2)) * ((K y ^ ((1 : ℝ) / 2)) * G y) := by
    intro y
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hf : Measurable fun y => K y ^ ((1 : ℝ) / 2) := by fun_prop
  have hg : Measurable fun y => (K y ^ ((1 : ℝ) / 2)) * G y := hf.mul hG
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hf.aemeasurable hg.aemeasurable
  have hA : ∫⁻ y, (K y ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ = ∫⁻ y, K y ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul]
    norm_num
  have hB : ∫⁻ y, ((K y ^ ((1 : ℝ) / 2)) * G y) ^ (2 : ℝ) ∂μ
      = ∫⁻ y, K y * G y ^ 2 ∂μ := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
    norm_num
  have hmain : (∫⁻ y, K y * G y ∂μ)
      ≤ (∫⁻ y, K y ∂μ) ^ ((1 : ℝ) / 2) * (∫⁻ y, K y * G y ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
    calc ∫⁻ y, K y * G y ∂μ
        = ∫⁻ y, (K y ^ ((1 : ℝ) / 2)) * ((K y ^ ((1 : ℝ) / 2)) * G y) ∂μ := by
          exact lintegral_congr fun y => hsplit y
      _ ≤ (∫⁻ y, (K y ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2)
          * (∫⁻ y, ((K y ^ ((1 : ℝ) / 2)) * G y) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := by
          simpa using hholder
      _ = (∫⁻ y, K y ∂μ) ^ ((1 : ℝ) / 2) * (∫⁻ y, K y * G y ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
          rw [hA, hB]
  calc (∫⁻ y, K y * G y ∂μ) ^ 2
      ≤ ((∫⁻ y, K y ∂μ) ^ ((1 : ℝ) / 2)
          * (∫⁻ y, K y * G y ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 := by
        exact pow_le_pow_left' hmain 2
    _ = (∫⁻ y, K y ∂μ) * ∫⁻ y, K y * G y ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast ((∫⁻ y, K y ∂μ) ^ ((1 : ℝ) / 2)) 2,
          ← ENNReal.rpow_natCast ((∫⁻ y, K y * G y ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) 2,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

/-- **Young's convolution inequality in `ℝ≥0∞` form.** -/
theorem lintegral_convolution_sq_le {K F : ℝ → ℝ≥0∞} (hK : Measurable K) (hF : Measurable F) :
    ∫⁻ x, (∫⁻ y, K y * F (x - y)) ^ 2 ≤ (∫⁻ y, K y) ^ 2 * ∫⁻ x, F x ^ 2 := by
  have hprod : Measurable fun p : ℝ × ℝ => K p.2 * F (p.1 - p.2) ^ 2 :=
    (hK.comp measurable_snd).mul ((hF.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  have hstep : ∀ x : ℝ, (∫⁻ y, K y * F (x - y)) ^ 2
      ≤ (∫⁻ y, K y) * ∫⁻ y, K y * F (x - y) ^ 2 := by
    intro x
    exact lintegral_weighted_sq_le volume hK (hF.comp (measurable_const.sub measurable_id))
  calc ∫⁻ x, (∫⁻ y, K y * F (x - y)) ^ 2
      ≤ ∫⁻ x, (∫⁻ y, K y) * ∫⁻ y, K y * F (x - y) ^ 2 := lintegral_mono hstep
    _ = (∫⁻ y, K y) * ∫⁻ x, ∫⁻ y, K y * F (x - y) ^ 2 := by
        rw [lintegral_const_mul _ (by fun_prop)]
    _ = (∫⁻ y, K y) * ∫⁻ y, ∫⁻ x, K y * F (x - y) ^ 2 := by
        rw [lintegral_lintegral_swap hprod.aemeasurable]
    _ = (∫⁻ y, K y) * ∫⁻ y, K y * ∫⁻ x, F x ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        have hmeas : Measurable fun x : ℝ => F (x - y) ^ 2 := by fun_prop
        rw [lintegral_const_mul _ hmeas]
        congr 1
        exact lintegral_sub_right_eq_self (fun x => F x ^ 2) y
    _ = (∫⁻ y, K y) ^ 2 * ∫⁻ x, F x ^ 2 := by
        rw [lintegral_mul_const _ hK, sq]
        ring

/-- **Operator form.**  A function dominated pointwise by the convolution majorant `K ⋆ F` has
square integral at most `(∫K)²·∫F²`.  For `K = ‖k‖₊` and `F = ‖f‖₊` this is `‖k ⋆ f‖₂ ≤ ‖k‖₁‖f‖₂`,
the boundedness of convolution by an `L¹` kernel on `L²`. -/
theorem lintegral_enorm_sq_le_of_convolution_bound {E : Type*} [NormedAddCommGroup E]
    {G : ℝ → E} {K F : ℝ → ℝ≥0∞} (hK : Measurable K) (hF : Measurable F)
    (hG : ∀ x, ‖G x‖ₑ ≤ ∫⁻ y, K y * F (x - y)) :
    ∫⁻ x, ‖G x‖ₑ ^ 2 ≤ (∫⁻ y, K y) ^ 2 * ∫⁻ x, F x ^ 2 :=
  le_trans (lintegral_mono fun x => pow_le_pow_left' (hG x) 2)
    (lintegral_convolution_sq_le hK hF)

/-! ### The real-valued line convolution -/

/-- Convolution on the line: `(k ⋆ V) x = ∫ k t · V (x − t) dt`. -/
noncomputable def lineConvolution (k V : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, k t * V (x - t)

/-- **Young's inequality `L¹ ⋆ L² → L²`, real form.**  The Bochner integrals are recovered from
the `ℝ≥0∞` inequality by `toReal`, which is monotone because the majorant `(∫|ρ|)²·∫u²` is finite. -/
theorem integral_sq_lineConvolution_le {ρ u : ℝ → ℝ} (hρm : Measurable ρ) (hum : Measurable u)
    (hρi : Integrable (fun t => |ρ t|)) (hu2 : Integrable (fun x => u x ^ 2))
    (hconv : Integrable (fun x => lineConvolution ρ u x ^ 2)) :
    (∫ x, lineConvolution ρ u x ^ 2) ≤ (∫ t, |ρ t|) ^ 2 * ∫ x, u x ^ 2 := by
  have hbound : ∀ x, ‖lineConvolution ρ u x‖ₑ ≤ ∫⁻ y, ‖ρ y‖ₑ * ‖u (x - y)‖ₑ := by
    intro x
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    exact lintegral_congr fun t => enorm_mul _ _
  have hmain := lintegral_enorm_sq_le_of_convolution_bound hρm.enorm hum.enorm hbound
  have hBfin : (∫⁻ t, ‖ρ t‖ₑ) ≠ ⊤ := by
    have h := hρi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa using h.ne
  have hDfin : (∫⁻ x, ‖u x‖ₑ ^ 2) ≠ ⊤ := by
    have h := hu2.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at h
    simpa [enorm_pow] using h.ne
  have hBeq : (∫⁻ t, ‖ρ t‖ₑ).toReal = ∫ t, |ρ t| := by
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun t => abs_nonneg _)
      hρi.aestronglyMeasurable]
    congr 1
    exact lintegral_congr fun t => Real.enorm_eq_ofReal_abs (ρ t)
  have hsq : ∀ f : ℝ → ℝ, Integrable (fun x => f x ^ 2) →
      (∫⁻ x, ‖f x‖ₑ ^ 2).toReal = ∫ x, f x ^ 2 := by
    intro f hf
    rw [integral_eq_lintegral_of_nonneg_ae (.of_forall fun x => sq_nonneg _)
      hf.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [← hsq _ hconv, ← hBeq, ← hsq _ hu2, ← ENNReal.toReal_pow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hBfin) hDfin) hmain

end GaloisForLFunctions.HTGeometry
