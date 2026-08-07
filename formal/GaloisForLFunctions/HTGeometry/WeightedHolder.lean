import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
/-!
# Weighted Cauchy–Schwarz over an arbitrary measure

The weighted Cauchy–Schwarz inequality

`∫ ‖g₁‖‖g₂‖‖W‖ ≤ (∫ ‖g₁‖²‖W‖)^{1/2}(∫ ‖g₂‖²‖W‖)^{1/2}`

uses nothing about its domain or its measure: splitting the weight symmetrically reduces it to Hölder with
conjugate exponents `2, 2`.  Stated here for an arbitrary measure space, so that the version on the whole line
and the version on a truncation `volume.restrict (Icc (−T) T)` are both instances.  The truncated form is the
one a vertical-integral estimate needs, because the uniform bound of a smoothed Perron kernel on a bounded
height range carries none of the `(N/H)²` that its global quadratic-decay bound does.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Weighted Cauchy–Schwarz over an arbitrary measure.**  The integral of a product of two moduli against a
weight is bounded by the two weighted mean squares:

`∫ ‖g₁‖‖g₂‖‖W‖ ≤ (∫ ‖g₁‖²‖W‖)^{1/2}(∫ ‖g₂‖²‖W‖)^{1/2}`.

Splitting the weight symmetrically reduces this to Hölder with conjugate exponents `2, 2`, which holds for any
measure; nothing about the domain or the measure enters.  The versions on the line, whether over the whole line
or over a truncation of it, are instances. -/
theorem integral_mul_mul_weight_le_sqrt_mul_sqrt_measure {g₁ g₂ W : α → ℂ}
    (hm1 : AEStronglyMeasurable g₁ μ) (hm2 : AEStronglyMeasurable g₂ μ)
    (hmW : AEStronglyMeasurable W μ)
    (h1 : Integrable (fun y => ‖g₁ y‖ ^ 2 * ‖W y‖) μ)
    (h2 : Integrable (fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) μ) :
    (∫ y, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ ∂μ)
      ≤ Real.sqrt (∫ y, ‖g₁ y‖ ^ 2 * ‖W y‖ ∂μ)
          * Real.sqrt (∫ y, ‖g₂ y‖ ^ 2 * ‖W y‖ ∂μ) := by
  set F : α → ℝ := fun y => ‖g₁ y‖ * Real.sqrt ‖W y‖ with hF
  set G : α → ℝ := fun y => ‖g₂ y‖ * Real.sqrt ‖W y‖ with hG
  have hFsq : ∀ y, F y ^ 2 = ‖g₁ y‖ ^ 2 * ‖W y‖ := by
    intro y
    rw [hF]
    have hsq : Real.sqrt ‖W y‖ ^ 2 = ‖W y‖ := Real.sq_sqrt (norm_nonneg _)
    calc (‖g₁ y‖ * Real.sqrt ‖W y‖) ^ 2 = ‖g₁ y‖ ^ 2 * (Real.sqrt ‖W y‖) ^ 2 := by ring
      _ = ‖g₁ y‖ ^ 2 * ‖W y‖ := by rw [hsq]
  have hGsq : ∀ y, G y ^ 2 = ‖g₂ y‖ ^ 2 * ‖W y‖ := by
    intro y
    rw [hG]
    have hsq : Real.sqrt ‖W y‖ ^ 2 = ‖W y‖ := Real.sq_sqrt (norm_nonneg _)
    calc (‖g₂ y‖ * Real.sqrt ‖W y‖) ^ 2 = ‖g₂ y‖ ^ 2 * (Real.sqrt ‖W y‖) ^ 2 := by ring
      _ = ‖g₂ y‖ ^ 2 * ‖W y‖ := by rw [hsq]
  have hFm : AEStronglyMeasurable F μ :=
    (hm1.norm).mul (Real.continuous_sqrt.comp_aestronglyMeasurable hmW.norm)
  have hGm : AEStronglyMeasurable G μ :=
    (hm2.norm).mul (Real.continuous_sqrt.comp_aestronglyMeasurable hmW.norm)
  have hFint : Integrable (fun y => ‖F y‖ ^ 2) μ := by
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, hFsq]
  have hGint : Integrable (fun y => ‖G y‖ ^ 2) μ := by
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, hGsq]
  have hFLp : MemLp F 2 μ := (memLp_two_iff_integrable_sq_norm hFm).mpr hFint
  have hGLp : MemLp G 2 μ := (memLp_two_iff_integrable_sq_norm hGm).mpr hGint
  have hFnn : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall fun y => by rw [hF]; positivity
  have hGnn : 0 ≤ᵐ[μ] G := Filter.Eventually.of_forall fun y => by rw [hG]; positivity
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hFnn hGnn
    (by simpa using hFLp) (by simpa using hGLp)
  have hpt : ∀ y, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ = F y * G y := by
    intro y
    rw [hF, hG]
    have hsq : Real.sqrt ‖W y‖ * Real.sqrt ‖W y‖ = ‖W y‖ := Real.mul_self_sqrt (norm_nonneg _)
    calc ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖
        = ‖g₁ y‖ * ‖g₂ y‖ * (Real.sqrt ‖W y‖ * Real.sqrt ‖W y‖) := by rw [hsq]
      _ = ‖g₁ y‖ * Real.sqrt ‖W y‖ * (‖g₂ y‖ * Real.sqrt ‖W y‖) := by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  refine hcs.trans (le_of_eq ?_)
  have hFpow : (∫ y, F y ^ (2 : ℝ) ∂μ) = ∫ y, ‖g₁ y‖ ^ 2 * ‖W y‖ ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.rpow_two, hFsq]
  have hGpow : (∫ y, G y ^ (2 : ℝ) ∂μ) = ∫ y, ‖g₂ y‖ ^ 2 * ‖W y‖ ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [Real.rpow_two, hGsq]
  rw [hFpow, hGpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Weighted Cauchy–Schwarz for the modulus of an integral, over an arbitrary measure.** -/
theorem norm_integral_mul_mul_le_sqrt_mul_sqrt_measure {g₁ g₂ W : α → ℂ}
    (hm1 : AEStronglyMeasurable g₁ μ) (hm2 : AEStronglyMeasurable g₂ μ)
    (hmW : AEStronglyMeasurable W μ)
    (h1 : Integrable (fun y => ‖g₁ y‖ ^ 2 * ‖W y‖) μ)
    (h2 : Integrable (fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) μ) :
    ‖∫ y, g₁ y * g₂ y * W y ∂μ‖
      ≤ Real.sqrt (∫ y, ‖g₁ y‖ ^ 2 * ‖W y‖ ∂μ)
          * Real.sqrt (∫ y, ‖g₂ y‖ ^ 2 * ‖W y‖ ∂μ) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ y, ‖g₁ y * g₂ y * W y‖ = ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ := fun y => by
    rw [norm_mul, norm_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_mul_mul_weight_le_sqrt_mul_sqrt_measure hm1 hm2 hmW h1 h2

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Cauchy–Schwarz without a weight, over an arbitrary measure.**  The weighted inequality at `W ≡ 1`. -/
theorem integral_mul_le_sqrt_mul_sqrt_measure {g₁ g₂ : α → ℂ}
    (hm1 : AEStronglyMeasurable g₁ μ) (hm2 : AEStronglyMeasurable g₂ μ)
    (h1 : Integrable (fun y => ‖g₁ y‖ ^ 2) μ) (h2 : Integrable (fun y => ‖g₂ y‖ ^ 2) μ) :
    (∫ y, ‖g₁ y‖ * ‖g₂ y‖ ∂μ)
      ≤ Real.sqrt (∫ y, ‖g₁ y‖ ^ 2 ∂μ) * Real.sqrt (∫ y, ‖g₂ y‖ ^ 2 ∂μ) := by
  have h := integral_mul_mul_weight_le_sqrt_mul_sqrt_measure (W := fun _ : α => (1 : ℂ))
    hm1 hm2 aestronglyMeasurable_const (by simpa using h1) (by simpa using h2)
  simpa using h

/-- The product of two moduli is integrable when both mean squares are. -/
theorem integrable_mul_norm_of_integrable_sq {g₁ g₂ : α → ℂ}
    (hm1 : AEStronglyMeasurable g₁ μ) (hm2 : AEStronglyMeasurable g₂ μ)
    (h1 : Integrable (fun y => ‖g₁ y‖ ^ 2) μ) (h2 : Integrable (fun y => ‖g₂ y‖ ^ 2) μ) :
    Integrable (fun y => ‖g₁ y‖ * ‖g₂ y‖) μ := by
  refine Integrable.mono' (h1.add h2) ((hm1.norm).mul (hm2.norm)) ?_
  filter_upwards with y
  have h0 : (0 : ℝ) ≤ ‖g₁ y‖ * ‖g₂ y‖ := by positivity
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  nlinarith [sq_nonneg (‖g₁ y‖ - ‖g₂ y‖)]

/-- **The three-factor inequality with a uniformly bounded weight.**  Two factors in mean square, one bounded
pointwise, and the weight bounded uniformly:

`‖∫ g₁g₂g₃W ∂μ‖ ≤ M·Wsup·(∫‖g₁‖² ∂μ)^{1/2}(∫‖g₂‖² ∂μ)^{1/2}`.

On a bounded height range this is the form a smoothed Perron kernel supports with `Wsup = (N+H)^σ/σ`, which
carries none of the penalty of its global quadratic-decay bound. -/
theorem norm_integral_mul_three_le_sup_mul_sqrt_measure {g₁ g₂ g₃ W : α → ℂ} {M Wsup : ℝ}
    (hm1 : AEStronglyMeasurable g₁ μ) (hm2 : AEStronglyMeasurable g₂ μ)
    (hM0 : 0 ≤ M) (hW0 : 0 ≤ Wsup) (hM : ∀ y, ‖g₃ y‖ ≤ M) (hW : ∀ y, ‖W y‖ ≤ Wsup)
    (h1 : Integrable (fun y => ‖g₁ y‖ ^ 2) μ) (h2 : Integrable (fun y => ‖g₂ y‖ ^ 2) μ) :
    ‖∫ y, g₁ y * g₂ y * g₃ y * W y ∂μ‖
      ≤ M * Wsup * (Real.sqrt (∫ y, ‖g₁ y‖ ^ 2 ∂μ) * Real.sqrt (∫ y, ‖g₂ y‖ ^ 2 ∂μ)) := by
  classical
  have hcross := integrable_mul_norm_of_integrable_sq hm1 hm2 h1 h2
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hbound : ∀ y, ‖g₁ y * g₂ y * g₃ y * W y‖ ≤ M * Wsup * (‖g₁ y‖ * ‖g₂ y‖) := by
    intro y
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖g₁ y‖ * ‖g₂ y‖ * ‖g₃ y‖ * ‖W y‖
        ≤ ‖g₁ y‖ * ‖g₂ y‖ * M * Wsup := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hM y) (by positivity)) (hW y)
            (norm_nonneg _) (by positivity)
      _ = M * Wsup * (‖g₁ y‖ * ‖g₂ y‖) := by ring
  have hmono : (∫ y, ‖g₁ y * g₂ y * g₃ y * W y‖ ∂μ)
      ≤ ∫ y, M * Wsup * (‖g₁ y‖ * ‖g₂ y‖) ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
      (hcross.const_mul (M * Wsup)) (Filter.Eventually.of_forall hbound)
  refine hmono.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM0 hW0)
  exact integral_mul_le_sqrt_mul_sqrt_measure hm1 hm2 h1 h2

end GaloisForLFunctions.HTGeometry
end
