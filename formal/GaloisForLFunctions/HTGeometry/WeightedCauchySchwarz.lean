import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
import GaloisForLFunctions.HTGeometry.WeightedHolder

/-!
# Cauchy–Schwarz for a weighted integral

A product of two factors integrated against a nonnegative weight is bounded by the two weighted mean
squares:

`‖∫ g₁ g₂ W‖ ≤ (∫ ‖g₁‖²‖W‖)^{1/2} (∫ ‖g₂‖²‖W‖)^{1/2}`.

Splitting the weight symmetrically, `‖g₁ g₂ W‖ = (‖g₁‖√‖W‖)(‖g₂‖√‖W‖)`, reduces this to Hölder's
inequality with conjugate exponents `2, 2`.  This is the device that turns a vertical-line integral of a
product of Dirichlet series into two mean squares, one of which can be estimated pointwise and the other
by a mean-value theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- **The weighted Cauchy–Schwarz inequality, in the form of the integral of the moduli.**  This is the step
that the vertical-integral bound uses through the triangle inequality, and it is also what makes the weighted
`L²` quantity subadditive. -/
theorem integral_mul_mul_weight_le_sqrt_mul_sqrt {g₁ g₂ W : ℝ → ℂ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hmW : AEStronglyMeasurable W volume)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    (∫ y : ℝ, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖)
      ≤ Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖) :=
  integral_mul_mul_weight_le_sqrt_mul_sqrt_measure hm1 hm2 hmW h1 h2

/-- **Cauchy–Schwarz for a weighted vertical integral.**  A product of two factors against a weight is
bounded by the two weighted mean squares. -/
theorem norm_integral_mul_mul_le_sqrt_mul_sqrt {g₁ g₂ W : ℝ → ℂ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hmW : AEStronglyMeasurable W volume)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    ‖∫ y : ℝ, g₁ y * g₂ y * W y‖
      ≤ Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖) := by
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hpt : ∀ y : ℝ, ‖g₁ y * g₂ y * W y‖ = ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ := fun y => by
    rw [norm_mul, norm_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_mul_mul_weight_le_sqrt_mul_sqrt hm1 hm2 hmW h1 h2

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- **Cauchy–Schwarz with one factor bounded pointwise.**  Absorbing the bounded factor into the weight
turns the two-factor inequality into

`‖∫ g₁ g₂ g₃ W‖ ≤ (sup ‖g₃‖) · (∫ ‖g₁‖²‖W‖)^{1/2} (∫ ‖g₂‖²‖W‖)^{1/2}`.

This is the shape a vertical-line integral of three Dirichlet series takes when one of them is estimated by
an Euler product and the other two in mean square. -/
theorem norm_integral_mul_three_le_sup_mul_sqrt_mul_sqrt {g₁ g₂ g₃ W : ℝ → ℂ} {M : ℝ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hm3 : AEStronglyMeasurable g₃ volume) (hmW : AEStronglyMeasurable W volume)
    (hM : ∀ y : ℝ, ‖g₃ y‖ ≤ M)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    ‖∫ y : ℝ, g₁ y * g₂ y * g₃ y * W y‖
      ≤ M * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set W' : ℝ → ℂ := fun y => g₃ y * W y with hW'
  have hW'norm : ∀ y : ℝ, ‖W' y‖ ≤ M * ‖W y‖ := by
    intro y
    rw [hW', norm_mul]
    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
  have hW'm : AEStronglyMeasurable W' volume := hm3.mul hmW
  have hdom : ∀ (g : ℝ → ℂ), AEStronglyMeasurable g volume →
      (Integrable fun y => ‖g y‖ ^ 2 * ‖W y‖) →
      (Integrable fun y => ‖g y‖ ^ 2 * ‖W' y‖)
        ∧ (∫ y : ℝ, ‖g y‖ ^ 2 * ‖W' y‖) ≤ M * ∫ y : ℝ, ‖g y‖ ^ 2 * ‖W y‖ := by
    intro g hgm hg
    have hbound : ∀ y : ℝ, ‖g y‖ ^ 2 * ‖W' y‖ ≤ M * (‖g y‖ ^ 2 * ‖W y‖) := by
      intro y
      have h := mul_le_mul_of_nonneg_left (hW'norm y) (sq_nonneg ‖g y‖)
      calc ‖g y‖ ^ 2 * ‖W' y‖ ≤ ‖g y‖ ^ 2 * (M * ‖W y‖) := h
        _ = M * (‖g y‖ ^ 2 * ‖W y‖) := by ring
    have hmeas : AEStronglyMeasurable (fun y : ℝ => ‖g y‖ ^ 2 * ‖W' y‖) volume :=
      ((hgm.norm).pow 2).mul hW'm.norm
    have hgM : Integrable fun y : ℝ => M * (‖g y‖ ^ 2 * ‖W y‖) := hg.const_mul M
    have hint : Integrable fun y : ℝ => ‖g y‖ ^ 2 * ‖W' y‖ := by
      refine Integrable.mono' hgM hmeas ?_
      filter_upwards with y
      have h0 : (0 : ℝ) ≤ ‖g y‖ ^ 2 * ‖W' y‖ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hbound y
    refine ⟨hint, ?_⟩
    have hmono : (∫ y : ℝ, ‖g y‖ ^ 2 * ‖W' y‖) ≤ ∫ y : ℝ, M * (‖g y‖ ^ 2 * ‖W y‖) :=
      integral_mono hint hgM hbound
    rwa [integral_const_mul] at hmono
  obtain ⟨h1', h1le⟩ := hdom g₁ hm1 h1
  obtain ⟨h2', h2le⟩ := hdom g₂ hm2 h2
  have hcs := norm_integral_mul_mul_le_sqrt_mul_sqrt hm1 hm2 hW'm h1' h2'
  have hassoc : ∀ y : ℝ, g₁ y * g₂ y * g₃ y * W y = g₁ y * g₂ y * W' y := by
    intro y
    rw [hW']
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hassoc)]
  refine hcs.trans ?_
  have hs1 : Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W' y‖)
      ≤ Real.sqrt M * Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖) := by
    rw [← Real.sqrt_mul hM0]
    exact Real.sqrt_le_sqrt h1le
  have hs2 : Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W' y‖)
      ≤ Real.sqrt M * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖) := by
    rw [← Real.sqrt_mul hM0]
    exact Real.sqrt_le_sqrt h2le
  have hprod := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity)
  refine hprod.trans (le_of_eq ?_)
  have hsq : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
  calc Real.sqrt M * Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
        * (Real.sqrt M * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖))
      = (Real.sqrt M * Real.sqrt M) * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖)) := by ring
    _ = M * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖)) := by rw [hsq]

/-- A mean square against a weight dominated by the Lorentzian kernel is integrable. -/
theorem integrable_normSq_mul_weight_of_le {g W : ℝ → ℂ} {C : ℝ}
    (hgm : AEStronglyMeasurable g volume) (hWm : AEStronglyMeasurable W volume)
    (hC : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hint : Integrable fun y : ℝ => ‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) :
    Integrable fun y : ℝ => ‖g y‖ ^ 2 * ‖W y‖ := by
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have h0 : (0 : ℝ) ≤ ‖W 0‖ := norm_nonneg _
    norm_num at h
    linarith
  have hbound : ∀ y : ℝ, ‖g y‖ ^ 2 * ‖W y‖ ≤ C * (‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by
    intro y
    have h := mul_le_mul_of_nonneg_left (hC y) (sq_nonneg ‖g y‖)
    calc ‖g y‖ ^ 2 * ‖W y‖ ≤ ‖g y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := h
      _ = C * (‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring
  refine Integrable.mono' (hint.const_mul C) (((hgm.norm).pow 2).mul hWm.norm) ?_
  filter_upwards with y
  have h0 : (0 : ℝ) ≤ ‖g y‖ ^ 2 * ‖W y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact hbound y

/-- **The mean square against a kernel with quadratic decay.**  A weight dominated by `C/(1+y²)` transfers
the mean square to the Lorentzian one at the cost of the constant. -/
theorem integral_normSq_mul_weight_le {g W : ℝ → ℂ} {C : ℝ}
    (hgm : AEStronglyMeasurable g volume) (hWm : AEStronglyMeasurable W volume)
    (hC : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hint : Integrable fun y : ℝ => ‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) :
    (∫ y : ℝ, ‖g y‖ ^ 2 * ‖W y‖) ≤ C * ∫ y : ℝ, ‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
  have hbound : ∀ y : ℝ, ‖g y‖ ^ 2 * ‖W y‖ ≤ C * (‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by
    intro y
    have h := mul_le_mul_of_nonneg_left (hC y) (sq_nonneg ‖g y‖)
    calc ‖g y‖ ^ 2 * ‖W y‖ ≤ ‖g y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := h
      _ = C * (‖g y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring
  have hmono := integral_mono (integrable_normSq_mul_weight_of_le hgm hWm hC hint)
    (hint.const_mul C) hbound
  rwa [integral_const_mul] at hmono

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- **The master inequality of a three-factor vertical integral.**  One factor bounded pointwise, a kernel
with quadratic decay, and two Lorentzian mean squares:

`‖∫ g₁ g₂ g₃ W‖ ≤ M·C·(∫ ‖g₁‖²/(1+y²))^{1/2}(∫ ‖g₂‖²/(1+y²))^{1/2}`,

for `‖g₃‖ ≤ M` and `‖W‖ ≤ C/(1+y²)`.  Nothing about Dirichlet series enters; the hypotheses are exactly
what a smoothed Perron kernel and an Euler product supply. -/
theorem norm_integral_mul_three_le_sup_mul_lorentz {g₁ g₂ g₃ W : ℝ → ℂ} {M C : ℝ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hm3 : AEStronglyMeasurable g₃ volume) (hmW : AEStronglyMeasurable W volume)
    (hM : ∀ y : ℝ, ‖g₃ y‖ ≤ M) (hC : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ 2)⁻¹)
    (h1 : Integrable fun y : ℝ => ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹)
    (h2 : Integrable fun y : ℝ => ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹) :
    ‖∫ y : ℝ, g₁ y * g₂ y * g₃ y * W y‖
      ≤ M * C * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have h0 : (0 : ℝ) ≤ ‖W 0‖ := norm_nonneg _
    norm_num at h
    linarith
  have h1' : Integrable fun y : ℝ => ‖g₁ y‖ ^ 2 * ‖W y‖ :=
    integrable_normSq_mul_weight_of_le hm1 hmW hC h1
  have h2' : Integrable fun y : ℝ => ‖g₂ y‖ ^ 2 * ‖W y‖ :=
    integrable_normSq_mul_weight_of_le hm2 hmW hC h2
  refine (norm_integral_mul_three_le_sup_mul_sqrt_mul_sqrt hm1 hm2 hm3 hmW hM h1' h2').trans ?_
  have hs1 : Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
      ≤ Real.sqrt C * Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by
    rw [← Real.sqrt_mul hC0]
    exact Real.sqrt_le_sqrt (integral_normSq_mul_weight_le hm1 hmW hC h1)
  have hs2 : Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖)
      ≤ Real.sqrt C * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by
    rw [← Real.sqrt_mul hC0]
    exact Real.sqrt_le_sqrt (integral_normSq_mul_weight_le hm2 hmW hC h2)
  have hprod := mul_le_mul hs1 hs2 (Real.sqrt_nonneg _) (by positivity)
  have hstep := mul_le_mul_of_nonneg_left hprod hM0
  refine hstep.trans (le_of_eq ?_)
  have hsq : Real.sqrt C * Real.sqrt C = C := Real.mul_self_sqrt hC0
  calc M * (Real.sqrt C * Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹)
        * (Real.sqrt C * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹)))
      = M * ((Real.sqrt C * Real.sqrt C) * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹))) := by ring
    _ = M * C * (Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * (1 + y ^ 2)⁻¹)
          * Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * (1 + y ^ 2)⁻¹)) := by rw [hsq]; ring

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- The weighted mean square of a sum is integrable when both parts are. -/
theorem integrable_normSq_add_mul_weight {g₁ g₂ W : ℝ → ℂ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hmW : AEStronglyMeasurable W volume)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    Integrable fun y => ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖ := by
  have hmaj : Integrable fun y : ℝ => 2 * (‖g₁ y‖ ^ 2 * ‖W y‖) + 2 * (‖g₂ y‖ ^ 2 * ‖W y‖) :=
    (h1.const_mul 2).add (h2.const_mul 2)
  refine Integrable.mono' hmaj (((hm1.add hm2).norm.pow 2).mul hmW.norm) ?_
  filter_upwards with y
  have htri : ‖g₁ y + g₂ y‖ ≤ ‖g₁ y‖ + ‖g₂ y‖ := norm_add_le _ _
  have hsq : ‖g₁ y + g₂ y‖ ^ 2 ≤ 2 * ‖g₁ y‖ ^ 2 + 2 * ‖g₂ y‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖g₁ y‖ - ‖g₂ y‖), norm_nonneg (g₁ y), norm_nonneg (g₂ y)]
  have h0 : (0 : ℝ) ≤ ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  calc ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖ ≤ (2 * ‖g₁ y‖ ^ 2 + 2 * ‖g₂ y‖ ^ 2) * ‖W y‖ :=
        mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
    _ = 2 * (‖g₁ y‖ ^ 2 * ‖W y‖) + 2 * (‖g₂ y‖ ^ 2 * ‖W y‖) := by ring

/-- **Minkowski's inequality for a weighted mean square.**  The quantity `(∫ ‖g‖²‖W‖)^{1/2}` is subadditive:

`(∫ ‖g₁+g₂‖²‖W‖)^{1/2} ≤ (∫ ‖g₁‖²‖W‖)^{1/2} + (∫ ‖g₂‖²‖W‖)^{1/2}`.

The cross term is handled by the weighted Cauchy–Schwarz inequality, so no `L²` space is constructed.  This
is what lets a Dirichlet polynomial be split into blocks and each block estimated with its own parameters. -/
theorem sqrt_integral_normSq_add_mul_weight_le {g₁ g₂ W : ℝ → ℂ}
    (hm1 : AEStronglyMeasurable g₁ volume) (hm2 : AEStronglyMeasurable g₂ volume)
    (hmW : AEStronglyMeasurable W volume)
    (h1 : Integrable fun y => ‖g₁ y‖ ^ 2 * ‖W y‖)
    (h2 : Integrable fun y => ‖g₂ y‖ ^ 2 * ‖W y‖) :
    Real.sqrt (∫ y : ℝ, ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖)
      ≤ Real.sqrt (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖)
          + Real.sqrt (∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖) := by
  set A₁ : ℝ := ∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖ with hA₁
  set A₂ : ℝ := ∫ y : ℝ, ‖g₂ y‖ ^ 2 * ‖W y‖ with hA₂
  have hA₁0 : 0 ≤ A₁ := by
    rw [hA₁]
    exact integral_nonneg fun y => by positivity
  have hA₂0 : 0 ≤ A₂ := by
    rw [hA₂]
    exact integral_nonneg fun y => by positivity
  have hcross := integral_mul_mul_weight_le_sqrt_mul_sqrt hm1 hm2 hmW h1 h2
  have hint := integrable_normSq_add_mul_weight hm1 hm2 hmW h1 h2
  have hcrossint : Integrable fun y : ℝ => ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ := by
    have hmaj : Integrable fun y : ℝ => (‖g₁ y‖ ^ 2 * ‖W y‖ + ‖g₂ y‖ ^ 2 * ‖W y‖) := h1.add h2
    refine Integrable.mono' hmaj (((hm1.norm).mul (hm2.norm)).mul hmW.norm) ?_
    filter_upwards with y
    have h0 : (0 : ℝ) ≤ ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have hab : ‖g₁ y‖ * ‖g₂ y‖ ≤ ‖g₁ y‖ ^ 2 + ‖g₂ y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖g₁ y‖ - ‖g₂ y‖)]
    calc ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖ ≤ (‖g₁ y‖ ^ 2 + ‖g₂ y‖ ^ 2) * ‖W y‖ :=
          mul_le_mul_of_nonneg_right hab (norm_nonneg _)
      _ = ‖g₁ y‖ ^ 2 * ‖W y‖ + ‖g₂ y‖ ^ 2 * ‖W y‖ := by ring
  have hexpand : (∫ y : ℝ, ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖)
      ≤ A₁ + 2 * (∫ y : ℝ, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + A₂ := by
    have hbound : ∀ y : ℝ, ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖
        ≤ ‖g₁ y‖ ^ 2 * ‖W y‖ + 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + ‖g₂ y‖ ^ 2 * ‖W y‖ := by
      intro y
      have htri : ‖g₁ y + g₂ y‖ ≤ ‖g₁ y‖ + ‖g₂ y‖ := norm_add_le _ _
      have hsq : ‖g₁ y + g₂ y‖ ^ 2 ≤ (‖g₁ y‖ + ‖g₂ y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      calc ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖ ≤ ((‖g₁ y‖ + ‖g₂ y‖) ^ 2) * ‖W y‖ :=
            mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
        _ = ‖g₁ y‖ ^ 2 * ‖W y‖ + 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + ‖g₂ y‖ ^ 2 * ‖W y‖ := by ring
    have hIntSum : Integrable fun y : ℝ => ‖g₁ y‖ ^ 2 * ‖W y‖
        + 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + ‖g₂ y‖ ^ 2 * ‖W y‖ :=
      (h1.add (hcrossint.const_mul 2)).add h2
    have hsplit : (∫ y : ℝ, ‖g₁ y‖ ^ 2 * ‖W y‖
          + 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + ‖g₂ y‖ ^ 2 * ‖W y‖)
        = A₁ + 2 * (∫ y : ℝ, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) + A₂ := by
      have hAB : Integrable fun y : ℝ => ‖g₁ y‖ ^ 2 * ‖W y‖
          + 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) := h1.add (hcrossint.const_mul 2)
      have hcm : Integrable fun y : ℝ => 2 * (‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) :=
        hcrossint.const_mul 2
      rw [integral_add hAB h2, integral_add h1 hcm, integral_const_mul, hA₁, hA₂]
    have hmono := integral_mono hint hIntSum hbound
    rw [hsplit] at hmono
    exact hmono
  have hfinal : (∫ y : ℝ, ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖)
      ≤ (Real.sqrt A₁ + Real.sqrt A₂) ^ 2 := by
    have hsq1 : Real.sqrt A₁ ^ 2 = A₁ := Real.sq_sqrt hA₁0
    have hsq2 : Real.sqrt A₂ ^ 2 = A₂ := Real.sq_sqrt hA₂0
    have hcross' : (∫ y : ℝ, ‖g₁ y‖ * ‖g₂ y‖ * ‖W y‖) ≤ Real.sqrt A₁ * Real.sqrt A₂ := by
      rw [hA₁, hA₂]
      exact hcross
    nlinarith [hexpand, hcross', hsq1, hsq2]
  calc Real.sqrt (∫ y : ℝ, ‖g₁ y + g₂ y‖ ^ 2 * ‖W y‖)
      ≤ Real.sqrt ((Real.sqrt A₁ + Real.sqrt A₂) ^ 2) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt A₁ + Real.sqrt A₂ := by
        rw [Real.sqrt_sq (by positivity)]

end GaloisForLFunctions.HTGeometry
end

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Finset

/-- The weighted mean square of a finite sum is integrable when each part's is. -/
theorem integrable_normSq_sum_mul_weight {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ) (W : ℝ → ℂ)
    (hm : ∀ i ∈ s, AEStronglyMeasurable (g i) volume) (hmW : AEStronglyMeasurable W volume)
    (h : ∀ i ∈ s, Integrable fun y => ‖g i y‖ ^ 2 * ‖W y‖) :
    Integrable fun y => ‖∑ i ∈ s, g i y‖ ^ 2 * ‖W y‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have hma : AEStronglyMeasurable (g a) volume := hm a (Finset.mem_insert_self a s)
      have hmsum : AEStronglyMeasurable (fun y : ℝ => ∑ i ∈ s, g i y) volume := by
        have h := Finset.aestronglyMeasurable_sum s fun i hi =>
          hm i (Finset.mem_insert_of_mem hi)
        have heq : (∑ i ∈ s, g i) = fun y : ℝ => ∑ i ∈ s, g i y := by
          funext y
          simp [Finset.sum_apply]
        rwa [heq] at h
      have hia : Integrable fun y : ℝ => ‖g a y‖ ^ 2 * ‖W y‖ :=
        h a (Finset.mem_insert_self a s)
      have hisum : Integrable fun y : ℝ => ‖∑ i ∈ s, g i y‖ ^ 2 * ‖W y‖ :=
        ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
          (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hcomb := integrable_normSq_add_mul_weight hma hmsum hmW hia hisum
      refine hcomb.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [Finset.sum_insert ha]

/-- **Minkowski's inequality for a finite sum.**  The weighted mean square is subadditive over any finite
decomposition, so a Dirichlet polynomial may be split into blocks and each block estimated on its own
terms. -/
theorem sqrt_integral_normSq_sum_mul_weight_le {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (W : ℝ → ℂ) (hm : ∀ i ∈ s, AEStronglyMeasurable (g i) volume)
    (hmW : AEStronglyMeasurable W volume)
    (h : ∀ i ∈ s, Integrable fun y => ‖g i y‖ ^ 2 * ‖W y‖) :
    Real.sqrt (∫ y : ℝ, ‖∑ i ∈ s, g i y‖ ^ 2 * ‖W y‖)
      ≤ ∑ i ∈ s, Real.sqrt (∫ y : ℝ, ‖g i y‖ ^ 2 * ‖W y‖) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      have hma : AEStronglyMeasurable (g a) volume := hm a (Finset.mem_insert_self a s)
      have hmsum : AEStronglyMeasurable (fun y : ℝ => ∑ i ∈ s, g i y) volume := by
        have h := Finset.aestronglyMeasurable_sum s fun i hi =>
          hm i (Finset.mem_insert_of_mem hi)
        have heq : (∑ i ∈ s, g i) = fun y : ℝ => ∑ i ∈ s, g i y := by
          funext y
          simp [Finset.sum_apply]
        rwa [heq] at h
      have hia : Integrable fun y : ℝ => ‖g a y‖ ^ 2 * ‖W y‖ :=
        h a (Finset.mem_insert_self a s)
      have hisum : Integrable fun y : ℝ => ‖∑ i ∈ s, g i y‖ ^ 2 * ‖W y‖ :=
        integrable_normSq_sum_mul_weight s g W
          (fun i hi => hm i (Finset.mem_insert_of_mem hi)) hmW
          (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hcongr : (∫ y : ℝ, ‖∑ i ∈ insert a s, g i y‖ ^ 2 * ‖W y‖)
          = ∫ y : ℝ, ‖g a y + ∑ i ∈ s, g i y‖ ^ 2 * ‖W y‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        dsimp only
        rw [Finset.sum_insert ha]
      rw [hcongr, Finset.sum_insert ha]
      refine le_trans (sqrt_integral_normSq_add_mul_weight_le hma hmsum hmW hia hisum) ?_
      have hrest := ih (fun i hi => hm i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
      linarith [hrest]

end GaloisForLFunctions.HTGeometry
end
