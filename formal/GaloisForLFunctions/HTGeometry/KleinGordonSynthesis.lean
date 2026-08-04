import GaloisForLFunctions.HTGeometry.KleinGordonSymbolEvolution
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Fourier synthesis of the Klein–Gordon propagator solves the equation

The propagator symbols satisfy the oscillator equation frequency by frequency. To turn that into a
statement about a function on spacetime one has to differentiate under the frequency integral, and
that is the content of this file.

The differentiation is dominated convergence: the `k`-th time derivative of the symbol costs a factor
`⟨ξ⟩^k`, so the hypothesis is exactly that `⟨ξ⟩^k` times the density is integrable — which every
Schwartz density satisfies for every `k`.

The conclusion is that the synthesis

`u(t) = ∫ cos(t⟨ξ⟩) h(ξ) dξ`

satisfies `∂ₜ²u = -∫ ⟨ξ⟩² cos(t⟨ξ⟩) h(ξ) dξ`, which is the Klein–Gordon equation with the Laplacian
read on the frequency side.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

/-! ## Differentiating a symbol integral in the parameter -/

section Parametric

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Differentiation under a symbol integral.** If the symbol is differentiable in the parameter
with derivative dominated by `g`, and `g` times the density is integrable, then the integral is
differentiable with the expected derivative. -/
theorem hasDerivAt_integral_symbol {m m' : ℝ → α → ℂ} {h : α → ℂ} {g : α → ℝ} (t₀ : ℝ)
    (hm_meas : ∀ t : ℝ, AEStronglyMeasurable (fun a => m t a * h a) μ)
    (hm_int : Integrable (fun a => m t₀ a * h a) μ)
    (hm'_meas : AEStronglyMeasurable (fun a => m' t₀ a * h a) μ)
    (hderiv : ∀ (t : ℝ) (a : α), HasDerivAt (fun r : ℝ => m r a) (m' t a) t)
    (hbound : ∀ (t : ℝ) (a : α), ‖m' t a‖ ≤ g a)
    (hg : Integrable (fun a => g a * ‖h a‖) μ) :
    HasDerivAt (fun t : ℝ => ∫ a, m t a * h a ∂μ) (∫ a, m' t₀ a * h a ∂μ) t₀ := by
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t₀)
    (F := fun t a => m t a * h a) (F' := fun t a => m' t a * h a)
    (bound := fun a => g a * ‖h a‖) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hm_meas) hm_int hm'_meas ?_ hg ?_
  · exact hmain.2
  · filter_upwards with a
    intro t _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound t a) (norm_nonneg _)
  · filter_upwards with a
    intro t _
    exact (hderiv t a).mul_const (h a)

end Parametric

/-! ## The Klein–Gordon synthesis -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E}

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem continuous_kgFreq : Continuous (kgFreq (E := E)) := by
  refine Real.continuous_sqrt.comp ?_
  exact continuous_const.add (continuous_norm.pow 2)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem continuous_kgCosSymbol_freq (t : ℝ) : Continuous (kgCosSymbol (E := E) t) := by
  refine Complex.continuous_ofReal.comp ?_
  exact Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq)

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem continuous_kgSinDeriv (t : ℝ) :
    Continuous fun ξ : E => ((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  exact (continuous_kgFreq.mul
    (Real.continuous_sin.comp (continuous_const.mul continuous_kgFreq))).neg

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] in
theorem continuous_kgCosSecond (t : ℝ) :
    Continuous fun ξ : E => ((-(kgFreq ξ ^ 2) * Real.cos (t * kgFreq ξ) : ℝ) : ℂ) := by
  refine Complex.continuous_ofReal.comp ?_
  exact (continuous_kgFreq.pow 2).neg.mul
    (Real.continuous_cos.comp (continuous_const.mul continuous_kgFreq))

omit [InnerProductSpace ℝ E] in
/-- **The first time derivative of the Klein–Gordon synthesis.** -/
theorem hasDerivAt_kgSynthesis {h : E → ℂ} (t : ℝ)
    (hmeas : AEStronglyMeasurable h μ)
    (hint : Integrable (fun ξ => kgCosSymbol t ξ * h ξ) μ)
    (hg : Integrable (fun ξ => kgFreq ξ * ‖h ξ‖) μ) :
    HasDerivAt (fun r : ℝ => ∫ ξ, kgCosSymbol r ξ * h ξ ∂μ)
      (∫ ξ, ((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ) * h ξ ∂μ) t := by
  refine hasDerivAt_integral_symbol (g := fun ξ => kgFreq ξ) t
    (fun r => ((continuous_kgCosSymbol_freq r).aestronglyMeasurable).mul hmeas) hint
    (((continuous_kgSinDeriv t).aestronglyMeasurable).mul hmeas)
    (fun r ξ => hasDerivAt_kgCosSymbol ξ r) (fun r ξ => ?_) hg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_of_pos (kgFreq_pos ξ)]
  have hsin : |Real.sin (r * kgFreq ξ)| ≤ 1 := Real.abs_sin_le_one _
  nlinarith [kgFreq_pos ξ, abs_nonneg (Real.sin (r * kgFreq ξ))]

omit [InnerProductSpace ℝ E] in
/-- **The second time derivative of the Klein–Gordon synthesis**: the synthesis solves the
Klein–Gordon equation, with the mass-shifted Laplacian read on the frequency side. -/
theorem hasDerivAt_deriv_kgSynthesis {h : E → ℂ} (t : ℝ)
    (hmeas : AEStronglyMeasurable h μ)
    (hint : Integrable (fun ξ => ((-(kgFreq ξ * Real.sin (t * kgFreq ξ)) : ℝ) : ℂ) * h ξ) μ)
    (hg : Integrable (fun ξ => kgFreq ξ ^ 2 * ‖h ξ‖) μ) :
    HasDerivAt (fun r : ℝ => ∫ ξ, ((-(kgFreq ξ * Real.sin (r * kgFreq ξ)) : ℝ) : ℂ) * h ξ ∂μ)
      (∫ ξ, ((-(kgFreq ξ ^ 2) * Real.cos (t * kgFreq ξ) : ℝ) : ℂ) * h ξ ∂μ) t := by
  refine hasDerivAt_integral_symbol (g := fun ξ => kgFreq ξ ^ 2) t
    (fun r => ((continuous_kgSinDeriv r).aestronglyMeasurable).mul hmeas) hint
    (((continuous_kgCosSecond t).aestronglyMeasurable).mul hmeas)
    (fun r ξ => hasDerivAt_deriv_cosFreq ξ r |>.ofReal_comp) (fun r ξ => ?_) hg
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_pos (pow_pos (kgFreq_pos ξ) 2)]
  have hcos : |Real.cos (r * kgFreq ξ)| ≤ 1 := Real.abs_cos_le_one _
  nlinarith [pow_pos (kgFreq_pos ξ) 2, abs_nonneg (Real.cos (r * kgFreq ξ))]

end GaloisForLFunctions.HTGeometry
