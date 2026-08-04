import GaloisForLFunctions.HTGeometry.KleinGordonChartC1

/-!
# Differentiating a synthesis in time, in general

The second-order coordinate calculus needs the time derivative of every first partial, so the
dominated-convergence step is packaged here once and for all: a family of densities differentiable in
time, whose derivative is dominated by the weight uniformly on each time interval, has a synthesis
differentiable in time, with the derivative taken under the integral.

The two instances used later are the density of the evolution, whose time derivative is the density
of the velocity, and any of its derived densities, where the derivation in time and the multiplication
by the frequency commute.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- **A dominated differentiable family of densities has a synthesis differentiable in time.** -/
theorem hasDerivAt_kgSynthesis_time {g g' : ℝ → E → ℂ}
    (hdim : (Module.finrank ℝ E : ℝ) < N)
    (hg : ∀ t : ℝ, AEStronglyMeasurable (g t) (volume : Measure E))
    (hg' : ∀ t : ℝ, AEStronglyMeasurable (g' t) (volume : Measure E))
    (hderiv : ∀ (t : ℝ) (ξ : E), HasDerivAt (fun r : ℝ => g r ξ) (g' t ξ) t)
    (hbound : ∀ T : ℝ, ∃ B : ℝ, ∀ t : ℝ, |t| ≤ T → ∀ ξ : E,
      ‖g' t ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B)
    (x : E) (t₀ : ℝ) (hint : Integrable (g t₀) (volume : Measure E)) :
    HasDerivAt (fun t : ℝ => kgSynthesis (g t) x) (kgSynthesis (g' t₀) x) t₀ := by
  obtain ⟨B, hB⟩ := hbound (|t₀| + 1)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (F := fun t ξ => kgChar x ξ * g t ξ)
    (F' := fun t ξ => kgChar x ξ * g' t ξ)
    (bound := fun ξ : E => (kgFreq ξ ^ N)⁻¹ * B) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t =>
      ((continuous_kgChar' x).aestronglyMeasurable).mul (hg t))
    (hint.bdd_mul (c := 1) ((continuous_kgChar' x).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => le_of_eq (norm_kgChar x ξ)))
    (((continuous_kgChar' x).aestronglyMeasurable).mul (hg' t₀))
    ?_ ((integrable_kgFreq_inv_pow (E := E) hdim).mul_const B) ?_
  · exact hmain.2
  · filter_upwards with ξ
    intro t ht
    rw [norm_mul, norm_kgChar, one_mul]
    exact hB t (abs_le_of_mem_ball ht) ξ
  · filter_upwards with ξ
    intro t _
    exact (hderiv t ξ).const_mul (kgChar x ξ)

end GaloisForLFunctions.HTGeometry
