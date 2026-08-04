import GaloisForLFunctions.HTGeometry.HillFieldEquation

/-!
# The field equation as a statement about derivatives

The previous file proved the equation between the *integrals* representing the two sides. Here it is
read back through the differentiation theorems: the field is twice differentiable in time, and its
second derivative is `(2π)⁻²c(t)²` times the sum of the second spatial directional derivatives minus
the mass term.

Nothing analytic is added — the derivatives were already identified with those integrals — but the
statement is now about the field itself, which is what a probe interface consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

open scoped RealInnerProductSpace

section TimeEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
variable {m K C b : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

theorem hillSynthesis_kgChar (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (x : E) :
    hillSynthesis m c G₀ (kgChar x) (volume : Measure E) =
      fun r => hillEvolutionField m c G₀ r x := rfl

/-- **The field is differentiable in time.** -/
theorem hasDerivAt_hillEvolutionField_time (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (x : E) {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (fun r => hillEvolutionField m c G₀ r x)
      (hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) t) t := by
  have hmain := hasDerivAt_hillSynthesis (b := b) hm hc hcd hcpos hK hC hG
    ((continuous_kgChar' x).aestronglyMeasurable) (fun ξ => le_of_eq (norm_kgChar x ξ))
    hint hweight ht0 htb
  rwa [hillSynthesis_kgChar] at hmain

/-- **The second time derivative of the field is the spatial operator applied to it.** -/
theorem hasDerivAt_deriv_hillEvolutionField_time {cmin : ℝ} (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (hweight2 : Integrable (fun ξ : E => (m ^ 2 + C ^ 2 * ‖ξ‖ ^ 2) * ‖G₀ ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ 2 * ‖G₀ ξ‖) (volume : Measure E))
    (bas : OrthonormalBasis ι ℝ E) (x : E) {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (fun r => deriv (fun q => hillEvolutionField m c G₀ q x) r)
      (((c t ^ 2 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, bas i⟫ : ℝ) : ℂ)) ^ 2 * kgChar x ξ *
            hillDensity m c G₀ t ξ)) -
        ((m ^ 2 : ℝ) : ℂ) * hillEvolutionField m c G₀ t x) t := by
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) b,
      deriv (fun q => hillEvolutionField m c G₀ q x) r
        = hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) r := by
    intro r hr
    exact (hasDerivAt_hillEvolutionField_time (b := b) hm hc hcd hcpos hK hC hG hint hweight x
      hr.1 hr.2).deriv
  have hsecond := hasDerivAt_hillSynthesisDeriv (b := b) hm hc hcd hcpos hK hC hcmin hclow hG
    ((continuous_kgChar' x).aestronglyMeasurable) (fun ξ => le_of_eq (norm_kgChar x ξ))
    hweight hweight2 ht0 htb
  rw [hillSynthesisSecond_eq hm hc hcd hcpos hK hC hG hint h2 bas (le_of_lt ht0) x] at hsecond
  refine hsecond.congr_of_eventuallyEq ?_
  have hIoo : Ioo (0 : ℝ) b ∈ nhds t := Ioo_mem_nhds ht0 htb
  filter_upwards [hIoo] with r hr
  exact hderiv r hr

end TimeEquation

end GaloisForLFunctions.HTGeometry
