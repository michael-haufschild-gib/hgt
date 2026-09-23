import GaloisForLFunctions.HTGeometry.HillFieldContinuity
import GaloisForLFunctions.HTGeometry.HillFieldTimeEquation

/-!
# The real field of the evolution

A clock probe is a real field. Taking the real part of the synthesis costs nothing analytically: the
real part is a continuous linear map, so it commutes with every derivative taken so far, and the
multipliers of the field equation are real, so the equation is inherited.

What the chart layer will consume is exactly this: a real field, twice differentiable in time,
satisfying the equation, and nonvanishing near a prescribed event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section RealField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
variable {m K C cmin b : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- The real field of the evolution. -/
noncomputable def hillRealField (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (t : ℝ) (x : E) : ℝ :=
  (hillEvolutionField m c G₀ t x).re

/-- **The real field is differentiable in time.** -/
theorem hasDerivAt_hillRealField_time (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (x : E) {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (fun r => hillRealField m c G₀ r x)
      ((hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) t).re) t := by
  have hbase := hasDerivAt_hillEvolutionField_time (b := b) hm hc hcd hcpos hK hC hG hint hweight
    x ht0 htb
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hbase

/-- **The second time derivative of the real field is the real part of the equation.** -/
theorem hasDerivAt_deriv_hillRealField_time (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (hweight : Integrable (fun ξ : E => (m + c 0 * ‖ξ‖) * ‖G₀ ξ‖) (volume : Measure E))
    (hweight2 : Integrable (fun ξ : E => (m ^ (2 : ℕ) + C ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖G₀ ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) (volume : Measure E))
    (bas : OrthonormalBasis ι ℝ E) (x : E) {t : ℝ} (ht0 : 0 < t) (htb : t < b) :
    HasDerivAt (fun r => (hillSynthesisDeriv m c G₀ (kgChar x) (volume : Measure E) r).re)
      ((((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, bas i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ *
            hillDensity m c G₀ t ξ)) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * hillEvolutionField m c G₀ t x).re) t := by
  have hbase := hasDerivAt_hillSynthesisDeriv (b := b) hm hc hcd hcpos hK hC hcmin hclow hG
    ((continuous_kgChar' x).aestronglyMeasurable) (fun ξ => le_of_eq (norm_kgChar x ξ))
    hweight hweight2 ht0 htb
  rw [hillSynthesisSecond_eq hm hc hcd hcpos hK hC hG hint h2 bas (le_of_lt ht0) x] at hbase
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hbase

/-- **The real field does not vanish near an event whose datum has a nonvanishing real
synthesis.** -/
theorem eventually_hillRealField_ne_zero (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hcmin : 0 < cmin) (hclow : ∀ r, cmin ≤ c r)
    (hG : Continuous G₀) (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    {x₀ : E} (hne : (kgSynthesis G₀ x₀).re ≠ 0) :
    ∀ᶠ p : ℝ × E in nhds ((0 : ℝ), x₀), hillRealField m c G₀ p.1 p.2 ≠ 0 := by
  have hcontAt := continuousAt_hillEvolutionField hm hc hcd hcpos hK hC hcmin hclow hG hint 0 x₀
  have hreal : ContinuousAt (fun p : ℝ × E => hillRealField m c G₀ p.1 p.2) (0, x₀) :=
    Complex.continuous_re.continuousAt.comp hcontAt
  have hval : hillRealField m c G₀ 0 x₀ ≠ 0 := by
    rw [hillRealField, hillEvolutionField_zero (C := C) hm hc hC x₀]
    exact hne
  exact hreal.eventually_ne hval

end RealField

end GaloisForLFunctions.HTGeometry
