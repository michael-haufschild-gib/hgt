import GaloisForLFunctions.HTGeometry.HillSynthesisField
import GaloisForLFunctions.HTGeometry.WienerSynthesisSpace

/-!
# The spatial derivatives of the time-dependent-speed field

The field is the synthesis of the frequency density against the character, so its derivatives in the
space variable are those of the character: each one costs a factor `2πi⟪ξ,v⟫`, bounded by the
frequency. The corpus's synthesis layer proves this for an arbitrary density, so nothing about the
evolution has to be repeated here; what this file supplies is the weighted integrability of the Hill
density, which is where the estimates of the previous files enter.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section FieldSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-- The field of the evolution: the synthesis of the frequency density. -/
noncomputable def hillEvolutionField (m : ℝ) (c : ℝ → ℝ) (G₀ : E → ℂ) (t : ℝ) (x : E) : ℂ :=
  kgSynthesis (hillDensity m c G₀ t) x

/-! ## Weighted integrability of the density -/

/-- The density inherits every weighted integrability of the datum, with a constant that does not
depend on the frequency. -/
theorem integrable_weight_mul_hillDensity {t : ℝ} {w : E → ℝ} (hw : ∀ ξ, 0 ≤ w ξ)
    (hmw : AEStronglyMeasurable (fun ξ : E => w ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E))
    (hm : 0 < m) (hc : Continuous c) (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r)
    (hK : ∀ r, |dc r| ≤ K * c r) (hC : ∀ r, c r ^ 2 ≤ C ^ 2)
    (hint : Integrable (fun ξ : E => w ξ * ‖G₀ ξ‖) (volume : Measure E))
    (ht : 0 ≤ t) :
    Integrable (fun ξ : E => w ξ * ‖hillDensity m c G₀ t ξ‖) (volume : Measure E) := by
  refine Integrable.mono' (hint.const_mul (max 1 (c 0 / c t) * Real.exp (K * t))) hmw ?_
  filter_upwards with ξ
  have hbase := norm_hillDensity_le (G₀ := G₀) hm hc hcd hcpos hK hC ht ξ
  have hwξ := hw ξ
  have hnorm : ‖w ξ * ‖hillDensity m c G₀ t ξ‖‖ = w ξ * ‖hillDensity m c G₀ t ξ‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwξ (norm_nonneg _))]
  rw [hnorm]
  calc w ξ * ‖hillDensity m c G₀ t ξ‖
      ≤ w ξ * ((max 1 (c 0 / c t) * Real.exp (K * t)) * ‖G₀ ξ‖) :=
        mul_le_mul_of_nonneg_left hbase hwξ
    _ = (max 1 (c 0 / c t) * Real.exp (K * t)) * (w ξ * ‖G₀ ξ‖) := by ring

/-! ## The spatial derivatives -/

/-- **The first spatial derivative of the field.** -/
theorem hasDerivAt_hillEvolutionField_dir (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => hillEvolutionField m c G₀ t (x + s • v))
      (∫ ξ, 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + r • v) ξ *
        hillDensity m c G₀ t ξ) r := by
  have hmeas := aestronglyMeasurable_hillDensity hm hc hC hG ht (volume : Measure E)
  have hdint : Integrable (hillDensity m c G₀ t) (volume : Measure E) :=
    integrable_of_hillDensity_bound hm hc hcd hcpos hK hC hG hint ht
  have hmw : AEStronglyMeasurable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    (continuous_kgFreq.aestronglyMeasurable).mul hmeas.norm
  have hw1 : Integrable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    integrable_weight_mul_hillDensity (fun ξ => le_of_lt (kgFreq_pos ξ)) hmw hm hc hcd hcpos hK hC
      h1 ht
  exact hasDerivAt_kgSynthesis_dir hmeas hdint hw1 x v r

/-- **The second spatial derivative of the field.** -/
theorem hasDerivAt_deriv_hillEvolutionField_dir (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ 2 ≤ C ^ 2) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖G₀ ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ 2 * ‖G₀ ξ‖) (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => deriv (fun q : ℝ => hillEvolutionField m c G₀ t (x + q • v)) s)
      (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ)) ^ 2 * kgChar (x + r • v) ξ *
        hillDensity m c G₀ t ξ) r := by
  have hmeas := aestronglyMeasurable_hillDensity hm hc hC hG ht (volume : Measure E)
  have hdint : Integrable (hillDensity m c G₀ t) (volume : Measure E) :=
    integrable_of_hillDensity_bound hm hc hcd hcpos hK hC hG hint ht
  have hmw1 : AEStronglyMeasurable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    (continuous_kgFreq.aestronglyMeasurable).mul hmeas.norm
  have hmw2 : AEStronglyMeasurable (fun ξ : E => kgFreq ξ ^ 2 * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    ((continuous_kgFreq.pow 2).aestronglyMeasurable).mul hmeas.norm
  have hw1 : Integrable (fun ξ : E => kgFreq ξ * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    integrable_weight_mul_hillDensity (fun ξ => le_of_lt (kgFreq_pos ξ)) hmw1 hm hc hcd hcpos hK hC
      h1 ht
  have hw2 : Integrable (fun ξ : E => kgFreq ξ ^ 2 * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    integrable_weight_mul_hillDensity (fun ξ => sq_nonneg _) hmw2 hm hc hcd hcpos hK hC h2 ht
  exact hasDerivAt_deriv_kgSynthesis_dir hmeas hdint hw1 hw2 x v r

end FieldSpace

end GaloisForLFunctions.HTGeometry
