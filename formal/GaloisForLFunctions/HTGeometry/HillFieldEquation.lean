import GaloisForLFunctions.HTGeometry.HillFieldSpace
import GaloisForLFunctions.HTGeometry.WienerSynthesisLaplacian

/-!
# The field equation of a time-dependent speed

The two halves of the construction meet on one multiplier. On the temporal side the fibre satisfies
`û'' = -(m² + c(t)²‖ξ‖²)û`; on the spatial side the sum of the second directional derivatives over an
orthonormal basis carries the factor `-4π²‖ξ‖²`. Dividing the latter by `(2π)²` and multiplying by
`c(t)²` produces exactly the spatial part of the former, and what is left over is the mass.

So the synthesis of the second-derivative density is the synthesis of `(2π)⁻²c(t)²Δ - m²` applied to
the field: the field equation, at the level of the integrals that represent both sides.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped RealInnerProductSpace

section FieldEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
variable {m K C : ℝ} {c dc : ℝ → ℝ} {G₀ : E → ℂ}

/-! ## The symbol identity -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The multiplier of the second time derivative is the spatial multiplier plus the mass.** -/
theorem hillDensitySecond_symbol (hm : 0 < m) (t : ℝ) (ξ : E) :
    hillDensitySecond m c G₀ t ξ =
      ((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * hillDensity m c G₀ t ξ) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * hillDensity m c G₀ t ξ := by
  have hpi : (2 * Real.pi) ^ (2 : ℕ) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hfreq : massiveFreq m c ‖ξ‖ t ^ (2 : ℕ) = m ^ (2 : ℕ) + (c t * ‖ξ‖) ^ (2 : ℕ) := massiveFreq_sq hm c ‖ξ‖ t
  have hscalar : (-(massiveFreq m c ‖ξ‖ t ^ (2 : ℕ)) : ℝ)
      = c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) * (-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ)) - m ^ (2 : ℕ) := by
    rw [hfreq]
    field_simp
    ring
  rw [hillDensitySecond, hillDensity]
  push_cast [hscalar]
  ring

/-! ## The equation -/

/-- **The field equation of the evolution**, at the level of the integrals representing both sides:
the synthesis of the second-derivative density is `(2π)⁻²c(t)²` times the sum of the second spatial
directional derivatives, minus the mass term. -/
theorem hillSynthesisSecond_eq (hm : 0 < m) (hc : Continuous c)
    (hcd : ∀ r, HasDerivAt c (dc r) r) (hcpos : ∀ r, 0 < c r) (hK : ∀ r, |dc r| ≤ K * c r)
    (hC : ∀ r, c r ^ (2 : ℕ) ≤ C ^ (2 : ℕ)) (hG : Continuous G₀)
    (hint : Integrable (fun ξ : E => ‖G₀ ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖G₀ ξ‖) (volume : Measure E))
    (b : OrthonormalBasis ι ℝ E) {t : ℝ} (ht : 0 ≤ t) (x : E) :
    hillSynthesisSecond m c G₀ (kgChar x) (volume : Measure E) t =
      ((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, b i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ *
            hillDensity m c G₀ t ξ)) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * hillEvolutionField m c G₀ t x := by
  have hmeas := aestronglyMeasurable_hillDensity hm hc hC hG ht (volume : Measure E)
  have hdint : Integrable (hillDensity m c G₀ t) (volume : Measure E) :=
    integrable_of_hillDensity_bound hm hc hcd hcpos hK hC hG hint ht
  have hmw2 : AEStronglyMeasurable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    ((continuous_kgFreq.pow 2).aestronglyMeasurable).mul hmeas.norm
  have hw2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖hillDensity m c G₀ t ξ‖)
      (volume : Measure E) :=
    integrable_weight_mul_hillDensity (fun ξ => sq_nonneg _) hmw2 hm hc hcd hcpos hK hC h2 ht
  have hlap := sum_integral_dirSq hmeas hw2 b x
  have hintLap : Integrable (fun ξ : E =>
      ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ)
      (volume : Measure E) := by
    have hmeasF : AEStronglyMeasurable (fun ξ : E =>
        ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ)
        (volume : Measure E) :=
      (((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_norm.pow 2))).mul
          (continuous_kgChar' x)).aestronglyMeasurable).mul hmeas
    refine Integrable.mono' (hw2.const_mul (4 * Real.pi ^ (2 : ℕ))) hmeasF ?_
    filter_upwards with ξ
    have hchar : ‖kgChar x ξ‖ = 1 := norm_kgChar x ξ
    have hnormle : ‖ξ‖ ^ (2 : ℕ) ≤ kgFreq ξ ^ (2 : ℕ) := by
      rw [kgFreq_sq]
      linarith
    have hDnn : (0 : ℝ) ≤ ‖hillDensity m c G₀ t ξ‖ := norm_nonneg _
    have hpi : (0 : ℝ) ≤ 4 * Real.pi ^ (2 : ℕ) := by positivity
    calc ‖((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ‖
        = (4 * Real.pi ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖hillDensity m c G₀ t ξ‖ := by
          rw [norm_mul, norm_mul, hchar, Complex.norm_real, Real.norm_eq_abs, mul_one]
          rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])]
          ring
      _ ≤ (4 * Real.pi ^ (2 : ℕ) * kgFreq ξ ^ (2 : ℕ)) * ‖hillDensity m c G₀ t ξ‖ := by
          have := mul_le_mul_of_nonneg_left hnormle hpi
          exact mul_le_mul_of_nonneg_right this hDnn
      _ = 4 * Real.pi ^ (2 : ℕ) * (kgFreq ξ ^ (2 : ℕ) * ‖hillDensity m c G₀ t ξ‖) := by ring
  have hintMass : Integrable (fun ξ : E => kgChar x ξ * hillDensity m c G₀ t ξ)
      (volume : Measure E) := by
    refine Integrable.mono' hdint.norm
      (((continuous_kgChar' x).aestronglyMeasurable).mul hmeas) ?_
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul]
  rw [hillSynthesisSecond, hillEvolutionField, kgSynthesis, hlap]
  have hsplit : ∀ ξ : E, kgChar x ξ * hillDensitySecond m c G₀ t ξ
      = ((c t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * hillDensity m c G₀ t ξ) -
        ((m ^ (2 : ℕ) : ℝ) : ℂ) * (kgChar x ξ * hillDensity m c G₀ t ξ) := by
    intro ξ
    rw [hillDensitySecond_symbol hm t ξ]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit)]
  rw [integral_sub ((hintLap.const_mul _)) ((hintMass.const_mul _)), integral_const_mul,
    integral_const_mul]

end FieldEquation

end GaloisForLFunctions.HTGeometry
