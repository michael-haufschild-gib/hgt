import GaloisForLFunctions.HTGeometry.HillDrivenField
import GaloisForLFunctions.HTGeometry.KleinGordonPotentialWave

/-!
# The wave equation of the driven evolution

The second time derivative of the field is the synthesis of the equation of the fibres. Its first
term carries the multiplier `-ω(t,ξ)² = -(m² + c(t)²‖ξ‖²)`, which is exactly the speed squared times
the spatial multiplier minus the mass; its second is the convolution, which the synthesis turns back
into multiplication by the potential.

So the field solves

`∂ₜ²u = (2π)⁻²c(t)²Δu - m²u + V u`,

with `V` the inverse transform of the convolving density — an arbitrary smooth potential, once the
density is chosen to realize it.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace

section Wave

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι] {N : ℕ}

/-- The second-derivative density splits into the frequency multiplier and the source. -/
theorem hillDrivenDensitySecond_eq (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) (ξ : E) :
    hillDrivenDensitySecond a b G₀ t ξ
      = -(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ +
        ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t := by
  rw [hillDrivenDensitySecond, hillDrivenDensity, kgWeighted]
  ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The frequency multiplier of a fibre is the spatial multiplier of the speed, minus the
mass.** -/
theorem hillFreq_symbol (a : HillSpeed) (t : ℝ) (ξ : E) (z : ℂ) :
    -(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * z =
      ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * z) - ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * z := by
  have hpi : (2 * Real.pi) ^ (2 : ℕ) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hfreq : a.freq ξ t ^ (2 : ℕ) = a.mass ^ (2 : ℕ) + (a.speed t * ‖ξ‖) ^ (2 : ℕ) :=
    massiveFreq_sq a.mass_pos a.speed ‖ξ‖ t
  have hscalar : (-(a.freq ξ t ^ (2 : ℕ)) : ℝ)
      = a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) * (-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ)) - a.mass ^ (2 : ℕ) := by
    rw [hfreq]
    field_simp
    ring
  have hC : -(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ))
      = ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) * ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ)
        - ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, hscalar]
    push_cast
    ring
  rw [hC]
  ring

/-- **The synthesis of the frequency part of the equation** is the spatial Laplacian term minus the
mass term. -/
theorem integral_kgChar_mul_freq_sq (a : HillSpeed) {f : E → ℂ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hint : Integrable f (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E))
    (bas : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    (∫ ξ, kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * f ξ))
      = ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, bas i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ * f ξ)) -
        ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * ∫ ξ, kgChar x ξ * f ξ := by
  have hlap := sum_integral_dirSq hmeas h2 bas x
  have hintLap : Integrable (fun ξ : E =>
      ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ) (volume : Measure E) := by
    have hmeasF : AEStronglyMeasurable (fun ξ : E =>
        ((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ) (volume : Measure E) :=
      (((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_norm.pow 2))).mul
          (continuous_kgChar' x)).aestronglyMeasurable).mul hmeas
    refine Integrable.mono' (h2.const_mul (4 * Real.pi ^ (2 : ℕ))) hmeasF ?_
    filter_upwards with ξ
    have hnormle : ‖ξ‖ ^ (2 : ℕ) ≤ kgFreq ξ ^ (2 : ℕ) := by
      rw [kgFreq_sq]
      linarith
    have hpi : (0 : ℝ) ≤ 4 * Real.pi ^ (2 : ℕ) := by positivity
    calc ‖((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ‖
        = (4 * Real.pi ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ)) * ‖f ξ‖ := by
          rw [norm_mul, norm_mul, norm_kgChar, Complex.norm_real, Real.norm_eq_abs, mul_one]
          rw [abs_of_nonpos (by nlinarith [sq_nonneg ‖ξ‖])]
          ring
      _ ≤ (4 * Real.pi ^ (2 : ℕ) * kgFreq ξ ^ (2 : ℕ)) * ‖f ξ‖ := by
          have := mul_le_mul_of_nonneg_left hnormle hpi
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = 4 * Real.pi ^ (2 : ℕ) * (kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) := by ring
  have hintChar : Integrable (fun ξ : E => kgChar x ξ * f ξ) (volume : Measure E) := by
    refine Integrable.mono' hint.norm (((continuous_kgChar' x).aestronglyMeasurable).mul hmeas) ?_
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul]
  rw [hlap]
  have hsplit : ∀ ξ : E, kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * f ξ)
      = ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ) -
        ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * (kgChar x ξ * f ξ) := by
    intro ξ
    have h := hillFreq_symbol a t ξ (f ξ)
    calc kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * f ξ)
        = kgChar x ξ * (((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
            (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * f ξ) -
          ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * f ξ) := by rw [h]
      _ = ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
            (((-(4 * Real.pi ^ (2 : ℕ)) * ‖ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * kgChar x ξ * f ξ) -
          ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * (kgChar x ξ * f ξ) := by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_sub (hintLap.const_mul _) (hintChar.const_mul _), integral_const_mul,
    integral_const_mul]

/-! ## The potential term -/

/-- The source, weighted, is the weighted convolution. -/
theorem weighted_hillFlowSource_eq (a : HillSpeed) (b : WienerFamily E N) (G₀ : E →ᵇ ℂ)
    (t : ℝ) (ξ : E) :
    ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t
      = kgWeighted N (kgConvBCF (b.density t) (hillPotentialFlow a b G₀ t)) ξ := by
  rw [kgWeighted, kgConvBCF_apply]
  rfl

/-- **The synthesis of the source is the potential times the field.** -/
theorem integral_kgChar_mul_weighted_source (hN : (Module.finrank ℝ E : ℝ) < N) (a : HillSpeed)
    (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (t : ℝ) (x : E) :
    (∫ ξ, kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t))
      = kgPotential (b.density t) x * hillDrivenField a b G₀ t x := by
  have ha_int : Integrable (fun η : E => b.density t η) (volume : Measure E) := by
    refine Integrable.mono' (b.density t).integrable_weight
      (b.density t).aestronglyMeasurable ?_
    filter_upwards with η
    have h1 : (1 : ℝ) ≤ kgFreq η ^ N := one_le_pow₀ (one_le_kgFreq η)
    nlinarith [norm_nonneg (b.density t η)]
  have hint : Integrable (hillDrivenDensity a b G₀ t) (volume : Measure E) :=
    integrable_kgWeighted (E := E) hN (hillPotentialFlow a b G₀ t)
  have hrw : (∫ ξ, kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t))
      = ∫ ξ, kgChar x ξ * ∫ η, b.density t η * hillDrivenDensity a b G₀ t (ξ - η) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t)
      = kgChar x ξ * ∫ η, b.density t η * hillDrivenDensity a b G₀ t (ξ - η)
    rw [weighted_hillFlowSource_eq a b G₀ t ξ, kgWeighted_kgConvBCF]
    rfl
  rw [hrw, integral_kgChar_mul_convolution ha_int hint x]
  rfl

/-! ## The equation -/

/-- **The field of the driven evolution solves the wave equation of its speed, with the
potential.** -/
theorem hillDrivenField_wave_equation (hN : (Module.finrank ℝ E : ℝ) + 2 < N) (a : HillSpeed)
    (b : WienerFamily E N) (G₀ : E →ᵇ ℂ) (bas : OrthonormalBasis ι ℝ E) (t : ℝ) (x : E) :
    deriv (deriv fun r : ℝ => hillDrivenField a b G₀ r x) t
      = ((a.speed t ^ (2 : ℕ) / (2 * Real.pi) ^ (2 : ℕ) : ℝ) : ℂ) *
          (∑ i, (∫ ξ, (2 * Real.pi * Complex.I * ((⟪ξ, bas i⟫ : ℝ) : ℂ)) ^ (2 : ℕ) * kgChar x ξ *
            hillDrivenDensity a b G₀ t ξ)) -
        ((a.mass ^ (2 : ℕ) : ℝ) : ℂ) * hillDrivenField a b G₀ t x +
        kgPotential (b.density t) x * hillDrivenField a b G₀ t x := by
  have hdim : (Module.finrank ℝ E : ℝ) < N := by linarith
  have hmeas : AEStronglyMeasurable (hillDrivenDensity a b G₀ t) (volume : Measure E) :=
    (continuous_hillDrivenDensity a b G₀ t).aestronglyMeasurable
  have hint : Integrable (hillDrivenDensity a b G₀ t) (volume : Measure E) :=
    integrable_kgWeighted (E := E) hdim (hillPotentialFlow a b G₀ t)
  have h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖hillDrivenDensity a b G₀ t ξ‖)
      (volume : Measure E) := by
    have hjN : (Module.finrank ℝ E : ℝ) + (2 : ℕ) < N := by push_cast; linarith
    exact integrable_kgFreq_pow_mul_kgWeighted' (E := E) (j := 2) hjN
      (hillPotentialFlow a b G₀ t)
  have hL : deriv (deriv fun r : ℝ => hillDrivenField a b G₀ r x) t
      = ∫ ξ, kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ :=
    (hasDerivAt_deriv_hillDrivenField hN a b G₀ x t).deriv
  have hfreqInt : Integrable
      (fun ξ : E => kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ))
      (volume : Measure E) := by
    have hcont : Continuous fun ξ : E =>
        kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ) := by
      have hfreq : Continuous fun ξ : E => ((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp ((continuous_massiveFreq_freq a.mass a.speed t).pow 2)
      exact (continuous_kgChar' x).mul
        (hfreq.neg.mul (continuous_hillDrivenDensity a b G₀ t))
    refine Integrable.mono' (h2.const_mul (a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ))) hcont.aestronglyMeasurable
      ?_
    filter_upwards with ξ
    have hfreqsq : a.freq ξ t ^ (2 : ℕ) ≤ (a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ) := by
      have h1 : a.freq ξ t ^ (2 : ℕ) ≤ a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ) * ‖ξ‖ ^ (2 : ℕ) :=
        massiveFreq_sq_le a.mass_pos a.speed_sq_le le_rfl t
      have h3 : kgFreq ξ ^ (2 : ℕ) = 1 + ‖ξ‖ ^ (2 : ℕ) := kgFreq_sq ξ
      nlinarith [sq_nonneg a.mass, sq_nonneg a.sizeBound, sq_nonneg ‖ξ‖]
    calc ‖kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ)‖
        = a.freq ξ t ^ (2 : ℕ) * ‖hillDrivenDensity a b G₀ t ξ‖ := by
          rw [norm_mul, norm_kgChar, one_mul, norm_mul, norm_neg, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a.freq ξ t))]
      _ ≤ ((a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * kgFreq ξ ^ (2 : ℕ)) * ‖hillDrivenDensity a b G₀ t ξ‖ :=
          mul_le_mul_of_nonneg_right hfreqsq (norm_nonneg _)
      _ = (a.mass ^ (2 : ℕ) + a.sizeBound ^ (2 : ℕ)) * (kgFreq ξ ^ (2 : ℕ) * ‖hillDrivenDensity a b G₀ t ξ‖) := by
          ring
  have hsrcInt : Integrable
      (fun ξ : E => kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t))
      (volume : Measure E) := by
    have hbase : Integrable (fun ξ : E => kgChar x ξ *
        kgWeighted N (kgConvBCF (b.density t) (hillPotentialFlow a b G₀ t)) ξ)
        (volume : Measure E) := by
      refine (integrable_kgWeighted (E := E) hdim
        (kgConvBCF (b.density t) (hillPotentialFlow a b G₀ t))).bdd_mul (c := 1)
        ((continuous_kgChar' x).aestronglyMeasurable) ?_
      filter_upwards with ξ
      exact le_of_eq (norm_kgChar x ξ)
    refine hbase.congr ?_
    filter_upwards with ξ
    rw [weighted_hillFlowSource_eq a b G₀ t ξ]
  have hsplit : (∫ ξ, kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ)
      = (∫ ξ, kgChar x ξ *
            (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ)) +
        ∫ ξ, kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t) := by
    rw [← integral_add hfreqInt hsrcInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show kgChar x ξ * hillDrivenDensitySecond a b G₀ t ξ
      = kgChar x ξ * (-(((a.freq ξ t ^ (2 : ℕ) : ℝ) : ℂ)) * hillDrivenDensity a b G₀ t ξ) +
        kgChar x ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ * hillFlowSource a b G₀ ξ t)
    rw [hillDrivenDensitySecond_eq a b G₀ t ξ]
    ring
  rw [hL, hsplit, integral_kgChar_mul_freq_sq a hmeas hint h2 bas t x,
    integral_kgChar_mul_weighted_source hdim a b G₀ t x]
  rfl

end Wave

end GaloisForLFunctions.HTGeometry
