import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularGaugeConnectionIndexNoGo

/-!
# Adapted energy of singular PW horizontal sections

Every positive even density core gives a reflection-unitary weight. The weighted
square of a horizontal section is exactly its constant amplitude squared times
that core. Constant cores admit nonzero sections with bounded mean energy;
The squared original Gamma profile admits the same sections with finite total energy. Neither
property implies vanishing of the horizontal section.
-/

open Real MeasureTheory GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Reflection-adapted density with prescribed even core. -/
def pwLogDensityFromCore (h : ℝ → ℝ) (t : ℝ) : ℝ :=
  (pwLogSingularGain t)⁻¹ * h t

/-- The horizontal gauge is the positive square root of the singular gain. -/
theorem pwLogSingularGauge_sq (t : ℝ) :
    pwLogSingularGauge t ^ (2 : ℕ) = pwLogSingularGain t := by
  rw [pwLogSingularGauge, pow_two, ← Real.exp_add, pwLogSingularGain]
  congr 1
  ring

/-- Exact weighted density for every horizontal amplitude and every core. -/
theorem pwLogWeightedEnergyDensity_horizontal (h : ℝ → ℝ) (c t : ℝ) :
    pwLogWeightedEnergyDensity (pwLogDensityFromCore h)
      (fun u => c * pwLogSingularGauge u) t = c ^ (2 : ℕ) * h t := by
  unfold pwLogWeightedEnergyDensity pwLogDensityFromCore
  rw [mul_pow, pwLogSingularGauge_sq]
  have ha : pwLogSingularGain t ≠ 0 := Real.exp_ne_zero _
  field_simp [ha]

/-- Horizontal sections carry exactly their density core as weighted energy. -/
theorem pwLogHorizontal_weightedEnergy_classification (f h : ℝ → ℝ) :
    (∀ t, HasDerivAt f (pwLogSingularConnectionPotential t * f t) t) ↔
      ∃ c : ℝ, (∀ t, f t = c * pwLogSingularGauge t) ∧
        (∀ t, pwLogWeightedEnergyDensity (pwLogDensityFromCore h) f t = c ^ (2 : ℕ) * h t) := by
  constructor
  · intro hf
    obtain ⟨c, hc⟩ := pwLogSingular_horizontal_plus_classification hf
    refine ⟨c, hc, ?_⟩
    have heq : f = fun t => c * pwLogSingularGauge t := funext hc
    rw [heq]
    exact pwLogWeightedEnergyDensity_horizontal h c
  · rintro ⟨c, hc, _⟩ t
    have heq : f = fun t => c * pwLogSingularGauge t := funext hc
    rw [heq]
    exact ((hasDerivAt_pwLogSingularGauge t).const_mul c).congr_deriv (by ring)

/-- The constant core gives exact volume growth, allowing nonzero bounded mean energy. -/
theorem pwLogHorizontal_flatCore_intervalEnergy (c a b : ℝ) :
    (∫ t in a..b, pwLogWeightedEnergyDensity (pwLogDensityFromCore (fun _ => 1))
      (fun u => c * pwLogSingularGauge u) t) = (b - a) * c ^ (2 : ℕ) := by
  simp only [pwLogWeightedEnergyDensity_horizontal, mul_one]
  rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Squared original critical-line Gamma source profile. -/
def pwLogGammaSourceDensity (t : ℝ) : ℝ :=
  expShift (1 / 2) 0 t ^ (2 : ℕ)

/-- The density core is the product of the original and reflected Gamma profiles. -/
theorem pwLogGammaSourceDensity_eq_core (t : ℝ) :
    pwLogGammaSourceDensity t =
      pwLogDensityFromCore (fun u => Real.exp (-2 * Real.cosh u)) t := by
  unfold pwLogGammaSourceDensity expShift pwLogDensityFromCore pwLogSingularGain
  rw [← Real.exp_neg]
  simp only [Nat.cast_zero, add_zero]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [pwLogSingularGaugePotential, Real.sinh_eq, Real.cosh_eq]
  ring

theorem pwLogGammaSourceDensity_positive_unitary :
    (∀ t, 0 < pwLogGammaSourceDensity t) ∧
      PWLogReflectionUnitaryDensityLaw pwLogGammaSourceDensity := by
  apply (pwLogReflectionUnitaryDensity_classification _).mpr
  refine ⟨fun t => Real.exp (-2 * Real.cosh t), fun t => Real.exp_pos _, ?_, ?_⟩
  · intro t
    simp only [Real.cosh_neg]
  · exact pwLogGammaSourceDensity_eq_core

/-- Exact original-source weighted density of every horizontal amplitude. -/
theorem pwLogGammaSourceDensity_horizontal_energy (c t : ℝ) :
    pwLogWeightedEnergyDensity pwLogGammaSourceDensity
      (fun u => c * pwLogSingularGauge u) t = c ^ (2 : ℕ) * Real.exp (-2 * Real.cosh t) := by
  have hw : pwLogGammaSourceDensity =
      pwLogDensityFromCore (fun u => Real.exp (-2 * Real.cosh u)) :=
    funext pwLogGammaSourceDensity_eq_core
  rw [hw]
  exact pwLogWeightedEnergyDensity_horizontal _ c t

/-- The even energy core retains both literal Gamma source profiles. -/
theorem pwLogGammaSourceCore_eq_source_product (t : ℝ) :
    Real.exp (-2 * Real.cosh t) = expShift (1 / 2) 0 t * expShift (1 / 2) 0 (-t) := by
  simp only [expShift, Nat.cast_zero, add_zero]
  rw [← Real.exp_add]
  congr 1
  rw [Real.cosh_eq]
  ring

/-- The product of the original and reflected source profiles is integrable. -/
theorem pwLogGammaSourceCore_integrable :
    Integrable (fun t : ℝ => Real.exp (-2 * Real.cosh t)) := by
  have hmajor : Integrable (expShift 1 0) := by
    simpa only [iteratedDeriv_zero] using
      integrable_iteratedDeriv_expShift (σ := 1) zero_lt_one 0
  apply hmajor.mono' (by fun_prop)
  filter_upwards [] with t
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  unfold expShift
  apply Real.exp_le_exp.mpr
  rw [Real.cosh_eq]
  have he := Real.add_one_le_exp (-t)
  simp only [Nat.cast_zero, add_zero, one_mul]
  linarith

/-- The original-source density admits every horizontal amplitude. -/
theorem pwLogGammaSourceDensity_horizontal_integrable (c : ℝ) :
    Integrable (pwLogWeightedEnergyDensity pwLogGammaSourceDensity
      (fun u => c * pwLogSingularGauge u)) := by
  have he : pwLogWeightedEnergyDensity pwLogGammaSourceDensity
      (fun u => c * pwLogSingularGauge u) =
      fun t => c ^ (2 : ℕ) * Real.exp (-2 * Real.cosh t) :=
    funext (pwLogGammaSourceDensity_horizontal_energy c)
  rw [he]
  exact pwLogGammaSourceCore_integrable.const_mul _

/-- The admitted gauge has strictly positive total adapted energy. -/
theorem pwLogGammaSourceDensity_gauge_integral_pos :
    0 < ∫ t, pwLogWeightedEnergyDensity pwLogGammaSourceDensity pwLogSingularGauge t := by
  have he : ∀ t, pwLogWeightedEnergyDensity pwLogGammaSourceDensity pwLogSingularGauge t =
      Real.exp (-2 * Real.cosh t) := by
    intro t
    simpa only [one_mul, one_pow] using pwLogGammaSourceDensity_horizontal_energy 1 t
  simp only [he]
  exact integral_exp_pos pwLogGammaSourceCore_integrable

/-- The admitted horizontal section is fixed by the exact weighted reflection. -/
theorem pwLogSingularWeightedReflection_gauge :
    pwLogSingularWeightedReflection pwLogSingularGauge = pwLogSingularGauge := by
  funext t
  unfold pwLogSingularWeightedReflection pwLogSingularGain pwLogSingularGauge
  rw [pwLogSingularGaugePotential_neg, ← Real.exp_add]
  congr 1
  ring

theorem pwLogSingularGauge_not_neutral_integrable :
    ¬ Integrable (fun t => pwLogSingularGauge t ^ (2 : ℕ)) := by
  intro h
  have hz := pwLogSingular_horizontal_plus_not_integrable hasDerivAt_pwLogSingularGauge h
  have hz0 := congrFun hz 0
  exact (pwLogSingularGauge_pos 0).ne' hz0

/-- The squared original Gamma source admits a strictly positive horizontal fixed section
with finite total adapted energy, although neutral square integrability excludes that section. -/
theorem pwLogGammaSource_exists_finiteEnergy_horizontal_fixed_section :
    ∃ f : ℝ → ℝ,
      (∀ t, 0 < pwLogGammaSourceDensity t) ∧
      PWLogReflectionUnitaryDensityLaw pwLogGammaSourceDensity ∧
      (∀ t, 0 < f t) ∧
      (∀ t, HasDerivAt f (pwLogSingularConnectionPotential t * f t) t) ∧
      pwLogSingularWeightedReflection f = f ∧
      Integrable (pwLogWeightedEnergyDensity pwLogGammaSourceDensity f) ∧
      (0 < ∫ t, pwLogWeightedEnergyDensity pwLogGammaSourceDensity f t) ∧
      (∀ t, pwLogWeightedEnergyDensity pwLogGammaSourceDensity f t =
        Real.exp (-2 * Real.cosh t)) ∧
      ¬ Integrable (fun t => f t ^ (2 : ℕ)) := by
  refine ⟨pwLogSingularGauge,
    pwLogGammaSourceDensity_positive_unitary.1,
    pwLogGammaSourceDensity_positive_unitary.2,
    pwLogSingularGauge_pos, hasDerivAt_pwLogSingularGauge,
    pwLogSingularWeightedReflection_gauge, ?_, pwLogGammaSourceDensity_gauge_integral_pos,
    ?_, pwLogSingularGauge_not_neutral_integrable⟩
  · simpa only [one_mul] using pwLogGammaSourceDensity_horizontal_integrable 1
  · intro t
    simpa only [one_mul, one_pow] using pwLogGammaSourceDensity_horizontal_energy 1 t

end

end RHTower
