import GaloisForLFunctions.HTGeometry.KleinGordonProbeNormalization

/-!
# Mixed derivatives of a synthesis

A spatial derivative of a synthesis is again a synthesis: the derivative along `v` multiplies the
density by `2πi⟪ξ,v⟫`. So the mixed second derivatives need no new analysis at all — the first
derivative theorem, applied to the derived density, gives them, and the derived density costs exactly
one power of the weight.

This is what the coordinate interface of the corpus needs: to know that a first partial derivative is
differentiable one must know *all* its partials, mixed ones included.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The derived density -/

/-- The density of a directional derivative: the frequency appears as a factor. -/
noncomputable def kgDirDensity (v : E) (f : E → ℂ) (ξ : E) : ℂ :=
  2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * f ξ

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_kgDirDensity_le (v : E) (f : E → ℂ) (ξ : E) :
    ‖kgDirDensity v f ξ‖ ≤ 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖) := by
  rw [kgDirDensity, norm_mul, norm_two_pi_I_inner]
  have hinner := norm_inner_le_kgFreq v ξ
  have hf : (0 : ℝ) ≤ ‖f ξ‖ := norm_nonneg _
  have hpipos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hstep : |(⟪ξ, v⟫ : ℝ)| * ‖f ξ‖ ≤ ‖v‖ * kgFreq ξ * ‖f ξ‖ :=
    mul_le_mul_of_nonneg_right hinner hf
  nlinarith [hstep, hpipos]

theorem aestronglyMeasurable_kgDirDensity {f : E → ℂ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E)) (v : E) :
    AEStronglyMeasurable (kgDirDensity v f) (volume : Measure E) := by
  have hinnerCont : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
  exact ((continuous_const.mul hinnerCont).aestronglyMeasurable).mul hmeas

theorem integrable_kgDirDensity {f : E → ℂ} (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E)) (v : E) :
    Integrable (kgDirDensity v f) (volume : Measure E) := by
  refine Integrable.mono' (h1.const_mul (2 * Real.pi * ‖v‖))
    (aestronglyMeasurable_kgDirDensity hmeas v) ?_
  filter_upwards with ξ
  exact norm_kgDirDensity_le v f ξ

theorem integrable_kgFreq_mul_kgDirDensity {f : E → ℂ}
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E)) (v : E)
    (hmeas : AEStronglyMeasurable f (volume : Measure E)) :
    Integrable (fun ξ : E => kgFreq ξ * ‖kgDirDensity v f ξ‖) (volume : Measure E) := by
  refine Integrable.mono' (h2.const_mul (2 * Real.pi * ‖v‖))
    ((continuous_kgFreq.aestronglyMeasurable).mul
      ((aestronglyMeasurable_kgDirDensity hmeas v).norm)) ?_
  filter_upwards with ξ
  have hstep : kgFreq ξ * ‖kgDirDensity v f ξ‖
      ≤ kgFreq ξ * (2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖)) :=
    mul_le_mul_of_nonneg_left (norm_kgDirDensity_le v f ξ) (kgFreq_pos ξ).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (kgFreq_pos ξ).le (norm_nonneg _))]
  calc kgFreq ξ * ‖kgDirDensity v f ξ‖
      ≤ kgFreq ξ * (2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖f ξ‖)) := hstep
    _ = 2 * Real.pi * ‖v‖ * (kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) := by ring

/-! ## The first derivative, as a synthesis -/

/-- **The directional derivative of a synthesis is the synthesis of the derived density.** -/
theorem hasDerivAt_kgSynthesis_dir_synthesis {f : E → ℂ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (hint : Integrable f (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E)) (x v : E) (r : ℝ) :
    HasDerivAt (fun s : ℝ => kgSynthesis f (x + s • v))
      (kgSynthesis (kgDirDensity v f) (x + r • v)) r := by
  have hmain := hasDerivAt_kgSynthesis_dir hmeas hint h1 x v r
  refine hmain.congr_deriv ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show 2 * Real.pi * Complex.I * ((⟪ξ, v⟫ : ℝ) : ℂ) * kgChar (x + r • v) ξ * f ξ
    = kgChar (x + r • v) ξ * kgDirDensity v f ξ
  rw [kgDirDensity]
  ring

/-- **The mixed second derivative of a synthesis**, as the synthesis of the twice derived
density. -/
theorem hasDerivAt_kgSynthesis_dir_dir {f : E → ℂ}
    (hmeas : AEStronglyMeasurable f (volume : Measure E))
    (h1 : Integrable (fun ξ : E => kgFreq ξ * ‖f ξ‖) (volume : Measure E))
    (h2 : Integrable (fun ξ : E => kgFreq ξ ^ (2 : ℕ) * ‖f ξ‖) (volume : Measure E)) (x v w : E)
    (r : ℝ) :
    HasDerivAt (fun s : ℝ => kgSynthesis (kgDirDensity v f) (x + s • w))
      (kgSynthesis (kgDirDensity w (kgDirDensity v f)) (x + r • w)) r :=
  hasDerivAt_kgSynthesis_dir_synthesis (aestronglyMeasurable_kgDirDensity hmeas v)
    (integrable_kgDirDensity hmeas h1 v) (integrable_kgFreq_mul_kgDirDensity h2 v hmeas) x w r

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgDirDensity {f : E → ℂ} (hf : Continuous f) (v : E) :
    Continuous (kgDirDensity v f) := by
  have hinnerCont : Continuous fun ξ : E => ((⟪ξ, v⟫ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp (continuous_id.prodMk continuous_const))
  exact (continuous_const.mul hinnerCont).mul hf

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_kgDirDensity_time {g : ℝ → E → ℂ} (v : E) (ξ : E)
    (hg : Continuous fun t : ℝ => g t ξ) :
    Continuous fun t : ℝ => kgDirDensity v (g t) ξ :=
  continuous_const.mul hg

end GaloisForLFunctions.HTGeometry
