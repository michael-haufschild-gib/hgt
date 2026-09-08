import GaloisForLFunctions.HTGeometry.FokasLenellsContourScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsSpectralEndpoints

/-!
# Uniform reflection control on the entire Fokas–Lenells contour

The explicit, nontrivial normalization of an arbitrary Schwartz potential
commutes with the imaginary-ray twist. Consequently the small-reflection
and jump-positivity mechanisms of Propositions 3.2 and 3.4 of
arXiv:2607.19649v1 hold on all four nonzero continuous-spectrum rays.
Both transmission coefficients are bounded away from zero, both reflection
quotients are at most one third, and the space-time jump energy has the
uniform lower bound five ninths. Reciprocal spectral envelopes also give
vanishing reflection at both ends of every ray. The time phase here is
prescribed scattering evolution, not a reconstructed nonlinear PDE solution.
-/

open Complex Matrix Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- One potential rescaling gives the same amplitude bounds on all four rays. -/
theorem globalSmall_contour_amplitudes (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) :
    ‖contourTransmission (globalSmallScatteringPotential q) vertical negative κ-1‖ ≤ 1/4 ∧
    ‖contourReverseTransmission (globalSmallScatteringPotential q) vertical negative κ-1‖ ≤ 1/4 ∧
    ‖contourReflectionAmplitude (globalSmallScatteringPotential q) vertical negative κ‖ ≤ 1/4 := by
  have hb := globalSmallScatteringPotential_amplitudes (contourSource q vertical) κ
  rw [contourTransmission_eq, contourReverseTransmission_eq, contourReflectionAmplitude_norm,
    contourSource_globalSmall]
  cases vertical
  · exact hb
  · exact ⟨hb.2.1,hb.1,hb.2.2⟩

theorem globalSmall_contour_transmission_lower (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    3/4 ≤ ‖contourTransmission (globalSmallScatteringPotential q) vertical negative κ‖ ∧
    3/4 ≤ ‖contourReverseTransmission (globalSmallScatteringPotential q) vertical negative κ‖ := by
  have hb := globalSmallScatteringPotential_transmission_lower (contourSource q vertical) κ
  rw [contourTransmission_eq, contourReverseTransmission_eq, contourSource_globalSmall]
  cases vertical
  · exact hb
  · exact ⟨hb.2,hb.1⟩

/-- No nonzero continuous-spectrum transmission zero survives the explicit normalization. -/
theorem globalSmall_contour_transmission_nonzero (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    contourTransmission (globalSmallScatteringPotential q) vertical negative κ ≠ 0 ∧
    contourReverseTransmission (globalSmallScatteringPotential q) vertical negative κ ≠ 0 := by
  have hb := globalSmall_contour_transmission_lower q vertical negative κ
  constructor <;> apply norm_pos_iff.mp <;> linarith [hb.1,hb.2]

def contourReflectionCoefficient (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourReflectionAmplitude q vertical negative κ/contourTransmission q vertical negative κ

def contourReverseReflectionCoefficient (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ : ℝ) : ℂ :=
  contourReverseReflectionAmplitude q vertical negative κ/contourReverseTransmission q vertical negative κ

/-- Imaginary rays exchange the two quotient norms, so the real-ray estimates transfer exactly. -/
theorem contourReflectionCoefficient_norms (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    ‖contourReflectionCoefficient q vertical negative κ‖ =
      (if vertical then ‖reverseReflectionCoefficient (contourSource q vertical) κ‖
        else ‖reflectionCoefficient (contourSource q vertical) κ‖) ∧
    ‖contourReverseReflectionCoefficient q vertical negative κ‖ =
      (if vertical then ‖reflectionCoefficient (contourSource q vertical) κ‖
        else ‖reverseReflectionCoefficient (contourSource q vertical) κ‖) := by
  simp only [contourReflectionCoefficient, contourReverseReflectionCoefficient, norm_div,
    contourReverseReflectionAmplitude_eq_neg, norm_neg, contourReflectionAmplitude_norm,
    contourTransmission_eq, contourReverseTransmission_eq, reflectionCoefficient,
    reverseReflectionCoefficient, reverseReflectionAmplitude_eq_neg]
  cases vertical <;> simp

/-- Proposition 3.2's small-reflection conclusion, uniformly on the full nonzero contour. -/
theorem globalSmall_contour_reflection_bounds (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    ‖contourReflectionCoefficient (globalSmallScatteringPotential q) vertical negative κ‖ ≤ 1/3 ∧
    ‖contourReverseReflectionCoefficient (globalSmallScatteringPotential q) vertical negative κ‖ ≤ 1/3 := by
  have hb := globalSmallScatteringPotential_reflection_bounds (contourSource q vertical) κ
  rw [(contourReflectionCoefficient_norms _ vertical negative κ).1,
    (contourReflectionCoefficient_norms _ vertical negative κ).2, contourSource_globalSmall]
  cases vertical
  · exact hb
  · exact ⟨hb.2,hb.1⟩

/-- Reciprocal low- and high-frequency envelopes hold on every ray, for arbitrary Schwartz data. -/
theorem contourReflectionAmplitude_exponential_envelopes (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ : ℝ) :
    ‖contourReflectionAmplitude q vertical negative κ‖ ≤
      (2*potentialScatteringError (contourSource q vertical))*Real.exp κ ∧
    ‖contourReflectionAmplitude q vertical negative κ‖ ≤
      (potentialScatteringError (contourSource q vertical)/2)*Real.exp (-κ) := by
  rw [contourReflectionAmplitude_norm]
  exact reflectionAmplitude_exponential_envelopes (contourSource q vertical) κ

theorem contourReflectionAmplitude_tendsto_high (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (contourReflectionAmplitude q vertical negative) atTop (𝓝 0) := by
  change Tendsto (fun κ => contourReflectionAmplitude q vertical negative κ) atTop (𝓝 0)
  by_cases he : vertical = negative
  · simpa only [contourReflectionAmplitude_eq, if_pos he] using
      reflectionAmplitude_tendsto_high (contourSource q vertical)
  · simpa only [contourReflectionAmplitude_eq, if_neg he, neg_zero] using
      (reflectionAmplitude_tendsto_high (contourSource q vertical)).neg

theorem contourReflectionAmplitude_tendsto_low (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (contourReflectionAmplitude q vertical negative) atBot (𝓝 0) := by
  change Tendsto (fun κ => contourReflectionAmplitude q vertical negative κ) atBot (𝓝 0)
  by_cases he : vertical = negative
  · simpa only [contourReflectionAmplitude_eq, if_pos he] using
      reflectionAmplitude_tendsto_low (contourSource q vertical)
  · simpa only [contourReflectionAmplitude_eq, if_neg he, neg_zero] using
      (reflectionAmplitude_tendsto_low (contourSource q vertical)).neg

/-- Both normalized reflection coefficients vanish at infinity on each contour ray. -/
theorem globalSmall_contour_reflection_tendsto_high (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (contourReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) atTop (𝓝 0) ∧
    Tendsto (contourReverseReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) atTop (𝓝 0) := by
  have h1 := (globalSmallScatteringPotential_reflection_tendsto_high (contourSource q vertical)).norm
  have h2 := (globalSmallScatteringPotential_reverseReflection_tendsto_high (contourSource q vertical)).norm
  simp only [norm_zero] at h1 h2
  constructor <;> apply tendsto_iff_norm_sub_tendsto_zero.mpr <;> simp only [sub_zero]
  · simp only [(contourReflectionCoefficient_norms _ vertical negative _).1, contourSource_globalSmall]
    cases vertical
    · exact h1
    · exact h2
  · simp only [(contourReflectionCoefficient_norms _ vertical negative _).2, contourSource_globalSmall]
    cases vertical
    · exact h2
    · exact h1

/-- Both normalized reflection coefficients vanish at the spectral origin along each ray. -/
theorem globalSmall_contour_reflection_tendsto_low (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) :
    Tendsto (contourReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) atBot (𝓝 0) ∧
    Tendsto (contourReverseReflectionCoefficient (globalSmallScatteringPotential q) vertical negative) atBot (𝓝 0) := by
  have h1 := (globalSmallScatteringPotential_reflection_tendsto_low (contourSource q vertical)).norm
  have h2 := (globalSmallScatteringPotential_reverseReflection_tendsto_low (contourSource q vertical)).norm
  simp only [norm_zero] at h1 h2
  constructor <;> apply tendsto_iff_norm_sub_tendsto_zero.mpr <;> simp only [sub_zero]
  · simp only [(contourReflectionCoefficient_norms _ vertical negative _).1, contourSource_globalSmall]
    cases vertical
    · exact h1
    · exact h2
  · simp only [(contourReflectionCoefficient_norms _ vertical negative _).2, contourSource_globalSmall]
    cases vertical
    · exact h2
    · exact h1

def contourScatteringAngle (vertical : Bool) (κ t x : ℝ) : ℝ :=
  contourSquaredParameter vertical κ*x-t/(4*contourSquaredParameter vertical κ)

def contourSpaceTimeReflection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ t x : ℝ) : ℂ :=
  FDNLS.staggerPhase 2 (contourScatteringAngle vertical κ t x)*contourReflectionCoefficient q vertical negative κ

def contourSpaceTimeReverseReflection (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ t x : ℝ) : ℂ :=
  FDNLS.staggerPhase (-2) (contourScatteringAngle vertical κ t x)*contourReverseReflectionCoefficient q vertical negative κ

theorem contourSpaceTimeReflection_norms (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ t x : ℝ) :
    ‖contourSpaceTimeReflection q vertical negative κ t x‖ = ‖contourReflectionCoefficient q vertical negative κ‖ ∧
    ‖contourSpaceTimeReverseReflection q vertical negative κ t x‖ = ‖contourReverseReflectionCoefficient q vertical negative κ‖ := by
  simp [contourSpaceTimeReflection, contourSpaceTimeReverseReflection, FDNLS.norm_staggerPhase]

def contourSpaceTimeJump (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ t x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  jump (contourSpaceTimeReflection q vertical negative κ t x)
    (contourSpaceTimeReverseReflection q vertical negative κ t x)

theorem contourSpaceTimeJump_det (q : SchwartzMap ℝ ℂ) (vertical negative : Bool) (κ t x : ℝ) :
    (contourSpaceTimeJump q vertical negative κ t x).det = 1 := by
  exact det_jump _ _

/-- Proposition 3.4's coercivity mechanism holds on every ray, at every prescribed space-time phase. -/
theorem globalSmall_contour_spaceTime_coercivity (q : SchwartzMap ℝ ℂ)
    (vertical negative : Bool) (κ t x : ℝ) (u v : ℂ) :
    (5/9 : ℝ)*(normSq u+normSq v) ≤
      energy (contourSpaceTimeReflection (globalSmallScatteringPotential q) vertical negative κ t x)
        (contourSpaceTimeReverseReflection (globalSmallScatteringPotential q) vertical negative κ t x) u v := by
  let a := contourSpaceTimeReflection (globalSmallScatteringPotential q) vertical negative κ t x
  let b := contourSpaceTimeReverseReflection (globalSmallScatteringPotential q) vertical negative κ t x
  have hbnd := globalSmall_contour_reflection_bounds q vertical negative κ
  have ha : ‖a‖ ≤ 1/3 := by
    simpa only [a, (contourSpaceTimeReflection_norms _ vertical negative κ t x).1] using hbnd.1
  have hb : ‖b‖ ≤ 1/3 := by
    simpa only [b, (contourSpaceTimeReflection_norms _ vertical negative κ t x).2] using hbnd.2
  have hab : ‖a‖*‖b‖ ≤ 1/9 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1/3-‖a‖) (norm_nonneg b)]
  have h1 : 5/9 ≤ 1-(‖a‖+‖b‖)/2 := by linarith
  have h2 : 5/9 ≤ 1-‖a‖*‖b‖-(‖a‖+‖b‖)/2 := by linarith
  calc
    (5/9 : ℝ)*(normSq u+normSq v) = (5/9 : ℝ)*normSq u+(5/9 : ℝ)*normSq v := by ring
    _ ≤ (1-(‖a‖+‖b‖)/2)*normSq u+(1-‖a‖*‖b‖-(‖a‖+‖b‖)/2)*normSq v :=
      add_le_add (mul_le_mul_of_nonneg_right h1 (normSq_nonneg u))
        (mul_le_mul_of_nonneg_right h2 (normSq_nonneg v))
    _ ≤ _ := energy_norm_lower_bound a b u v

end
end GaloisForLFunctions.HTGeometry.FokasLenells
