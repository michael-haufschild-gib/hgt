import GaloisForLFunctions.HTGeometry.FokasLenellsRegularPositiveWeight

/-!
# Second inverse weights under the paper's time and position phases

The actual jump channels retain exactly the norms of the normalized
reflection channels. Consequently the positive-axis second inverse
weight, and its compatibility obstruction, persist at every time and
position. No differentiation of the nonlinear inverse map is asserted.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Actual jump data with the second inverse squared-spectral-coordinate weight. -/
def regularSecondInverseJump (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  regularInverseFrequencyJump q t x reverse z / (z : ℂ)

/-- This is exactly the jump reflection entry divided by z squared. -/
theorem regularSecondInverseJump_eq (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    regularSecondInverseJump q t x reverse z =
      (if reverse then regularJumpReverseReflection (globalSmallScatteringPotential q) t x z
        else regularJumpReflection (globalSmallScatteringPotential q) t x z) / (z : ℂ)^2 := by
  simp only [regularSecondInverseJump, regularInverseFrequencyJump, div_div, pow_two]

/-- Both physical phases preserve the second-inverse-weight channel norm exactly. -/
theorem regularSecondInverseJump_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖regularSecondInverseJump q t x reverse z‖ =
      ‖regularSecondInverseReflection (globalSmallScatteringPotential q) reverse z‖ := by
  rw [regularSecondInverseJump, regularSecondInverseReflection_globalSmall_eq,
    norm_div, norm_div, regularInverseFrequencyJump_norm]

theorem regularSecondInverseJump_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (regularSecondInverseJump q t x reverse) :=
  (regularInverseFrequencyJump_measurable q t x reverse).div Complex.continuous_ofReal.measurable

/-- Phase evolution preserves every Lp membership for every measure, including restricted spectral intervals. -/
theorem regularSecondInverseJump_memLp_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool)
    (p : ℝ≥0∞) (μ : Measure ℝ) :
    MemLp (regularSecondInverseJump q t x reverse) p μ ↔
      MemLp (regularSecondInverseReflection (globalSmallScatteringPotential q) reverse) p μ :=
  memLp_congr_norm (regularSecondInverseJump_measurable q t x reverse).aestronglyMeasurable
    (regularSecondInverseReflection_measurable _ reverse).aestronglyMeasurable
    (Eventually.of_forall (regularSecondInverseJump_norm q t x reverse))

/-- The lower jump channel has the global positive-axis second inverse weight at every time and position. -/
theorem regularSecondInverseJump_lower_positive_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (regularSecondInverseJump q t x false) 2 (volume.restrict (Ioi 0)) :=
  (regularSecondInverseJump_memLp_iff q t x false 2 _).2
    (regularSecondInverseReflection_lower_globalSmall_positive_memLp q)

/-- For the upper jump channel, compatibility remains the exact positive-axis criterion at every time and position. -/
theorem regularSecondInverseJump_upper_positive_memLp_iff (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (regularSecondInverseJump q t x true) 2 (volume.restrict (Ioi 0)) ↔
      compatibilityMoment (globalSmallScatteringPotential q) = 0 := by
  rw [regularSecondInverseJump_memLp_iff,
    regularSecondInverseReflection_upper_globalSmall_positive_memLp_iff]

/-- Time and position phases cannot repair the explicit small Gaussian obstruction. -/
theorem regularSecondInverseJump_upper_globalSmallGaussian_not_memLp (a t x : ℝ) :
    ¬ MemLp (regularSecondInverseJump (compatibilityGaussian a) t x true) 2 volume := by
  rw [regularSecondInverseJump_memLp_iff]
  exact regularSecondInverseReflection_upper_globalSmallGaussian_not_memLp a

/-- Compatible profiles with prescribed fifth scattering trace retain the weighted jump estimate everywhere. -/
theorem regularSecondInverseJump_upper_quinticGaussianProfile_positive_memLp (a : ℝ) (c : ℂ) (t x : ℝ) :
    MemLp (regularSecondInverseJump (quinticGaussianProfile a c) t x true) 2
      (volume.restrict (Ioi 0)) :=
  (regularSecondInverseJump_upper_positive_memLp_iff _ t x).2
    (compatibilityMoment_globalSmall_quinticGaussianProfile a c)

end
end GaloisForLFunctions.HTGeometry.FokasLenells
