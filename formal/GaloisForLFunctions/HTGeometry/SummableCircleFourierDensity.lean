import GaloisForLFunctions.HTGeometry.CircleRieszFischerFourier
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral

/-!
# Symmetric densities from summable circle Fourier tails

For a real sequence `a`, this module packages the literal density
`a 0 + 2 * Σ_{n ≥ 0} a (n + 1) Re(z^n)` on the unit circle.  Absolute
summability of the nonconstant coefficients makes the series measurable and
integrable.  Its tail norm gives pointwise two-sided bounds; a strict tail gap
therefore produces a finite strictly positive density measure.

This is the reusable analytic layer for source-defined circle states.  It
contains no reflected-Hankel positivity assertion.
-/

open MeasureTheory Complex Filter Topology Set
open scoped BigOperators ENNReal NNReal ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real even Fourier density determined by a real sequence. -/
def symmetricCircleFourierDensity (a : ℕ → ℝ) (z : Circle) : ℝ :=
  a 0 + 2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re

/-- Absolute summability of the nonconstant coefficients controls the density series at every
circle point. -/
theorem summable_symmetricCircleFourierDensity_terms {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    Summable (fun n : ℕ => a (n + 1) * ((z : ℂ) ^ (n + 1)).re) := by
  refine Summable.of_norm_bounded ha fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |a (n + 1)| * |((z : ℂ) ^ (n + 1)).re|
      ≤ |a (n + 1)| * ‖(z : ℂ) ^ (n + 1)‖ := by
        gcongr
        exact abs_re_le_norm _
    _ = |a (n + 1)| := by
      rw [norm_pow, Circle.norm_coe, one_pow, mul_one]

/-- The nonconstant part of a symmetric circle density is bounded by twice its absolute Fourier
tail. -/
theorem abs_symmetricCircleFourierDensity_sub_head_le {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    |symmetricCircleFourierDensity a z - a 0| ≤
      2 * ∑' n : ℕ, |a (n + 1)| := by
  have hs := summable_symmetricCircleFourierDensity_terms ha z
  have hterm : ∀ n : ℕ,
      ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ≤ |a (n + 1)| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    calc |a (n + 1)| * |((z : ℂ) ^ (n + 1)).re|
        ≤ |a (n + 1)| * ‖(z : ℂ) ^ (n + 1)‖ := by
          gcongr
          exact abs_re_le_norm _
      _ = |a (n + 1)| := by
        rw [norm_pow, Circle.norm_coe, one_pow, mul_one]
  have htsum : ∑' n : ℕ, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ ≤
      ∑' n : ℕ, |a (n + 1)| :=
    hs.norm.tsum_le_tsum hterm ha
  rw [symmetricCircleFourierDensity]
  have hrewrite : a 0 + 2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re - a 0 =
      2 * ∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re := by
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * ‖∑' n : ℕ, a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖
      ≤ 2 * ∑' n : ℕ, ‖a (n + 1) * ((z : ℂ) ^ (n + 1)).re‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm hs.norm
    _ ≤ 2 * ∑' n : ℕ, |a (n + 1)| := by
      gcongr

/-- Pointwise lower bound from the absolute Fourier tail. -/
theorem symmetricCircleFourierDensity_lower {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    a 0 - 2 * ∑' n : ℕ, |a (n + 1)| ≤ symmetricCircleFourierDensity a z := by
  have h := (abs_le.mp (abs_symmetricCircleFourierDensity_sub_head_le ha z)).1
  linarith

/-- Pointwise upper bound from the absolute Fourier tail. -/
theorem symmetricCircleFourierDensity_upper {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    symmetricCircleFourierDensity a z ≤ a 0 + 2 * ∑' n : ℕ, |a (n + 1)| := by
  have h := (abs_le.mp (abs_symmetricCircleFourierDensity_sub_head_le ha z)).2
  linarith

/-- A strict absolute-tail gap makes the symmetric circle density strictly positive everywhere. -/
theorem symmetricCircleFourierDensity_pos {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|)
    (hstrict : 2 * ∑' n : ℕ, |a (n + 1)| < a 0) (z : Circle) :
    0 < symmetricCircleFourierDensity a z := by
  have hlower := symmetricCircleFourierDensity_lower ha z
  linarith

/-- The symmetric density is measurable. -/
theorem measurable_symmetricCircleFourierDensity (a : ℕ → ℝ) :
    Measurable (symmetricCircleFourierDensity a) := by
  unfold symmetricCircleFourierDensity
  apply Measurable.add measurable_const
  apply Measurable.mul measurable_const
  apply Measurable.tsum
  intro n
  apply Measurable.mul measurable_const
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  exact (Complex.reCLM.continuous.comp (hcoe.pow (n + 1))).measurable

/-- Uniform integrability bound for the symmetric density. -/
theorem norm_symmetricCircleFourierDensity_le {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) (z : Circle) :
    ‖symmetricCircleFourierDensity a z‖ ≤
      |a 0| + 2 * ∑' n : ℕ, |a (n + 1)| := by
  have hbound := abs_symmetricCircleFourierDensity_sub_head_le ha z
  have hfirst : ‖symmetricCircleFourierDensity a z - a 0‖ ≤
      2 * ∑' n : ℕ, |a (n + 1)| := by
    simpa only [Real.norm_eq_abs] using hbound
  have hsecond : ‖a 0‖ = |a 0| := Real.norm_eq_abs _
  calc ‖symmetricCircleFourierDensity a z‖ =
      ‖(symmetricCircleFourierDensity a z - a 0) + a 0‖ := by
        ring_nf
    _ ≤ ‖symmetricCircleFourierDensity a z - a 0‖ + ‖a 0‖ := norm_add_le _ _
    _ ≤ 2 * ∑' n : ℕ, |a (n + 1)| + |a 0| := by
      rw [hsecond]
      exact add_le_add hfirst (le_refl _)
    _ = _ := by ring

/-- The symmetric density is integrable against normalized circle Haar measure. -/
theorem integrable_symmetricCircleFourierDensity {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    Integrable (symmetricCircleFourierDensity a) circleLebesgue := by
  apply Integrable.of_bound
    (measurable_symmetricCircleFourierDensity a).aestronglyMeasurable
    (|a 0| + 2 * ∑' n : ℕ, |a (n + 1)|)
  filter_upwards with z
  exact norm_symmetricCircleFourierDensity_le ha z

/-- The finite circle measure having the symmetric Fourier density with respect to Haar. -/
def symmetricCircleFourierDensityMeasure (a : ℕ → ℝ) : Measure Circle :=
  circleLebesgue.withDensity fun z => ENNReal.ofReal (symmetricCircleFourierDensity a z)

/-- Absolute summability ensures that the symmetric density measure is finite. -/
theorem symmetricCircleFourierDensityMeasure_finite {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => |a (n + 1)|) :
    IsFiniteMeasure (symmetricCircleFourierDensityMeasure a) := by
  unfold symmetricCircleFourierDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (integrable_symmetricCircleFourierDensity ha).hasFiniteIntegral

end

end GaloisForLFunctions.HTGeometry
