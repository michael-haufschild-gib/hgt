import GaloisForLFunctions.RHTower.CCMRadialSquaredProfile
import GaloisForLFunctions.RHTower.RadialLeakageArcsineMeasure

/-!
# The limiting profile density is the arcsine leakage density

The weak limit of the squared radial profile, `1/(pi x sqrt(x²-1))`, is the corpus's radial leakage density
`1/(x sqrt(x²-1))` divided by `pi`.  So the two lines of work — the profile side, which produces the measure
from Dunster's expansion, and the leakage side, which produces it from the exact exterior mass — converge on
the same measure, and the two antiderivatives agree:

```text
theta(x) = arctan(sqrt(x²-1)) = pi/2 - arcsin(1/x).
```

That identity is proved here *from the two tail laws*, not by differentiating: both sides are the tail mass of
the same density, computed with two different primitives.
-/

noncomputable section

open MeasureTheory Set

namespace GaloisForLFunctions.RHTower

/-- The limiting profile density is the arcsine leakage density up to the factor `pi`. -/
theorem profileDensity_eq_radialLeakageDensity_div_pi (x : ℝ) :
    profileDensity x = _root_.RHTower.radialLeakageDensity x / Real.pi := by
  rw [profileDensity, _root_.RHTower.radialLeakageDensity]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The tail mass of the profile density, for every left endpoint. -/
theorem integral_Ioi_profileDensity_eq {a : ℝ} (ha : 1 ≤ a) :
    (∫ x in Ioi a, profileDensity x) = 1 / 2 - radialAngle a / Real.pi := by
  have hcont : ContinuousWithinAt (fun t : ℝ => radialAngle t / Real.pi) (Ici a) a :=
    ((continuous_radialAngle.div_const Real.pi).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi a, HasDerivAt (fun t : ℝ => radialAngle t / Real.pi)
      (profileDensity x) x := fun x hx =>
    hasDerivAt_radialAngle_div_pi (lt_of_le_of_lt ha hx)
  have hnonneg : ∀ x ∈ Ioi a, 0 ≤ profileDensity x := fun x hx =>
    profileDensity_nonneg (le_of_lt (lt_of_le_of_lt ha hx))
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg
    tendsto_radialAngle_div_pi
  rw [h]

/-- **The two primitives agree.**  `arctan(sqrt(x²-1)) = pi/2 - arcsin(1/x)` for `x >= 1`: both sides are the
tail mass of the same density, up to the factor `pi`. -/
theorem radialAngle_eq_pi_div_two_sub_arcsin {a : ℝ} (ha : 1 ≤ a) :
    radialAngle a = Real.pi / 2 - Real.arcsin (1 / a) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmine := integral_Ioi_profileDensity_eq ha
  have htheirs := _root_.RHTower.integral_Ioi_radialLeakageDensity ha
  have hbridge : (∫ x in Ioi a, profileDensity x)
      = (∫ x in Ioi a, _root_.RHTower.radialLeakageDensity x) / Real.pi := by
    rw [← MeasureTheory.integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x _
    exact profileDensity_eq_radialLeakageDensity_div_pi x
  rw [htheirs] at hbridge
  rw [hmine] at hbridge
  field_simp at hbridge
  linarith [hbridge]

/-- The mass identity `(17)` in the leakage normalisation: `int_1^infinity profileDensity = 1/2`, which is
`(1/pi)` times the corpus's `pi/2`. -/
theorem integral_Ioi_one_profileDensity_eq_half :
    (∫ x in Ioi (1 : ℝ), profileDensity x) = 1 / 2 := integral_Ioi_profileDensity

end GaloisForLFunctions.RHTower

end
