import GaloisForLFunctions.HTGeometry.FokasLenellsRawScatteringTaylor
import GaloisForLFunctions.HTGeometry.FokasLenellsCompatibilityMoment
import GaloisForLFunctions.HTGeometry.FokasLenellsZeroScattering

/-!
# The anchored mixed primitive in the genuine scattering coefficients

The second Dyson coefficient contains the primitive of q times the reflected
spatial derivative. Its uniform bound makes multiplication by arbitrary
Schwartz profiles integrable. Integration by parts then reduces the nested
cubic integral to a local cubic moment, without any compatibility premise.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def rawMixedProfile (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ := mulS q (reflectedDerivative q)

theorem rawMixedProfile_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    rawMixedProfile q x = q x*reflectedDerivative q x := mulS_apply _ _ x

def rawMixedPrimitive (q : SchwartzMap ℝ ℂ) (x : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..x, rawMixedProfile q s

def rawMixedMass (q : SchwartzMap ℝ ℂ) : ℝ := ∫ x : ℝ, ‖rawMixedProfile q x‖

theorem rawMixedMass_nonneg (q : SchwartzMap ℝ ℂ) : 0 ≤ rawMixedMass q :=
  integral_nonneg fun x => norm_nonneg (rawMixedProfile q x)

theorem rawMixedPrimitive_hasDerivAt (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (rawMixedPrimitive q) (q x*reflectedDerivative q x) x := by
  have hh := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := x) (rawMixedProfile q).integrable.intervalIntegrable
    (rawMixedProfile q).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    (rawMixedProfile q).continuous.continuousAt
  convert! hh using 1
  exact (rawMixedProfile_apply q x).symm

theorem continuous_rawMixedPrimitive (q : SchwartzMap ℝ ℂ) : Continuous (rawMixedPrimitive q) :=
  (rawMixedProfile q).integrable.continuous_primitive 0

theorem rawMixedPrimitive_initial (q : SchwartzMap ℝ ℂ) : rawMixedPrimitive q 0 = 0 := by
  simp only [rawMixedPrimitive,intervalIntegral.integral_same]

/-- The mixed primitive is bounded over the entire real line by a finite Schwartz mass. -/
theorem rawMixedPrimitive_bound (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖rawMixedPrimitive q x‖ ≤ rawMixedMass q :=
  intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_le_integral (rawMixedProfile q).integrable.norm
      (Eventually.of_forall fun s => norm_nonneg (rawMixedProfile q s)))

/-- Every Schwartz test remains integrable after multiplication by the bounded mixed primitive. -/
theorem integrable_schwartz_mul_rawMixedPrimitive (q f : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => f x*rawMixedPrimitive q x) := by
  have hc : Continuous (fun x : ℝ => f x*rawMixedPrimitive q x) :=
    f.continuous.mul (continuous_rawMixedPrimitive q)
  apply (f.integrable.norm.mul_const (rawMixedMass q)).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (rawMixedPrimitive_bound q x) (norm_nonneg (f x))

/-- An integration-by-parts identity for the actual nested second primitive. -/
theorem integral_deriv_mul_rawMixedPrimitive (q f : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, deriv f x*rawMixedPrimitive q x) = -∫ x : ℝ, f x*q x*reflectedDerivative q x := by
  have hi1 : Integrable (fun x : ℝ => deriv f x*rawMixedPrimitive q x) := by
    simpa only [SchwartzMap.derivCLM_apply] using
      integrable_schwartz_mul_rawMixedPrimitive q (SchwartzMap.derivCLM ℂ ℂ f)
  have hi2 : Integrable (fun x : ℝ => f x*q x*reflectedDerivative q x) := by
    have hh : Integrable (fun x : ℝ => mulS (mulS f q) (reflectedDerivative q) x) :=
      (mulS (mulS f q) (reflectedDerivative q)).integrable
    simpa only [mulS_apply] using hh
  have hd : ∀ x : ℝ, HasDerivAt (fun y => f y*rawMixedPrimitive q y)
      (deriv f x*rawMixedPrimitive q x+f x*q x*reflectedDerivative q x) x := by
    intro x
    have hf := ((f.smooth ⊤).differentiable (by simp)).differentiableAt (x := x) |>.hasDerivAt
    convert! hf.mul (rawMixedPrimitive_hasDerivAt q x) using 1
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd (hi1.add hi2)
    (integrable_schwartz_mul_rawMixedPrimitive q f)
  rw [integral_add hi1 hi2] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- The nested cubic integral reduces exactly to the local reflected cubic moment. -/
theorem integral_q_deriv_mul_rawMixedPrimitive (q : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, deriv q x*rawMixedPrimitive q x) = -∫ x : ℝ, q x^2*reflectedDerivative q x := by
  simpa only [pow_two] using integral_deriv_mul_rawMixedPrimitive q q

end
end GaloisForLFunctions.HTGeometry.FokasLenells
