import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceClearedPrincipal
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOnsetPulseTransform

/-!
# The cleared onset factor as a derivative-pulse transform

`clearedOnset s w = 1 + (w - 2s) * onsetCorrection (2s) w` is exactly the Laplace transform of
the onset derivative pulse at exponent `2s - w`.  Consequently it equals `1` at the source rate,
is a positive real number whenever `2s - w` is real, and along the duration ray
`L ↦ L * (2s - w)` its zeros are isolated: every duration has arbitrarily close real durations
at which the stretched onset factor is nonzero.

The stretched factor `clearedOnsetDuration s w L` is the cleared onset of the transition
`u ↦ χ(u/L)`; the identification with the fixed-duration pipeline is the identity
`clearedOnsetDuration s w 1 = clearedOnset s w`.  No physical response is evaluated here.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- The cleared onset numerator is the derivative-pulse transform at exponent `2s - w`. -/
theorem clearedOnset_eq_onsetPulseTransform (s w : ℂ) :
    clearedOnset s w = onsetPulseTransform (2 * s - w) := by
  rw [clearedOnset, onsetPulseTransform_sub]

/-- At the source rate the cleared onset is exactly one. -/
theorem clearedOnset_source_rate (s : ℂ) : clearedOnset s (2 * s) = 1 := by
  rw [clearedOnset_eq_onsetPulseTransform, sub_self, onsetPulseTransform_zero]

/-- For a real exponent difference the cleared onset is a positive real number. -/
theorem clearedOnset_re_pos_of_im_eq_zero {s w : ℂ} (h : (2 * s - w).im = 0) :
    0 < (clearedOnset s w).re := by
  rw [clearedOnset_eq_onsetPulseTransform, ← Complex.re_add_im (2 * s - w), h]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  exact onsetPulseTransform_ofReal_re_pos _

theorem clearedOnset_ne_zero_of_im_eq_zero {s w : ℂ} (h : (2 * s - w).im = 0) :
    clearedOnset s w ≠ 0 := by
  intro h0
  have hp := clearedOnset_re_pos_of_im_eq_zero h
  rw [h0] at hp
  simp at hp

/-- The cleared onset of the transition stretched to duration `L`. -/
def clearedOnsetDuration (s w : ℂ) (L : ℂ) : ℂ :=
  onsetPulseTransform (L * (2 * s - w))

theorem clearedOnsetDuration_one (s w : ℂ) : clearedOnsetDuration s w 1 = clearedOnset s w := by
  rw [clearedOnsetDuration, one_mul, clearedOnset_eq_onsetPulseTransform]

theorem clearedOnsetDuration_zero (s w : ℂ) : clearedOnsetDuration s w 0 = 1 := by
  rw [clearedOnsetDuration, zero_mul, onsetPulseTransform_zero]

theorem differentiable_clearedOnsetDuration (s w : ℂ) :
    Differentiable ℂ (clearedOnsetDuration s w) :=
  differentiable_onsetPulseTransform.comp (differentiable_id.mul_const _)

/-- Around every duration the stretched cleared onset is nonzero except at isolated durations. -/
theorem clearedOnsetDuration_eventually_ne_zero (s w L₀ : ℂ) :
    ∀ᶠ L in 𝓝[≠] L₀, clearedOnsetDuration s w L ≠ 0 :=
  onsetPulseTransform_ray_eventually_ne_zero (2 * s - w) L₀

/-- Every real duration, in particular the original unit duration, has arbitrarily close real
durations whose cleared onset factor is nonzero. -/
theorem exists_real_duration_clearedOnsetDuration_ne_zero (s w : ℂ) (L₀ ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, |L - L₀| < ε ∧ L ≠ L₀ ∧ clearedOnsetDuration s w L ≠ 0 :=
  exists_real_near_onsetPulseTransform_ne_zero (2 * s - w) L₀ ε hε

end
end RHTower.D4BMJointSource
