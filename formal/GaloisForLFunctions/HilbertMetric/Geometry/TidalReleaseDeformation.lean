import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quadratic release and its exact quartic deformation

The quadratic configuration jet in §4 of Beron-Vera,
*Tendex Lines and Short-Time Deformation: The Geometry of Lunar Tides*,
arXiv:2611.16083, has an exact Hilbert-space length identity. Its quadratic
coefficient is the acceleration pairing; its quartic coefficient is a squared
norm. Thus a null direction need not be an acceleration-free direction.

These are identities for the quadratic jet, not an assertion that the jet is
the full nonlinear gravitational flow.
-/

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Configuration jet for release from rest with initial acceleration `a`. -/
def tidalReleaseJet (x a : H) (t : ℝ) : H := x + (t ^ 2 / 2) • a

/-- Exact squared-length identity, including the quartic remainder. -/
theorem tidalReleaseJet_norm_sq (x a : H) (t : ℝ) :
    ‖tidalReleaseJet x a t‖ ^ 2 =
      ‖x‖ ^ 2 + t ^ 2 * inner ℝ x a + t ^ 4 / 4 * ‖a‖ ^ 2 := by
  rw [tidalReleaseJet, norm_add_sq_real, norm_smul, real_inner_smul_right,
    mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- Release is even in time, reflecting the zero initial velocity. -/
theorem tidalReleaseJet_neg (x a : H) (t : ℝ) :
    tidalReleaseJet x a (-t) = tidalReleaseJet x a t := by
  simp only [tidalReleaseJet, neg_sq]

/-- The velocity of the quadratic configuration jet. -/
theorem tidalReleaseJet_hasDerivAt (x a : H) (t : ℝ) :
    HasDerivAt (tidalReleaseJet x a) (t • a) t := by
  convert (hasDerivAt_const t x).add
    (((hasDerivAt_id t).pow 2).div_const 2 |>.smul_const a) using 1 <;>
    simp [tidalReleaseJet]

/-- The length coefficient differs from the quadratic prediction by a nonnegative term. -/
theorem tidalReleaseJet_quadratic_lower (x a : H) (t : ℝ) :
    ‖x‖ ^ 2 + t ^ 2 * inner ℝ x a ≤ ‖tidalReleaseJet x a t‖ ^ 2 := by
  rw [tidalReleaseJet_norm_sq]
  exact le_add_of_nonneg_right (by positivity)

/-- The lower bound is sharp exactly at release or at zero acceleration. -/
theorem tidalReleaseJet_quadratic_eq_iff (x a : H) (t : ℝ) :
    ‖tidalReleaseJet x a t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 * inner ℝ x a ↔
      t = 0 ∨ a = 0 := by
  rw [tidalReleaseJet_norm_sq, add_eq_left, mul_eq_zero, div_eq_zero_iff,
    pow_eq_zero_iff (by decide : 4 ≠ 0), sq_eq_zero_iff, norm_eq_zero]
  norm_num

/-- Nullity and exact length preservation are jointly equivalent to zero time or
zero acceleration. No sign or nondegeneracy premise is required. -/
theorem tidalReleaseJet_null_and_length_iff (x a : H) (t : ℝ) :
    (inner ℝ x a = 0 ∧ ‖tidalReleaseJet x a t‖ ^ 2 = ‖x‖ ^ 2) ↔
      (inner ℝ x a = 0 ∧ (t = 0 ∨ a = 0)) := by
  constructor
  · rintro ⟨hnull, hlen⟩
    refine ⟨hnull, (tidalReleaseJet_quadratic_eq_iff x a t).mp ?_⟩
    simpa only [hnull, mul_zero, add_zero] using hlen
  · rintro ⟨hnull, hzero⟩
    refine ⟨hnull, ?_⟩
    simpa only [hnull, mul_zero, add_zero] using
      (tidalReleaseJet_quadratic_eq_iff x a t).mpr hzero

/-- Polarization gives the Cauchy--Green bilinear identity for any two releases. -/
theorem tidalReleaseJet_inner (x a y b : H) (t : ℝ) :
    inner ℝ (tidalReleaseJet x a t) (tidalReleaseJet y b t) =
      inner ℝ x y + t ^ 2 / 2 * (inner ℝ a y + inner ℝ x b) +
        t ^ 4 / 4 * inner ℝ a b := by
  simp only [tidalReleaseJet, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring

end GaloisForLFunctions.HilbertMetric
