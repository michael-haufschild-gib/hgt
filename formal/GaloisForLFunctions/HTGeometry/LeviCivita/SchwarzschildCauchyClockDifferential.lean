import GaloisForLFunctions.HTGeometry.LeviCivita.SchwarzschildCauchySlices
import GaloisForLFunctions.HTGeometry.TanhSubstitution
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Schwarzschild clock has timelike differential

The inverse derivative of `tanh` supplies the differential missing from the
algebraic slice construction. At every point of every slice, the actual clock
has positive time derivative and a strictly timelike gradient for every
positive conformal multiple of the radial Kruskal metric.
-/

noncomputable section
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open Real Filter

/-- Inverse hyperbolic tangent has derivative `cosh(u)²` at `tanh(u)`. -/
theorem artanh_hasDerivAt_tanh (u : ℝ) :
    HasDerivAt artanh (cosh u ^ 2) (tanh u) := by
  have hminus : 0 < 1 - tanh u := sub_pos.mpr (tanh_lt_one u)
  have hplus : 0 < 1 + tanh u := by linarith only [neg_one_lt_tanh u]
  have hc : ContinuousAt artanh (tanh u) := by
    apply ContinuousAt.log
    · exact (((continuousAt_const.add continuousAt_id).div
        (continuousAt_const.sub continuousAt_id) hminus.ne').sqrt)
    · exact (sqrt_pos.mpr (div_pos hplus hminus)).ne'
  have hf : HasDerivAt tanh (1 / cosh u ^ 2) (artanh (tanh u)) := by
    rw [artanh_tanh]
    exact _root_.HTGeometry.hasDerivAt_tanh u
  have hlocal : ∀ᶠ y in 𝓝 (tanh u), tanh (artanh y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨neg_one_lt_tanh u, tanh_lt_one u⟩] with y hy
    exact tanh_artanh hy
  simpa only [one_div, inv_inv] using
    hf.of_local_left_inverse hc (by positivity) hlocal

/-- Positive time derivative of the clock, written in slice coordinates. -/
def schwarzschildClockTimeDerivative (m u X : ℝ) : ℝ :=
  4 * exp m * cosh u ^ 2 / sqrt (1 + X ^ 2)

/-- Spatial derivative at fixed Kruskal time. -/
def schwarzschildClockSpaceDerivative (m u X : ℝ) : ℝ :=
  -schwarzschildClockTimeDerivative m u X * schwarzschildCauchySlope u X

/-- Partial differentiation in Kruskal time gives the stated positive derivative. -/
theorem schwarzschildCauchyClock_time_hasDerivAt (m u X : ℝ) :
    HasDerivAt (fun T => schwarzschildCauchyClock m T X)
      (schwarzschildClockTimeDerivative m u X) (schwarzschildCauchySlice u X) := by
  have hs : sqrt (1 + X ^ 2) ≠ 0 := by positivity
  have hratio : schwarzschildCauchySlice u X / sqrt (1 + X ^ 2) = tanh u := by
    simp only [schwarzschildCauchySlice, mul_div_cancel_left₀ _ hs]
  have hi := (hasDerivAt_id (schwarzschildCauchySlice u X)).div_const (sqrt (1 + X ^ 2))
  have ha := artanh_hasDerivAt_tanh u
  rw [← hratio] at ha
  have h := (ha.comp _ hi).const_mul (4 * exp m)
  have he : 4 * exp m * (cosh u ^ 2 * (1 / sqrt (1 + X ^ 2))) =
      schwarzschildClockTimeDerivative m u X := by
    unfold schwarzschildClockTimeDerivative
    ring
  rw [he] at h
  exact h

/-- Partial differentiation in space makes the clock gradient normal to its slices. -/
theorem schwarzschildCauchyClock_space_hasDerivAt (m u X : ℝ) :
    HasDerivAt (fun Y => schwarzschildCauchyClock m (schwarzschildCauchySlice u X) Y)
      (schwarzschildClockSpaceDerivative m u X) X := by
  have hs : sqrt (1 + X ^ 2) ≠ 0 := by positivity
  have hp : 1 + X ^ 2 ≠ 0 := by positivity
  have hbase : HasDerivAt (fun Y : ℝ => 1 + Y ^ 2) (2 * X) X := by
    simpa using ((hasDerivAt_id X).pow 2).const_add 1
  have hi := (hbase.sqrt hp).const_div (schwarzschildCauchySlice u X) hs
  have hratio : schwarzschildCauchySlice u X / sqrt (1 + X ^ 2) = tanh u := by
    simp only [schwarzschildCauchySlice, mul_div_cancel_left₀ _ hs]
  have ha := artanh_hasDerivAt_tanh u
  rw [← hratio] at ha
  have h := (ha.comp X hi).const_mul (4 * exp m)
  have he : 4 * exp m * (cosh u ^ 2 *
      (-schwarzschildCauchySlice u X * (2 * X / (2 * sqrt (1 + X ^ 2))) /
        sqrt (1 + X ^ 2) ^ 2)) = schwarzschildClockSpaceDerivative m u X := by
    unfold schwarzschildClockSpaceDerivative schwarzschildClockTimeDerivative
      schwarzschildCauchySlope schwarzschildCauchySlice
    field_simp
    ring
  rw [he] at h
  exact h

/-- The clock increases strictly in the Kruskal time direction. -/
theorem schwarzschildClockTimeDerivative_pos (m u X : ℝ) :
    0 < schwarzschildClockTimeDerivative m u X := by
  unfold schwarzschildClockTimeDerivative
  positivity

/-- Exact Lorentz norm of the clock covector in slice coordinates. -/
theorem schwarzschildClockDifferential_norm (m u X : ℝ) :
    schwarzschildClockTimeDerivative m u X ^ 2 -
      schwarzschildClockSpaceDerivative m u X ^ 2 =
      schwarzschildClockTimeDerivative m u X ^ 2 *
        (1 - schwarzschildCauchySlope u X ^ 2) := by
  unfold schwarzschildClockSpaceDerivative
  ring

/-- Every positive conformal radial Kruskal metric sees a timelike clock differential. -/
theorem schwarzschildClockDifferential_timelike (m u X c : ℝ) :
    exp c * (-(schwarzschildClockTimeDerivative m u X ^ 2) +
      schwarzschildClockSpaceDerivative m u X ^ 2) < 0 := by
  have h := schwarzschildClockDifferential_norm m u X
  have hp : 0 < schwarzschildClockTimeDerivative m u X ^ 2 *
      (1 - schwarzschildCauchySlope u X ^ 2) :=
    mul_pos (sq_pos_of_pos (schwarzschildClockTimeDerivative_pos m u X))
      (sub_pos.mpr (schwarzschildCauchySlope_sq_lt_one u X))
  exact mul_neg_of_pos_of_neg (exp_pos c) (by linarith only [h, hp])

end GaloisForLFunctions.HTGeometry
